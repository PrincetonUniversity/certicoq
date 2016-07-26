(** Implements an uncurrying pass for the L6 CPS language, based on the same
    approach used in SML/NJ.  The following issues need to be addressed:

    * This doesn't do all of the uncurrying at once -- you have to iterate until
      there's no change.  But...

    * We need to tag the eta-expansions so that they don't get uncurried again, and

    * We need to tag the uncurried function so that it doesn't get inlined into
      the eta expansion (thereby undoing the uncurrying.)
*)
Require Import CpdtTactics.
Require Import cps.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadState.
Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Data.List.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Positive.
Require Import Coq.Bool.Bool.
Require Import closure_conversion.  (* for max_var *)

Section UNCURRY.
  Import MonadNotation.

  Definition eq_var := Pos.eqb.

  (** We need to determine whether variables occur free in some terms.  We
      over-approximate by determining whether the variable occurs at all. *)
  
  (* Returns true iff [k] is in [xs]. *)
  Fixpoint occurs_in_vars (k:var) (xs:list var) : bool :=
    match xs with
    | nil => false
    | x::xs1 => eq_var k x || occurs_in_vars k xs1
    end.

  (* Returns true iff [k] occurs (at all) within the expression [e] *)
  Fixpoint occurs_in_exp (k:var) (e:exp) : bool :=
    match e with
    | Econstr z _ xs e1 =>
      eq_var z k || occurs_in_vars k xs || occurs_in_exp k e1
    | Ecase x arms =>
      eq_var k x ||
              (fix occurs_in_arms (arms: list (cTag * exp)) : bool :=
                 match arms with
                 | nil => false
                 | p::arms1 => match p with
                               | (_,e) => occurs_in_exp k e || occurs_in_arms arms1
                               end
                 end) arms
    | Eproj z _ _ x e1 =>
      eq_var z k || eq_var k x || occurs_in_exp k e1
    | Efun fds e =>
      occurs_in_fundefs k fds || occurs_in_exp k e
    | Eapp x _ xs => eq_var k x || occurs_in_vars k xs
    | Eprim z _ xs e1 =>
      eq_var z k || occurs_in_vars k xs || occurs_in_exp k e1
    end
  (* Returns true iff [k] occurs within the function definitions [fds] *)
  with occurs_in_fundefs (k:var) (fds:fundefs) : bool :=
         match fds with
         | Fnil => false
         | Fcons z _ zs e fds1 =>
           eq_var z k || occurs_in_vars k zs || occurs_in_exp k e ||
                   occurs_in_fundefs k fds1
         end.

  (* The state for this includes a "next" var for gensyming a fresh variable
     and a boolean for tracking whether or not a reduction happens. *)
  Definition uncurryM := state (var * bool).
  
  (* Generate a fresh variable, relying upon the fact that variables are
     represented as positives.  Later on, if we have additional information
     associated with the variable (e.g., a string), we can preserve that here.
  *)
  Definition copyVar (x:var) : uncurryM var :=
    s <- get ;;
      match (s:(var*bool)%type) with
      | (y,b) => 
        _ <- put ((y + 1)%positive,b) ;;
        ret y
      end.
  
  Fixpoint copyVars (xs:list var) : uncurryM (list var) :=
    match xs with
    | nil => ret nil
    | x::xs' => y <- copyVar x ;; ys <- copyVars xs' ;; ret (y::ys)
    end.

  Definition click : uncurryM unit :=
    s <- get ;;
      match (s : (var*bool)%type) with
      | (y,b) => put (y,true)
      end.
                   
  (* I'm following the same algorithm as in Andrew's book, or more 
     appropriately, in the SML/NJ code base.  In essence, we look for
     code that looks like this:

     let rec f (k,v1,...,vn) = 
           let rec g (u1,...,um) = e in k(g)
      in ...

     and replace it with:

     let rec f (k',v1',...,vn') = 
           let rec g' (u1',...,um') = f'(u1',...,um',v1',...,vn') in k'(g')
         and f' (k,u1,...,um,v1,...,vn) = e
     in ...

     where all of the primed variables are fresh. 

     One difference with SML/NJ is that this won't get all of the uncurrying
     done in a single pass.  In particular, if f gets uncurried, but the 
     resulting function can be further uncurried, we won't pick this up.  So
     really, we should iterate this until there's no change.  But, doing so
     will try to uncurry f yet again.  So we need to either fix this so that
     we tag f as something that should no longer be uncurried, or else 
     do all of the uncurrying in one pass.  The latter would be preferable
     but makes a structural termination argument harder.  
  *)
  Fixpoint uncurry_exp (e:exp) : uncurryM exp :=
    match e with
    | Econstr x ct vs e1 =>
      e1' <- uncurry_exp e1 ;; 
      ret (Econstr x ct vs e1')
    | Ecase x arms =>
      (* annoyingly, I can't seem to use a separate mapM definition here, but
         if I inline the definition, and specialize it, it seems to work. *)
      arms' <- (fix uncurry_list (arms: list (cTag*exp)) :
                  uncurryM (list (cTag*exp)) :=
                  match arms with
                  | nil => ret nil
                  | h::t =>
                    match h with
                    | (s,e) => 
                      e' <- uncurry_exp e ;; t' <- uncurry_list t ;;
                         ret ((s,e')::t')
                    end
                  end) arms ;;
      ret (Ecase x arms')
    | Eproj x ct n y e1 =>
      e1' <- uncurry_exp e1 ;;
      ret (Eproj x ct n y e1')
    | Eapp x ft xs => ret (Eapp x ft xs)
    | Eprim x p xs e1 =>
      e1' <- uncurry_exp e1 ;;
      ret (Eprim x p xs e1')
    | Efun fds e1 =>
      fds' <- uncurry_fundefs fds ;;
      e1' <- uncurry_exp e1 ;;
      ret (Efun fds' e1')
    end
  with uncurry_fundefs (fds : fundefs) : uncurryM fundefs :=
         match fds with
         | Fnil => ret Fnil
         | Fcons f ft fvs fe fds1 =>
           fds1' <- uncurry_fundefs fds1 ;;
           match fvs, fe with
           | fk::fvs, Efun (Fcons g gt gvs ge Fnil)
                           (Eapp fk' ft (g'::nil)) =>
             ge' <- uncurry_exp ge ;;
             if eq_var fk fk' && eq_var g g' &&
                        negb (occurs_in_exp fk ge) &&
                        negb (occurs_in_exp g ge) then
               gvs' <- copyVars gvs ;;
               fvs' <- copyVars fvs ;;
               fk'' <- copyVar fk ;;
               g'' <- copyVar g ;;
               f' <- copyVar f ;;
               _ <- click ;; 
               ret (Fcons f ft (fk''::fvs')
                          (* Note:  not sure what fTag to put on this application *)
                          (Efun (Fcons g' gt gvs' (Eapp f' ft (gvs' ++ fvs')) Fnil)
                                (Eapp fk'' ft (g''::nil)))
                          (* Note:  not sure what fTag to put on this function, but
                             it needs to match the Eapp noted above. *)
                          (Fcons f' ft (gvs ++ fvs) ge' fds1'))
             else
               ret (Fcons f ft (fk::fvs) (Efun (Fcons g gt gvs ge' Fnil)
                                               (Eapp fk' ft (g'::nil))) fds1')
           | _, _ => 
             fe' <- uncurry_exp fe ;;
                 ret (Fcons f ft fvs fe' fds1')
           end
         end.

  (* Tries to uncurry functions within [e].  If no function matches the
     pattern, returns [None], otherwise returns the transformed expression. *)
  Definition uncurry (e:exp) : option exp :=
    let n := ((max_var e 1) + 1)%positive in
    match runState (uncurry_exp e) (n,false) with
    | (e, (_,true)) => Some e
    | _ => None
    end.

  Fixpoint uncurry_fuel (n:nat) (e:exp) : exp :=
    match n with
    | 0 => e
    | S m => match uncurry e with
             | None => e
             | Some e' => uncurry_fuel m e'
             end
    end.

End UNCURRY.