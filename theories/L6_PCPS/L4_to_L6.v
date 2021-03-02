(* Conversion from L4.expression to L6.cps *)

Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Strings.String
        Coq.Sorting.Sorted Coq.Arith.Arith.
Require Import ExtLib.Data.String.
Require Import Common.AstCommon Common.compM.

(* ask about this import *)
Require compcert.lib.Maps.

Import ListNotations.

Require Import L4.expression L4.exp_eval.
(* Require Import Coq.Relations.Relation_Definitions. *)
(* Require Import Coq.Classes.Morphisms. *)
(* Require Import Coq.Classes.RelationClasses. *)
Require Import L6.cps L6.cps_show  L6.eval L6.ctx L6.List_util. 
Require Import compcert.lib.Coqlib.

Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Structures.Monads.

Import Monad.MonadNotation.
Open Scope monad_scope.

Section CPS.

  Context (prim_map : M.t (kername * string (* C definition *) * bool (* tinfo *) * nat (* arity *))). 
  Context (func_tag kon_tag default_tag default_itag : positive)
          (next_id : positive).

  (* Zoe: For translating proof. TODO *)
  Definition consume_fun (f x : var) : exp_ctx :=
    Efun1_c (Fcons f func_tag [x] (Ehalt f) Fnil) Hole_c. 

  Definition conId_map:= list (dcon * ctor_tag).
  
  Theorem conId_dec: forall x y:dcon, {x = y} + {x <> y}.
  Proof.
    intros. destruct x,y.
    assert (H:= AstCommon.inductive_dec i i0).
    destruct H.
    - destruct (classes.eq_dec n n0).
      + subst. left. auto.
      + right. intro. apply n1. inversion H. auto.
    - right; intro; apply n1. inversion H; auto.
  Defined.

  Fixpoint dcon_to_info (a:dcon) (sig:conId_map) :=
    match sig with
    | nil => default_tag
    | ((cId, inf)::sig') => match conId_dec a cId with
                            | left _ => inf
                            | right _ => dcon_to_info a sig'
                            end
    end.

  Definition dcon_to_tag (a:dcon) (sig:conId_map) :=
    dcon_to_info a sig.


  Definition name_env := M.t BasicAst.name.
  Definition n_empty : name_env := M.empty _.
  
  Definition t_info:Type := fun_tag.
  Definition t_map := M.t t_info.
  Definition t_empty:t_map := M.empty _.
  
  (* get the fun_tag of a variable, func_tag if not found *)
  Fixpoint get_f (n:var) (sig:t_map): fun_tag :=
    match M.get n sig with
    | None => func_tag
    | Some v => v
    end.


  Definition s_map := M.t var.
  Definition s_empty := M.empty var.


  Definition constr_env:Type := conId_map.

  Definition ienv := list (BasicAst.kername * AstCommon.itypPack).

  
  Inductive symgen := SG : (var * name_env) -> symgen. (* TODO use compilation monad instead *)

  Definition gensym : symgen -> name -> (var * symgen) :=
    fun s n => match s with
               | SG (i, nenv) =>
                 let env' := M.set i n nenv in
                 (i, SG (Pos.succ i, env'))
               end.

  Fixpoint gensym_n' (i : var) (env : name_env) (nlst : list name) :=
    match nlst with
    | nil => (nil, env, i)
    | cons n nlst' =>
      let env' := M.set i n env in
      let '(vlst, env'', next) := gensym_n' (Pos.succ i) env' nlst' in
      (i::vlst, env'', next)
    end.

  Definition gensym_n : symgen -> list name -> (list var * symgen) :=
    fun s nlst => match s with
                  | SG (i, nenv) =>
                    let '(ilst, nenv', next) := gensym_n' i nenv nlst in
                    (ilst, SG (next, nenv'))
                  end.

  Fixpoint gensym_n_nAnon' (i : var) (env : name_env )
           (n : nat) : (list var * name_env * var) :=
    match n with
    | O => (nil, env, i)
    | S n' =>
      let env' := M.set i nAnon env in
      let '(vlst, env'', next_var) := gensym_n_nAnon' (Pos.succ i) env' n' in
      (i::vlst, env'', next_var)
    end.

  Definition gensym_n_nAnon (s : symgen) (n : nat) : (list var * symgen) :=
    match s with
      SG (i, nenv) =>
      let '(ilist, nenv', next_var) := gensym_n_nAnon' i nenv n in
      (ilist, SG (next_var, nenv'))
    end.

  Fixpoint gen_nlst (n : nat) : list name :=
    match n with
    | O => nil
    | S n' => (nNamed "f"%string) :: (gen_nlst n')
    end.

  (* helper function for building name_env *)
  (*
Definition set_n (x:var) (n:BasicAst.name) (tgm:conv_env) : conv_env :=
  let '(t1,t2,t3) := tgm in
  (t1, t2, M.set x n t3).

Fixpoint add_names lnames vars tgm : conv_env :=
  match lnames, vars with
  | nil, nil => tgm
  | l::lnames', v::vars' =>
    let tgm := set_n v l tgm in
    add_names lnames' vars' tgm
  | _, _ => tgm
  end.
   *)

  (* returns list of numbers [n, n+m[  and the positive n+m (next available pos) *)
  Fixpoint fromN (n:positive) (m:nat) : list positive * positive :=
    match m with
    | O => (nil, n)
    | S m' =>
      let (l, nm ) := (fromN (n+1) (m')) in
      (n::l, nm)
    end.


  (* Bind m projections (starting from the (p+1)th) of var r to
   variables [n, n+m[, returns the generated context and n+m *)
  Fixpoint ctx_bind_proj (tg:ctor_tag) (r:positive) (m:nat) (n:var) (p:nat)
    : (exp_ctx * var) :=
    match m with
    | O => (Hole_c, n)
    | S m' =>
      let (ctx_p', n') := ctx_bind_proj tg r m' n p in
      (Eproj_c  n' tg (N.of_nat (m'+p)) r ctx_p', Pos.succ n')
    end.

  (* returns length of given expression.efnlst *)
  Fixpoint efnlst_names (vs:efnlst) : nat * list name :=
    match vs with
    | eflnil => (O, nil)
    | eflcons n e fds' =>
      let (i, l) := efnlst_names fds' in
      ((S i), n::l)
    end.

  (* definition of nth for the purposes of the cps_cvt function *)
  Definition nth := nth_default (1%positive).


  (** process a list of constructors from inductive type ind with ind_tag niT.
    - update the ctor_env with a mapping from the current ctor_tag to the cTypInfo
    - update the conId_map with a pair relating the nCon'th constructor of
      ind to the ctor_tag of the current constructor
   *)
  Fixpoint convert_cnstrs (tyname:string) (cct:list ctor_tag) (itC:list AstCommon.Cnstr)
           (ind:BasicAst.inductive) (nCon:N) (unboxed : N) (boxed : N)
           (niT:ind_tag) (ce:ctor_env) (dcm:conId_map) :=
    match (cct, itC) with
    | (cn::cct', cst::icT') =>
      let (cname, ccn) := cst in
      let is_unboxed := Nat.eqb ccn 0 in
      let info := {| ctor_name := BasicAst.nNamed cname
                     ; ctor_ind_name := BasicAst.nNamed tyname
                     ; ctor_ind_tag := niT
                     ; ctor_arity := N.of_nat ccn
                     ; ctor_ordinal := if is_unboxed then unboxed else boxed
                  |} in
      convert_cnstrs tyname cct' icT' ind (nCon+1)%N
                     (if is_unboxed then unboxed + 1 else unboxed)
                     (if is_unboxed then boxed else boxed + 1)
                     niT
                     (M.set cn info ce)
                     (((ind,nCon), cn)::dcm (** Remove this now that params are always 0? *))
    | (_, _) => (ce, dcm)
    end.


  (** For each inductive type defined in the mutually recursive bundle,
    - use tag niT for this inductive datatype
    - reserve constructor tags for each constructors of the type
    - process each of the constructor, indicating they are the ith constructor
      of the nth type of idBundle
    np: number of type parameters for this bundle
   *)
  Fixpoint convert_typack typ (idBundle:BasicAst.kername) (n:nat)
           (ice : (ind_env * ctor_env*  ctor_tag * ind_tag * conId_map))
    : (ind_env * ctor_env * ctor_tag * ind_tag * conId_map) :=
    let '(ie, ce, ncT, niT, dcm) := ice in
    match typ with
    | nil => ice
    (* let cct := (ncT::nil) in
      let ncT' := Pos.succ ncT in
      let itN := "Unit"%string in
      let itC := ((mkCnstr "prf"%string 0%nat) :: nil) in
      let (ce', dcm') :=
          convert_cnstrs itN cct itC (BasicAst.mkInd idBundle n) 0 niT ce dcm
      in
      let ityi := ((ncT, N.of_nat 0%nat)::nil) in
      (M.set niT ityi ie, ce', ncT', (Pos.succ niT), dcm') *)
    | (AstCommon.mkItyp itN itC ) ::typ' =>
      let (cct, ncT') := fromN ncT (List.length itC) in
      let (ce', dcm') :=
          convert_cnstrs itN cct itC (BasicAst.mkInd idBundle n) 0 0 0 niT ce dcm
      in
      let ityi :=
          combine cct (map (fun (c:AstCommon.Cnstr) =>
                              let (_, n) := c in N.of_nat n) itC)
      in
      convert_typack typ' idBundle (n+1)
                     (M.set niT ityi ie, ce', ncT', (Pos.succ niT) , dcm')
    end.


  Fixpoint convert_env' (g:ienv) (ice:ind_env * ctor_env * ctor_tag * ind_tag * conId_map)
    : (ind_env * ctor_env * ctor_tag * ind_tag * conId_map) :=
    let '(ie, ce, ncT, niT, dcm) := ice in
    match g with
    | nil => ice
    | (id, ty)::g' =>
      (* id is name of mutual pack ty is mutual pack *)
      (* constructors are indexed with : name (string) of the mutual pack
       with which projection of the ty, and indice of the constructor *)
      convert_env' g' (convert_typack ty id 0 (ie, ce, ncT, niT, dcm))
    end.


  (** As we process the L4 inductive environment (ienv), we build:
    - an L6 inductive environment (ind_env) mapping tags (ind_tag) to constructors

      and their arities
      - an L6 constructor environment (ctor_env) mapping tags (ctor_tag) to
      information about the constructors
      - a map (conId_map) from L4 tags (conId) to L6 constructor tags (ctor_tag)
      convert_env' is called with the next available constructor tag and the
      next available inductive datatype tag, and inductive and constructor
      environment containing only the default "box" constructor/type
   *)
  Definition convert_env (g:ienv): (ind_env * ctor_env*  ctor_tag * ind_tag * conId_map) :=
    let default_ind_env := M.set default_itag (cons (default_tag, 0%N) nil) (M.empty ind_ty_info) in
    let info := {| ctor_name := BasicAst.nAnon
                   ; ctor_ind_name := BasicAst.nAnon
                   ; ctor_ind_tag := default_itag
                   ; ctor_arity := 0%N
                   ; ctor_ordinal := 0%N
                |} in
    let default_ctor_env := M.set default_tag info (M.empty ctor_ty_info) in
    convert_env' g (default_ind_env, default_ctor_env, (Pos.succ default_tag:ctor_tag), (Pos.succ default_itag:ind_tag), nil).


  (* vx is list of variables to which exps are bound in cvt_triples *)
  Fixpoint cps_exps (ts : list (cps.exp * var * var)) (vx : list var) (k : var)
    : option (cps.exp) :=
    match ts with
    | nil => ret (cps.Eapp k kon_tag vx)
    | t::ts' =>
      let '(e1, k1, x1) := t in
      r <- cps_exps ts' vx k;;
      let e_exp := r in
      ret (cps.Efun
             (Fcons k1 kon_tag (x1::nil) e_exp Fnil)
             e1)
    end.

  Fixpoint convert_prim (n : nat) (* arity *)
           (prim : positive) (args : list var) (kont : var)
           (next : symgen) : (cps.exp * symgen) :=
    match n with
    | 0%nat =>
      let (pr, next) := gensym next (nNamed "prim"%string) in      
      (Eprim pr prim (List.rev args) (Eapp kont kon_tag [pr]), next)
    | S n =>
      let (arg, next) := gensym next (nNamed "p_arg"%string) in
      let (kont1, next) := gensym next (nNamed "p_k"%string) in            
      let (f, next) := gensym next (nNamed "prim_wrapper"%string) in            
      let '(trm, next) := convert_prim n prim (arg :: args) kont1 next in
      (Efun (Fcons f func_tag [kont1; arg] trm Fnil) (Eapp kont kon_tag [f]), next)
    end.                  
  

  (* returns cps exp, var and next fresh var *)
  Fixpoint cps_cvt (e : expression.exp) (vn : list var) (k : var) (next : symgen)
           (tgm : constr_env) : option (cps.exp * symgen) :=
    match e with
    | Var_e x =>
      match nth_error vn (N.to_nat x) with
      | Some v => ret (cps.Eapp k kon_tag (v::nil), next)
      | None => None
      end
    | App_e e1 e2 =>
      let (k1, next) := gensym next (nNamed "k1"%string) in
      let (x1, next) := gensym next (nNamed "x1"%string) in
      r1 <- cps_cvt e1 vn k1 (next) tgm;;
      let '(e1', next) := r1 : (cps.exp * symgen) in
      let (k2, next) := gensym next (nNamed "k2"%string) in
      let (x2, next) := gensym next (nNamed "x2"%string) in
      r2 <- cps_cvt e2 vn k2 (next) tgm;;
      let '(e2', next) := r2 : (cps.exp * symgen) in
      ret (cps.Efun
             (Fcons k1 kon_tag (x1::nil)
                    (cps.Efun
                       (Fcons k2 kon_tag (x2::nil)
                              (cps.Eapp x1 func_tag (k::x2::nil)) Fnil)
                       e2') Fnil)
             e1', next)

    | Lam_e n e1 =>
      let (k1, next) := gensym next (nNamed "k_lam"%string) in
      let (x1, next) := gensym next (nNamed "x_lam"%string) in
      let (f, next) := gensym next n in
      (* let tgm := set_n f n tgm in *)
      r <- cps_cvt e1 (x1::vn) k1 (next) tgm;;
      let '(e1', next) := r : (cps.exp * symgen) in
      ret ((cps.Efun
              (Fcons f func_tag (k1::x1::nil) e1' Fnil)
              (cps.Eapp k kon_tag (f::nil))), next)

    | Let_e n e1 e2 =>
      (* let e' = L4.App_e (L4.Lam_e n e1) e2 in
    cps_cvt e' vn k next *)
      let (x, next) := gensym next n in
      let (k1, next) := gensym next (nNamed "k"%string) in
      r2 <- cps_cvt e2 (x::vn) k (next) tgm;;
      let '(e2', next) := r2 : (cps.exp * symgen) in
      r1 <- cps_cvt e1 vn k1 next tgm;;
      let '(e1', next) := r1 : (cps.exp * symgen) in
      (* let tgm := set_n x n tgm in *)
      ret (cps.Efun
             (Fcons k1 kon_tag (x::nil) e2' Fnil)
             e1', next)

    | Con_e dci es =>
      let c_tag := dcon_to_tag dci tgm in
      let (k', next) := gensym next (nNamed "k'"%string) in
      let (x', next) := gensym next (nNamed "x'"%string) in
      (* r1 <- cvt_triples_exps es vn next tgm;; *)
      (* let '(cvt_ts, next) := r1 in *)
      (* let vx := List.map *)
      (*             (fun x => let '(_, _, v) := x : (cps.exp * var * var) in v) *)
      (*             cvt_ts *)
      (* in *)
      (* r2 <- cps_exps cvt_ts vx k';; *)
      (* let e' := r2 in *)
      let (vx, next) := gensym_n_nAnon next (N.to_nat (exps_length es)) in
      r <- cps_cvt_exps es vn k' nil next tgm;;
      let (e', next) := r : cps.exp * symgen in
      ret (cps.Efun
             (Fcons k' kon_tag vx
                    (Econstr x' c_tag vx
                             (Eapp k kon_tag (x'::nil))) Fnil)
             e', next)

    | Fix_e fnlst i =>
      let (fnlst_length, names_lst) := efnlst_names fnlst in
      let (nlst, next) := gensym_n next names_lst in
      r <- cps_cvt_efnlst fnlst (nlst ++ vn) nlst next tgm;;
      let '(fdefs, next) := r : (fundefs * symgen) in
      i' <- (nth_error nlst (N.to_nat i));;
      ret (cps.Efun fdefs
                    (cps.Eapp k kon_tag (i'::nil)),
           next)

    | Match_e e1 n bl =>
      let (k1, next) := gensym next (nNamed "k1"%string) in
      let (x1, next) := gensym next (nNamed "x1"%string) in
      r1 <- cps_cvt e1 vn k1 next tgm;;
      let '(e1', next) := r1 in
      r2 <- cps_cvt_branches bl vn k x1 next tgm;;
      let '(cbl, next) := r2 : (list (ctor_tag * exp) * symgen) in
      ret (cps.Efun
             (Fcons k1 kon_tag (x1::nil)
                    (Ecase x1 cbl) Fnil)
             e1', next)

    | Prf_e =>
      let (x, next) := gensym next (nNamed ""%string) in
      ret (cps.Econstr x default_tag nil (cps.Eapp k kon_tag (x::nil)), next)
   (* let (f, next) := gensym next (nNamed "f_proof"%string) in *)
   (* let (x, next) := gensym next (nNamed "x"%string) in *)
   (* let c := consume_fun f x in *)
          (* ret (c |[ cps.Eapp k kon_tag (f::nil) ]|, next) *)
    | Prim_e p =>
      match M.get p prim_map with
      | Some (nm, s, ar) =>
        Some (convert_prim ar p [] k next)
      | None => None (* failwith "Internal error: identifier for primitive not found" *)
      end
    end
  (* with cvt_triples_exps (es : expression.exps) (vn : list var) (next : symgen) *)
  (*                       (tgm : constr_env) *)
  (*      : option ((list (cps.exp * var * var)) * symgen) := *)
  (*        match es with *)
  (*        | enil => ret (nil, next) *)
  (*        | econs e es' => *)
  (*          let (k, next) := gensym next (nNamed ""%string) in *)
  (*          let (x, next) := gensym next (nNamed ""%string) in *)
  (*          r1 <- cps_cvt e vn k next tgm;; *)
  (*          let '(e', next) := r1 in *)
  (*          r2 <- cvt_triples_exps es' vn next tgm;; *)
  (*          let '(cvt_ts', next) := *)
  (*              r2 : (list (cps.exp * var * var)) * symgen in *)
  (*          ret ((e', k, x) :: cvt_ts', next) *)
  (*        end *)

  (* merge cvt_triples_exps and cps_exps *)
  with cps_cvt_exps (es : expression.exps) (vn : list var) (k : var) (vx : list var)
                    (next : symgen) (tgm : constr_env) 
       : option (cps.exp * symgen) :=
         match es with
         | enil => ret (cps.Eapp k kon_tag (List.rev vx), next)
         | econs e es' =>
           let (k1, next) := gensym next (nNamed ""%string) in
           let (x1, next) := gensym next (nNamed ""%string) in
           r1 <- cps_cvt e vn k1 next tgm;;
           let (e', next) := r1 : (cps.exp * symgen) in
           r2 <- cps_cvt_exps es' vn k (x1 :: vx) next tgm;;
           let (e_exp, next) := r2 : (cps.exp * symgen) in
           ret (cps.Efun
                  (Fcons k1 kon_tag (x1::nil) e_exp Fnil)
                  e', next)
         end      

  (* nlst must be of the same length as fdefs *)
  with cps_cvt_efnlst (fdefs : expression.efnlst) (vn : list var)
                      (nlst : list var) (next : symgen) (tgm : constr_env)
       : option (fundefs * symgen) :=
         match fdefs with
         | eflnil => ret (Fnil, next)
         | eflcons n1 e1 fdefs' =>
           let (x, next) := gensym next (nNamed "fix_x"%string) in
           let (k', next) := gensym next (nNamed "fix_k"%string) in
           let curr_var := List.hd 1%positive nlst in
           match e1 with
           | Lam_e n2 e2 =>
             r1 <- cps_cvt e2 (x::vn) k' (next) tgm;;
             let '(ce, next) := r1 : (cps.exp * symgen) in
             r2 <- cps_cvt_efnlst fdefs' vn (List.tl nlst) next tgm;;
             let '(cfdefs, next) := r2 : (fundefs * symgen) in
             ret (Fcons curr_var func_tag (k'::x::nil) ce cfdefs, next)
           | _ => None
           end
         end

  with cps_cvt_branches (bl : expression.branches_e) (vn : list var) (k : var)
                        (r : var) (next : symgen) (tgm : constr_env)
       : option (list (ctor_tag * exp) * symgen) :=
         match bl with
         | brnil_e => ret (nil, next)
         | brcons_e dc (i, lnames) e bl' =>
           let tg := dcon_to_tag dc tgm in
           let l := List.length lnames in
           rb <- cps_cvt_branches bl' vn k r next tgm;;
           let (cbl, next) := rb : (list (ctor_tag * exp) * symgen) in
           let (vars, next) := gensym_n next (List.rev lnames) in
           let (ctx_p, _) :=
               ctx_bind_proj tg r l (List.hd (1%positive) vars) 0
           in
           let vars_rev := List.rev vars in
           re <- cps_cvt e (vars_rev ++ vn) k next tgm;;
           let '(ce, next) := re : (exp * symgen) in
           ret ((tg, app_ctx_f ctx_p ce)::cbl, next)
         end.

  Fixpoint cps_cvt_exps' (es : expression.exps) (vn : list var) (k : var)
           (next : symgen) (tgm : constr_env) :=
    match es with
    | enil => ret (nil, next)
    | econs e es' =>
      r1 <- cps_cvt e vn k next tgm;;
      let '(e', next) := r1 in
      r2 <- cps_cvt_exps' es' vn k next tgm;;
      let (es'', next) := r2 in
      ret (cons e' es'', next)
    end.

  Fixpoint cps_cvt_efnlst' (efns : expression.efnlst) (vn : list var) (k : var)
           (next : symgen) (tgm : constr_env) :=
    match efns with
    | eflnil => ret (nil, next)
    | eflcons na e efns' =>
      r1 <- cps_cvt e vn k next tgm;;
      let (e', next) := r1 : (cps.exp * symgen) in
      r2 <- cps_cvt_efnlst' efns' vn k next tgm;;
      let (efns'', next) := r2 in
      ret (cons e' efns'', next)
    end.

  Fixpoint cps_cvt_branches' (bs : expression.branches_e) (vn : list var) (k : var)
           (next : symgen) (tgm : constr_env) :=
    match bs with
    | brnil_e => ret (nil, next)
    | brcons_e dc (n, l) e bs' =>
      r1 <- cps_cvt e vn k next tgm;;
      let (e', next) := r1 : (cps.exp * symgen) in
      r2 <- cps_cvt_branches' bs' vn k next tgm;;
      let (bs'', next) := r2 in
      ret (cons e' bs'', next)
    end. 
  

  Inductive fresh_var : var -> symgen -> Prop :=
  | is_gt :
      forall v1 v2 nenv,
        (v1 >= v2)%positive ->
        fresh_var v1 (SG (v2, nenv)).

  Definition lt_symgen (v1 : var) (next : symgen) : Prop :=
    match next with
    | SG (v2, nenv) => (v1 < v2)%positive
    end.

  Definition geq_symgen (v1 : var) (next : symgen) : Prop :=
    match next with
    | SG (v2, nenv) => (v1 >= v2)%positive
    end. 

  Definition lt_lst_symgen (vars : list var) (next : symgen) : Prop :=
    Forall (fun v => lt_symgen v next) vars. 

  (* scratch *)
  (* how to ensure fresh variables? *)
  Inductive cps_cvt_rel : expression.exp -> list var -> var -> cps.exp -> Prop :=
  | e_Var :
      forall v vn x k,
        v = (nth vn (N.to_nat x)) ->
        cps_cvt_rel (Var_e x) vn k (cps.Eapp k kon_tag (v::nil))
  | e_Lam :
      forall na e1 e1' x1 vn k k1 f,
        cps_cvt_rel e1 (x1::vn) k1 e1' ->
        cps_cvt_rel (Lam_e na e1) vn k (cps.Efun
                                          (Fcons f func_tag (k1::x1::nil) e1' Fnil)
                                          (cps.Eapp k kon_tag (f::nil)))
  | e_App :
      forall e1 e1' e2 e2' k k1 k2 x1 x2 vn,
        cps_cvt_rel e1 vn k1 e1' ->
        cps_cvt_rel e2 vn k2 e2' ->
        cps_cvt_rel (App_e e1 e2)
                    vn
                    k
                    (cps.Efun
                       (Fcons k1 kon_tag (x1::nil)
                              (cps.Efun
                                 (Fcons k2 kon_tag (x2::nil)
                                        (cps.Eapp x1 func_tag
                                                  (k::x2::nil)) Fnil)
                                 e2') Fnil)
                       e1')
  | e_Let :
      forall na e1 e1' e2 e2' x vn k k1,
        cps_cvt_rel e2 (x::vn) k e2' ->
        cps_cvt_rel e1 vn k1 e1' ->
        cps_cvt_rel (Let_e na e1 e2) vn k (cps.Efun
                                             (Fcons k1 kon_tag (x::nil) e2' Fnil)
                                             e1')
  | e_Fix :
      forall fnlst i i' nlst vn k fdefs,
        List.length nlst = efnlength fnlst ->
        cps_cvt_rel_efnlst fnlst (nlst ++ vn) nlst fdefs ->
        i' = (nth nlst (N.to_nat i)) ->
        cps_cvt_rel (Fix_e fnlst i) vn k (cps.Efun fdefs
                                                   (cps.Eapp k kon_tag (i'::nil)))
  with cps_cvt_rel_efnlst :
         expression.efnlst -> list var -> list var -> fundefs -> Prop :=
  | e_Eflnil :
      forall vn nlst,
        cps_cvt_rel_efnlst eflnil vn nlst Fnil
  | e_Eflcons :
      forall vn nlst e1 e1' fnlst' fdefs' cvar n1 na x k',
        cps_cvt_rel e1 (x::vn) k' e1' ->
        cps_cvt_rel_efnlst fnlst' vn (List.tl nlst) fdefs' ->
        List.hd_error nlst = Some cvar ->
        cps_cvt_rel_efnlst
          (eflcons n1 (Lam_e na e1) fnlst')
          vn
          nlst
          (Fcons cvar func_tag (k'::x::nil) e1' fdefs').                       


  Definition convert_top (ee:ienv * expression.exp) :
    option (ctor_env * name_env * fun_env * ctor_tag * ind_tag * cps.exp) :=
    let '(_, cG, ctag, itag,  dcm) := convert_env (fst ee) in
    let f := next_id in
    let k := (next_id + 1)%positive in
    let x := (next_id + 2)%positive in
    r <- cps_cvt (snd ee) nil k (SG ((next_id + 3)%positive, n_empty)) dcm;;
    let (e', sg) := r : (cps.exp * symgen) in
    match sg with
      SG (next, nM) =>
      let fenv : fun_env := M.set func_tag (2%N, (0%N::1%N::nil))
                                  (M.set kon_tag (1%N, (0%N::nil)) (M.empty _) ) in
      ret (cG, nM, fenv, ctag, itag,
           (cps.Efun
              (Fcons f kon_tag (k::nil) e'
                     (Fcons k kon_tag (x::nil) (Ehalt x) Fnil))
              (cps.Eapp f kon_tag (k::nil))))
    end.

  Fixpoint rho_names (rho : exp_eval.env) : list name :=
    match rho with
    | nil => nil
    | cons v rho' =>
      let na := nNamed "rho_elt"%string in
      (na :: (rho_names rho'))
    end.

  Fixpoint cps_cvt_val (v : exp_eval.value) (next : symgen)
           (tgm : constr_env) {struct v} : option (cps.val * symgen) :=
    let fix cps_cvt_env vs next tgm :=
        match vs with
        | nil => ret (nil, next)
        | cons v vs' =>
          r1 <- cps_cvt_val v next tgm;;
          let (v', next) := r1 : (cps.val * symgen) in
          r2 <- cps_cvt_env vs' next tgm;;
          let (vs'', next) := r2 : (list cps.val * symgen) in
          ret (cons v' vs'', next)
        end
    in
    match v with
    | Con_v dc vs =>
      let c_tag := dcon_to_tag dc tgm in
      r <- cps_cvt_env vs next tgm;;
      let (vs', next) := r : (list cps.val * symgen) in
      ret (Vconstr c_tag vs', next)
    | Clos_v rho na e =>
      r1 <- cps_cvt_env rho next tgm;;
      let (rho', next) := r1 : (list cps.val * symgen) in
      let lnames := rho_names rho in
      let (vars, next) := gensym_n next lnames in
      m <- set_lists vars rho' (M.empty cps.val);;
      let (k1, next) := gensym next (nNamed "k_lam"%string) in
      let (x1, next) := gensym next (nNamed "x_lam"%string) in
      let (f, next) := gensym next na in
      r2 <- cps_cvt e (x1::vars) k1 (next) tgm;;
      let (e', next) := r2 : (cps.exp * symgen) in
      ret (Vfun m (Fcons f func_tag (k1::x1::nil) e' Fnil) f, next)
    | ClosFix_v rho efns n =>
      r1 <- cps_cvt_env rho next tgm;;
      let (rho', next) := r1 : (list cps.val * symgen) in
      let lnames := rho_names rho in
      let (vars, next) := gensym_n next lnames in
      m <- set_lists vars rho' (M.empty cps.val);;
      let (fnlst_length, names_lst) := efnlst_names efns in
      let (nlst, next) := gensym_n next names_lst in
      r2 <- cps_cvt_efnlst efns (nlst ++ vars) nlst next tgm;;
      let (fdefs, next) := r2 : (fundefs * symgen) in
      i <- (nth_error nlst (N.to_nat n));;
      ret (Vfun m fdefs i, next)
    | _ => (* TODO *)
      ret (Vint 0, next)
    end.

  Fixpoint cps_cvt_env (vs : list exp_eval.value) (next : symgen)
           (tgm : constr_env) : option (list cps.val * symgen) :=
    match vs with
    | nil => ret (nil, next)
    | cons v vs' =>
      r1 <- cps_cvt_val v next tgm;;
      let (v', next) := r1 : (cps.val * symgen) in
      r2 <- cps_cvt_env vs' next tgm;;
      let (vs'', next) := r2 : (list cps.val * symgen) in
      ret (cons v' vs'', next)
    end.

  Definition cps_cvt_val' (v : exp_eval.value) (next : symgen) (tgm : constr_env) :=
    match v with
    | Con_v dc vs =>
      let c_tag := dcon_to_tag dc tgm in
      r <- cps_cvt_env vs next tgm;;
      let (vs', next) := r : (list cps.val * symgen) in
      ret (Vconstr c_tag vs', next)
    | Clos_v rho na e =>
      r1 <- cps_cvt_env rho next tgm;;
      let (rho', next) := r1 : (list cps.val * symgen) in
      let lnames := rho_names rho in
      let (vars, next) := gensym_n next lnames in
      m <- set_lists vars rho' (M.empty cps.val);;
      let (k1, next) := gensym next (nNamed "k_lam"%string) in
      let (x1, next) := gensym next (nNamed "x_lam"%string) in
      let (f, next) := gensym next na in
      r2 <- cps_cvt e (x1::vars) k1 (next) tgm;;
      let (e', next) := r2 : (cps.exp * symgen) in
      ret (Vfun m (Fcons f func_tag (k1::x1::nil) e' Fnil) f, next)
    | ClosFix_v rho efns n =>
      r1 <- cps_cvt_env rho next tgm;;
      let (rho', next) := r1 : (list cps.val * symgen) in
      let lnames := rho_names rho in
      let (vars, next) := gensym_n next lnames in
      m <- set_lists vars rho' (M.empty cps.val);;
      let (fnlst_length, names_lst) := efnlst_names efns in
      let (nlst, next) := gensym_n next names_lst in
      r2 <- cps_cvt_efnlst efns (nlst ++ vars) nlst next tgm;;
      let (fdefs, next) := r2 : (fundefs * symgen) in
      i <- (nth_error nlst (N.to_nat n));;
      ret (Vfun m fdefs i, next)
    | _ => (* TODO *)
      ret (Vint 0, next)
    end.

  Lemma cps_cvt_val_eq :
    forall v next cnstrs,
      cps_cvt_val v next cnstrs = cps_cvt_val' v next cnstrs.
  Proof.
    intros v next cnstrs.
    induction v using value_ind'.
    - simpl. unfold cps_cvt_env. reflexivity.
    - simpl. reflexivity.
    - simpl. unfold cps_cvt_env. reflexivity.
    - simpl. unfold cps_cvt_env. reflexivity.
  Qed. 

(*<<<<<<< HEAD
=======
Section Post.
  
  Context {fuel : Type} {Hfuel : @fuel_resource fuel} {trace : Type}
          {Htrace : @trace_resource trace}.

    Context (P1 : PostT) (* Local *)
            (PG : PostGT) (* Global *)
            (cnstrs : conId_map)
            (cenv : ctor_env)
            (Hprops : Post_properties cenv P1 P1 PG)
            (HpropsG : Post_properties cenv PG PG PG)
            (Hincl : inclusion _ (comp P1 P1) P1)
            (HinclG : inclusion _ P1 PG).

    Inductive StrictlyIncreasing' : list positive -> Prop :=
    | SInc_nil : StrictlyIncreasing' []
    | SInc_cons1 a : StrictlyIncreasing' [a]
    | SInc_consn a b l :
        StrictlyIncreasing' (b :: l) ->
        (a < b)%positive  ->
        StrictlyIncreasing' (a :: b :: l).

    Definition StrictlyIncreasing l :=
      Sorted (fun p1 p2 => (p1 < p2)%positive) l.

    Definition cps_env_rel'' (R : value -> cps.val -> Prop) rho vs :=
      forall v n,
        nth_error rho n = Some v ->
        exists v',
          nth_error vs n = Some v' ->
          forall v'' k,
            R v v'' ->
            preord_val cenv PG k v'' v'.

    Fixpoint cps_val_rel' (v : value) (v': cps.val) {struct v} : Prop :=
      let fix Forall2_aux vs1 vs2 :=
          match vs1, vs2 with
          | [], [] => True
          | v1 :: vs1, v2 :: vs2 =>
            cps_val_rel' v1 v2 /\ Forall2_aux vs1 vs2
          | _, _ => False
          end
      in
      let fix cps_env_rel' rho vs :=
          match rho, vs with
          | [], [] => True
          | v1 :: rho, v2 :: vs =>
            (forall v'' k,
                cps_val_rel' v1 v'' ->
                preord_val cenv PG k v'' v2) /\
            cps_env_rel' rho vs
          | _, _ => False
          end
      in
      match v, v' with
      | Con_v dc vs, Vconstr c_tag vs' =>
        dcon_to_tag dc cnstrs = c_tag /\ Forall2_aux vs vs'
      | Prf_v, Vint 0 => True
      | Clos_v rho na e, Vfun rho_m (Fcons f func_tag (k::x::nil) e' Fnil) f' =>
        exists vs names n nenv next,
        cps_env_rel' rho vs /\ 
        StrictlyIncreasing names /\
        set_lists names vs (M.empty cps.val) = Some rho_m /\
        (k > List.last names (1%positive))%positive /\ (x > k)%positive
        /\ (f = f') /\ (f > x)%positive /\ (n > f)%positive /\
        cps_cvt e names k (SG (n, nenv)) cnstrs = Some (e', next)
      | _, _ => False
      end.

    (* Inductive cps_val_rel : value -> val -> Prop := *)
    (* | rel_Con : *)
    (*     forall vs vs' dc c_tag cnstrs, *)
    (*       Forall2 (fun v v' => cps_val_rel v v') vs vs' ->   *)
    (*       dcon_to_tag dc cnstrs = c_tag -> *)
    (*       cps_val_rel (Con_v dc vs) (Vconstr c_tag vs') *)
    (* | rel_Prf : *)
    (*     cps_val_rel Prf_v (Vint 0) *)
    (* | rel_Clos : *)
    (*     forall rho vs rho_m names na k x f n nenv next e e' cnstrs, *)
    (*       cps_env_rel' cps_val_rel rho vs ->  *)
    (*       StrictlyIncreasing names -> *)
    (*       set_lists names vs (M.empty val) = Some rho_m -> *)
    (*       (k > List.last names (1%positive))%positive /\ (x > k)%positive *)
    (*       /\ (f > x)%positive /\ (n > f)%positive -> *)
    (*       cps_cvt e names k (SG (n, nenv)) cnstrs = Some (e', next) -> *)
    (*       cps_val_rel (Clos_v rho na e) *)
    (*                   (Vfun rho_m (Fcons f func_tag (x::k::nil) e' Fnil) f). *)

    Fixpoint cps_env_rel rho vs :=
      match rho, vs with
      | [], [] => True
      | v1 :: rho, v2 :: vs =>
        (forall v'' k,
            cps_val_rel' v1 v'' ->
            preord_val cenv PG k v'' v2) /\
        cps_env_rel rho vs
      | _, _ => False
      end. 

    Definition cps_val_rel (v : value) (v': cps.val) : Prop :=
      match v, v' with
      | Con_v dc vs, Vconstr c_tag vs' =>
        dcon_to_tag dc cnstrs = c_tag /\ Forall2 cps_val_rel' vs vs'
      | Prf_v, Vint 0 => True
      | Clos_v rho na e, Vfun rho_m (Fcons f func_tag (k::x::nil) e' Fnil) f' =>
        exists vs names n nenv next,
        cps_env_rel rho vs /\ 
        StrictlyIncreasing names /\
        set_lists names vs (M.empty cps.val) = Some rho_m /\
        (k > List.last names (1%positive))%positive /\ (x > k)%positive
        /\ (f = f') /\ (f > x)%positive /\ (n > f)%positive /\
        cps_cvt e names k (SG (n, nenv)) cnstrs = Some (e', next)
      | _, _ => False
      end.

    Fixpoint obs_rel' (v : value) (v': cps.val) : Prop :=
      let fix Forall2_aux vs1 vs2 :=
          match vs1, vs2 with
          | [], [] => True
          | v1 :: vs1, v2 :: vs2 =>
            obs_rel' v1 v2 /\ Forall2_aux vs1 vs2
          | _, _ => False
          end
      in
      match v, v' with
      | Con_v dc vs, Vconstr c_tag vs' =>
        dcon_to_tag dc cnstrs = c_tag /\ Forall2_aux vs vs'
      | Prf_v, Vint 0 => True
      | Clos_v rho na e, Vfun rho_m (Fcons f func_tag (k::x::nil) e' Fnil) f' =>
        True
      | _, _ => False
      end.

    Fixpoint env_obs_rel rho rho' :=
      match rho, rho' with
      | [], [] => True
      | v1 :: rho, v2 :: vs =>
        (forall v'' k,
            obs_rel' v1 v'' ->
            preord_val cenv PG k v'' v2) /\
        env_obs_rel rho vs
      | _, _ => False
      end.


    Lemma Forall2_aux_is_Forall2 :
      forall vs l, 
        (fix Forall2_aux (vs1 : list value) (vs2 : list cps.val) {struct vs1} :
           Prop :=
           match vs1 with
           | [] => match vs2 with
                   | [] => True
                   | _ :: _ => False
                   end
           | v1 :: vs3 =>
             match vs2 with
             | [] => False
             | v2 :: vs4 => cps_val_rel' v1 v2 /\ Forall2_aux vs3 vs4
             end
           end) vs l ->
        Forall2 cps_val_rel' vs l.
    Proof.
      induction vs; intros l Haux.
      - destruct l. constructor. destruct Haux.
      - destruct l. destruct Haux.
        destruct Haux. econstructor.
        eassumption. eapply IHvs. eassumption.
    Qed.

    Lemma gensym_n_nAnon'_strictlyInc :
      forall n v nenv vars nenv' v',
        gensym_n_nAnon' v nenv n = (vars, nenv', v') ->
        StrictlyIncreasing vars.
    Proof.
      induction n; intros v nenv vars nenv' v' Hgen; unfold StrictlyIncreasing in *.
      - simpl in Hgen. inv Hgen. econstructor.
      - simpl in Hgen.
        destruct (gensym_n_nAnon' (Pos.succ v) (M.set v nAnon nenv) n) eqn: Hgen2.
        destruct p eqn: Hp.
        inv Hgen. econstructor.
        + eapply IHn. eapply Hgen2.
        + destruct l eqn: Hl.
          econstructor.
          econstructor.
          assert (Heq: v0 = Pos.succ v).
          { unfold gensym_n_nAnon' in Hgen2.
            destruct n eqn: Hn.
            inv Hgen2.
            destruct (
                (fix gensym_n_nAnon' (i : var) (env : name_env) (n : nat)
                     {struct n} :
                   list var * name_env * var :=
                   match n with
                   | 0%nat => ([], env, i)
                   | S n' =>
                     let
                       '(vlst, env'', next_var) :=
                       gensym_n_nAnon' (Pos.succ i) (M.set i nAnon env) n' in
                     (i :: vlst, env'', next_var)
                   end) (Pos.succ (Pos.succ v))
                        (M.set (Pos.succ v) nAnon (M.set v nAnon nenv)) n0
              ) eqn:Hgen.
            destruct p eqn: Hp.
            inv Hgen2. reflexivity. }
          rewrite Heq. zify. lia. 
    Qed.

    Lemma gensym_n_nAnon'_cons :
      forall n vars p p' nenv nenv' v,
        gensym_n_nAnon' p nenv n = (p' :: vars, nenv', v) ->
        exists nenv1, gensym_n_nAnon' (Pos.succ p) nenv (n - 1) = (vars, nenv1, v).
    Proof.
      induction n; intros vars p p' nenv nenv' v Hgen.
      - unfold gensym_n_nAnon' in Hgen. inv Hgen.
      - simpl. rewrite Nat.sub_0_r. unfold gensym_n_nAnon'. 
        destruct n eqn: Hn.
        + unfold gensym_n_nAnon' in Hgen. inversion Hgen.
          eexists. reflexivity. 
        + unfold gensym_n_nAnon' in Hgen.
          destruct (
              (fix gensym_n_nAnon' (i : var) (env : name_env) (n1 : nat) {struct n1} :
                 list var * name_env * var :=
                 match n1 with
                 | 0%nat => ([], env, i)
                 | S n' =>
                   let
                     '(vlst, env'', next_var) :=
                     gensym_n_nAnon' (Pos.succ i) (M.set i nAnon env) n' in
                   (i :: vlst, env'', next_var)
                 end) (Pos.succ (Pos.succ p)) (M.set (Pos.succ p) nAnon nenv) n0
            ) eqn: Hgen2.
          destruct p0 eqn: Hp0.      
    Abort.

    Lemma gensym_n_nAnon_cons :
      forall n v nenv vars a next,
        gensym_n_nAnon (SG (v, nenv)) n = (a :: vars, next) ->
        exists next1, gensym_n_nAnon (SG (Pos.succ v, nenv)) (n - 1) = (vars, next1).
    Proof.
      induction n; unfold gensym_n_nAnon; intros v nenv vars a next Hgen.
      - destruct (gensym_n_nAnon' v nenv 0) eqn: Hgen2.
        destruct p eqn: Hp.
    Abort. 
      
    Lemma gensym_n_nAnon_strictlyInc :
      forall vars next next1 n,
        gensym_n_nAnon next n = (vars, next1) ->
        StrictlyIncreasing vars.
    Proof.
      intros vars. 
      induction vars; intros next next1 n Hgen.
      - unfold StrictlyIncreasing. econstructor.
      - unfold StrictlyIncreasing in *. econstructor.
        + unfold gensym_n_nAnon in Hgen.
          destruct next eqn: Hnext.
          destruct p eqn: Hp.
          destruct (gensym_n_nAnon' v n0 n) eqn: Hgen2.
          destruct p0 eqn: Hp0.
          inv Hgen.
          eapply IHvars. 
          admit.
        + unfold gensym_n_nAnon in Hgen. destruct vars eqn: Hvars.
          econstructor.
          econstructor.
          destruct next eqn: Hnext.
          destruct p eqn: Hp.
          destruct (gensym_n_nAnon' v0 n0 n) eqn: Hgen2.
          destruct p0 eqn: Hp0.
          inv Hgen.
          eapply gensym_n_nAnon'_strictlyInc in Hgen2.
          unfold StrictlyIncreasing in Hgen2.
          inv Hgen2. inv H2. eassumption. 
    Admitted. 

    Lemma id_vars_nth_error :
      forall A vars1 vars2 n (f: var -> A) v1 v2,
        List.length vars1 = List.length vars2 ->
        NoDup vars1 ->
        nth_error vars1 n = Some v1 ->
        nth_error vars2 n = Some v2 ->
        (f <{ vars1 ~> vars2 }>) v1 = v2.
    Proof.
      intros A vars1. induction vars1; intros vars2 n f v1 v2 Hlen Hdup Hv1 Hv2.
      - destruct vars2 eqn:Hvars2.
        destruct n eqn:Hn; simpl in Hv1; inv Hv1.
        inv Hlen. 
      - destruct vars2 eqn:Hvars2.
        inv Hlen.
        destruct n eqn:Hn.
        + simpl in Hv1, Hv2.
          inv Hv1. inv Hv2.
          simpl. rewrite extend_gss. reflexivity.
        + simpl in *.
          rewrite extend_gso.
          eapply IHvars1. lia.
          inv Hdup. eassumption.
          eassumption.
          eassumption.
          intros Heq.
          eapply nth_error_In in Hv1.
          inv Hdup. contradiction.
    Qed. 

    Lemma nth_FromList :
      forall A l n x,
        nth_error l n = Some x ->
        In A (FromList l) x.
    Proof.
      intros A l n x Hx.
      generalize dependent n. induction l; intros n Hx.
      - destruct n eqn:Hn; inv Hx. 
      - destruct n eqn:Hn.
        + simpl in Hx. inv Hx.
          unfold FromList. simpl. 
          left. reflexivity.
        + simpl in Hx. 
          unfold FromList in *. unfold In in *.
          simpl. right. eapply IHl.
          eassumption.
    Qed.

    Lemma geq_gensym :
      forall next1 next2 na v,
        gensym next1 na = (v, next2) ->
        geq_symgen v next1.
    Proof.
      intros next1 next2 na v Hgen.
      destruct next1. simpl in Hgen.
      destruct p. inv Hgen.
      simpl. zify. lia.
    Qed. 

    Lemma lt_symgen_In_lst :
      forall vars next1 next2 na v',
        Forall (fun v => lt_symgen v next1) vars ->
        gensym next1 na = (v', next2) ->
        ~ In var (FromList vars) v'.
    Proof.
      induction vars; intros next1 next2 na v' Hall Hgen.
      - intros Hin. inv Hin.
      - intros Hin.
        inv Hall. 
        unfold lt_symgen in H1.
        destruct next1. destruct p eqn:Hp.
        inv Hin.
        + assert (Hgt: (v' >= v)%positive).
          { eapply geq_gensym in Hgen. simpl in Hgen. eassumption. } 
          zify. lia.
        + eapply IHvars in H. destruct H.
          eassumption. eassumption.
    Qed.

    Lemma lt_symgen_gensym :
      forall n nenv na v next,
        gensym (SG (n, nenv)) na = (v, next) ->
        lt_symgen n next.
    Proof.
      intros n nenv na v next H.
      simpl in H.
      unfold lt_symgen. destruct next. destruct p.
      inv H. zify. lia.
    Qed.

    Lemma lt_symgen_gensym_2 :
      forall next1 next2 v na,
        gensym next1 na = (v, next2) ->
        lt_symgen v next2.
    Proof.
      intros next1 next2 v na H.
      destruct next1. destruct p. simpl in H.
      destruct next2. destruct p. inv H.
      unfold lt_symgen. zify. lia.
    Qed. 

    Lemma lt_lst_symgen_gensym_n' :
      forall n v1 v2 nenv nenv' vars,
        gensym_n_nAnon' v1 nenv n = (vars, nenv', v2) ->
        (v1 <= v2)%positive.
    Proof.
      induction n; intros v1 v2 nenv nenv' vars Hgen.
      - simpl in Hgen. inv Hgen. zify. lia.
      - simpl in Hgen.
        destruct (gensym_n_nAnon' (Pos.succ v1) (M.set v1 nAnon nenv) n) eqn:Hgen2.
        destruct p eqn:Hp. inv Hgen.
        eapply IHn in Hgen2. zify. lia. 
    Qed. 

    Lemma lt_lst_symgen_gensym_n :
      forall n vars next1 next2,
        gensym_n_nAnon next1 n = (vars, next2) ->
        Forall (fun v => lt_symgen v next2) vars.
    Proof.
      induction n; intros vars next1 next2 Hgen; unfold gensym_n_nAnon in Hgen.
      - destruct next1. destruct p.
        destruct (gensym_n_nAnon' v n 0) eqn:Hgen2.
        destruct p. simpl in Hgen2. inv Hgen2. inv Hgen.
        econstructor.
      - destruct next1. destruct p.
        destruct (gensym_n_nAnon' v n0 (S n)) eqn:Hgen2.
        destruct p. simpl in Hgen2.
        destruct (gensym_n_nAnon' (Pos.succ v) (M.set v nAnon n0) n) eqn:Hgen3.
        destruct p. inv Hgen2. inv Hgen.
        econstructor.
        + unfold lt_symgen. eapply lt_lst_symgen_gensym_n' in Hgen3.
          zify. lia. 
        + specialize IHn with (next1 := (SG (Pos.succ v, (M.set v nAnon n0)))).
          eapply IHn. unfold gensym_n_nAnon.
          destruct (gensym_n_nAnon' (Pos.succ v) (M.set v nAnon n0) n).
          destruct p. inv Hgen3. reflexivity.
    Qed.

    Lemma Forall_lt_symgen_gensym :
      forall vars next1 next2 na v,
        Forall (fun v => lt_symgen v next1) vars ->
        gensym next1 na = (v, next2) ->
        Forall (fun v => lt_symgen v next2) vars.
    Proof.
      induction vars; intros next1 next2 na v Hall Hgen.
      - econstructor.
      - inv Hall. econstructor.
        pose proof lt_symgen_gensym as Hgen2.
        destruct next1. destruct p. eapply Hgen2 in Hgen.  
        unfold lt_symgen in *. destruct next2. destruct p.
        zify. lia.
        eapply IHvars. eassumption. eassumption.
    Qed.

    Lemma Forall_lt_symgen_gensym_n :
      forall vars1 n vars2 next1 next2,
        Forall (fun v => lt_symgen v next1) vars1 ->
        gensym_n_nAnon next1 n = (vars2, next2) ->
        Forall (fun v => lt_symgen v next2) vars1.
    Proof.
      induction vars1; intros n vars2 next1 next2 Hall Hgen.
      - econstructor.
      - econstructor.
        + pose proof lt_lst_symgen_gensym_n as Hgen2.
          inv Hall.
          destruct next1. destruct p. simpl in Hgen.
          destruct (gensym_n_nAnon' v n0 n) eqn:Hgen'. destruct p.
          eapply lt_lst_symgen_gensym_n' in Hgen'.
          inv Hgen. unfold lt_symgen in *. zify. lia. 
        + inv Hall.
          eapply IHvars1. eassumption. eassumption.
    Qed. 

    Lemma gensym_n_nAnon_length_eq :
      forall n next1 next2 next3 next4 l1 l2,
        gensym_n_nAnon next1 n = (l1, next2) ->
        gensym_n_nAnon next3 n = (l2, next4) ->
        Datatypes.length l1 = Datatypes.length l2.
    Proof.
      induction n; intros next1 next2 next3 next4 l1 l2 Hgen1 Hgen2;
        unfold gensym_n_nAnon in *.
      - destruct next1. destruct p.
        destruct (gensym_n_nAnon' v n 0) eqn:H1. destruct p.
        destruct next3. destruct p.
        destruct (gensym_n_nAnon' v1 n1 0) eqn:H2. destruct p.
        simpl in H1, H2. inv H1. inv Hgen1. inv H2. inv Hgen2.
        reflexivity.
      - destruct next1. destruct p.
        destruct (gensym_n_nAnon' v n0 (S n)) eqn:H1. destruct p.
        destruct next3. destruct p.
        destruct (gensym_n_nAnon' v1 n2 (S n)) eqn:H2. destruct p.
        simpl in H1, H2.
        destruct (gensym_n_nAnon' (Pos.succ v) (M.set v nAnon n0) n) eqn:H1'.
        destruct p.
        destruct (gensym_n_nAnon' (Pos.succ v1) (M.set v1 nAnon n2) n) eqn:H2'.
        destruct p.
        inv H1. inv Hgen1.
        inv H2. inv Hgen2.
        simpl. f_equal.
        specialize IHn with (next1 := SG (Pos.succ v, (M.set v nAnon n0)))
                            (next3 := SG (Pos.succ v1, (M.set v1 nAnon n2))).
        eapply IHn.
        destruct (gensym_n_nAnon' (Pos.succ v) (M.set v nAnon n0) n) eqn:H1. destruct p.
        inv H1'. reflexivity.
        destruct (gensym_n_nAnon' (Pos.succ v1) (M.set v1 nAnon n2) n) eqn:H2. destruct p.
        inv H2'. reflexivity.
    Qed.

    Lemma gensym_n'_length_eq :
      forall names v1 v2 v3 v4 nenv1 nenv2 nenv3 nenv4 l1 l2,
        gensym_n' v1 nenv1 names = (l1, nenv2, v2) ->
        gensym_n' v3 nenv3 names = (l2, nenv4, v4) ->
        Datatypes.length l1 = Datatypes.length l2.
    Proof.
      induction names; intros v1 v2 v3 v4 nenv1 nenv2 nenv3 nenv4 l1 l2 Hgen1 Hgen2.
      - simpl in Hgen1, Hgen2. inv Hgen1. inv Hgen2. econstructor.
      - simpl in Hgen1, Hgen2.
        destruct (gensym_n' (Pos.succ v1) (M.set v1 a nenv1) names) eqn:H1.
        destruct p.
        destruct (gensym_n' (Pos.succ v3) (M.set v3 a nenv3) names) eqn:H2.
        destruct p.
        inv H1. inv Hgen1. inv H2. inv Hgen2.
        simpl. f_equal.
        eapply IHnames. eassumption. eassumption.
    Qed. 

    Lemma gensym_n_length_eq :
      forall names next1 next2 next3 next4 vars1 vars2,
        gensym_n next1 names = (vars1, next2) ->
        gensym_n next3 names = (vars2, next4) ->
        Datatypes.length vars1 = Datatypes.length vars2.
    Proof.
      destruct names; intros next1 next2 next3 next4 vars1 vars2 Hgen1 Hgen2.
      - destruct next1. destruct p.
        destruct next3. destruct p.
        simpl in Hgen1, Hgen2. inv Hgen1. inv Hgen2.
        econstructor.
      - destruct next1. destruct p. simpl in Hgen1.
        destruct (gensym_n' (Pos.succ v) (M.set v n n0) names) eqn:H1. destruct p.
        destruct next3. destruct p. simpl in Hgen2.
        destruct (gensym_n' (Pos.succ v1) (M.set v1 n n2) names) eqn:H2. destruct p.
        inv H1. inv Hgen1.
        inv H2. inv Hgen2.
        simpl. f_equal.
        eapply gensym_n'_length_eq. eassumption. eassumption.
    Qed. 

    Lemma StrictlyInc_impl_NoDup :
      forall l,
        StrictlyIncreasing l -> NoDup l.
    Proof.
      induction l; intros H.
      - econstructor.
      - inv H. econstructor.
    Abort.

    Lemma Forall_lt_not_In :
      forall l x,
        Forall (fun v => (x < v)%positive) l ->
        ~ List.In x l.
    Proof.
      induction l; intros x Hall.
      - intros Hnot. inv Hnot.
      - intros Hnot. inv Hall. inv Hnot.
        zify. lia.
        unfold not in IHl. eapply IHl. eassumption. eassumption.
    Qed.

    Lemma Forall_lt_gensym_n_nAnon_Pos_succ :
      forall n v v' nenv nenv' vars,
        gensym_n_nAnon' (Pos.succ v) nenv n = (vars, nenv', v') ->
        Forall (fun v' => (v < v')%positive) vars.
    Proof.
      induction n; intros v v' nenv nenv' vars H.
      - simpl in H. inv H. econstructor.
      - simpl in H.
        destruct (gensym_n_nAnon' (Pos.succ (Pos.succ v))
                                  (M.set (Pos.succ v) nAnon nenv) n) eqn:Hgen.
        destruct p eqn:Hp. inv H. econstructor.
        zify. lia.
        eapply IHn in Hgen. eapply All_Forall.Forall_impl.
        eassumption.
        intros x H. simpl in H. zify. lia.
    Qed.

    Lemma Forall_lt_gensym_n_Pos_succ :
      forall nlst v v' nenv nenv' vars,
        gensym_n' (Pos.succ v) nenv nlst = (vars, nenv', v') ->
        Forall (fun v'=> (v < v')%positive) vars.
    Proof.
      induction nlst; intros v v' nenv nenv' vars H.
      - simpl in H. inv H. econstructor.
      - simpl in H.
        destruct (gensym_n' (Pos.succ (Pos.succ v))
                            (M.set (Pos.succ v) a nenv) nlst) eqn:Hgen.
        destruct p. inv H. econstructor.
        zify. lia.
        eapply IHnlst in Hgen. eapply All_Forall.Forall_impl.
        eassumption.
        intros x H. simpl in H. zify. lia.
    Qed. 

    Lemma gensym_n_nAnon_NoDup :
      forall n vars next1 next2,
        gensym_n_nAnon next1 n = (vars, next2) ->
        NoDup vars.
    Proof.
      induction n; intros vars next1 next2 H; unfold gensym_n_nAnon in *.
      - destruct next1. destruct p.
        destruct (gensym_n_nAnon' v n 0) eqn:Hgen. destruct p.
        simpl in Hgen. inv Hgen. inv H. econstructor.
      - destruct next1. destruct p.
        destruct (gensym_n_nAnon' v n0 (S n)) eqn:Hgen. destruct p.
        simpl in Hgen.
        destruct (gensym_n_nAnon' (Pos.succ v) (M.set v nAnon n0) n) eqn:Hgen2.
        destruct p. inv Hgen. inv H.
        econstructor. eapply Forall_lt_not_In.
        eapply Forall_lt_gensym_n_nAnon_Pos_succ. eassumption.
        specialize IHn with (next1 := SG (Pos.succ v, (M.set v nAnon n0))).
        eapply IHn. destruct (gensym_n_nAnon' (Pos.succ v) (M.set v nAnon n0) n).
        destruct p. inv Hgen2. reflexivity.
    Qed.

    Lemma gensym_n_NoDup :
      forall l next1 next2 vars,
        gensym_n next1 l = (vars, next2) ->
        NoDup vars.
    Proof.
      induction l; intros next1 next2 vars H.
      - destruct next1. destruct p. simpl in H. inv H. econstructor.
      - destruct next1. destruct p. simpl in H.
        destruct (gensym_n' (Pos.succ v) (M.set v a n) l) eqn:Hgen.
        destruct p. inv Hgen. inv H. econstructor.
        eapply Forall_lt_not_In.
        eapply Forall_lt_gensym_n_Pos_succ. eassumption.
        specialize IHl with (next1 := SG ((Pos.succ v), (M.set v a n))).
        eapply IHl. simpl. destruct (gensym_n' (Pos.succ v) (M.set v a n) l).
        destruct p. inv H1. reflexivity.
    Qed. 

    Fixpoint fundefs_to_list (fdefs : fundefs) :=
      match fdefs with
      | Fnil => []
      | Fcons v tg vars e fdefs' => (v, tg, vars, e) :: (fundefs_to_list fdefs')
      end.

    Lemma preord_env_P_inj_set_lists_l_Disjoint S k f rho1 rho2 rho1' xs vs :
      preord_env_P_inj cenv PG S k f rho1 rho2 ->
      set_lists xs vs rho1 = Some rho1' ->
      Disjoint _(FromList xs) S ->
      preord_env_P_inj cenv PG S k f rho1' rho2.
    Proof.
      intros Henv Hnin Hnin' z Hy v' Hget.
      edestruct Henv as [v'' [Hget' Hv]]; eauto.
      erewrite <- set_lists_not_In in Hget. eassumption.
      eassumption. intros Hc. eapply Hnin'. constructor; eauto.
    Qed.

    Lemma preord_env_P_inj_set_lists_r_Disjoint S k f rho1 rho2 rho2' xs vs :
      preord_env_P_inj cenv PG S k f rho1 rho2 ->
      set_lists xs vs rho2 = Some rho2' ->
      Disjoint _ (FromList xs) (image f S) ->
      preord_env_P_inj cenv PG S k f rho1 rho2'.
    Proof.
      intros Henv Hnin Hnin' z Hy v' Hget.
      edestruct Henv as [v'' [Hget' Hv]]; eauto. eexists.
      split. 
      erewrite <- set_lists_not_In. eassumption.
      eassumption. intros Hc. eapply Hnin'. constructor; eauto.
      eapply In_image. eassumption. eassumption.
    Qed.

    Definition cps_cvt_exp_alpha_equiv k :=
      forall e e1 e2 k1 k2 vars1 vars2 rho1 rho2 next1 next2 next3 next4,
        cps_cvt e vars1 k1 next1 cnstrs = Some (e1, next2) ->
        cps_cvt e vars2 k2 next3 cnstrs = Some (e2, next4) ->
        NoDup vars1 ->
        ~(k1 \in (FromList vars1)) ->
        List.length vars1 = List.length vars2 ->
        Forall (fun v => lt_symgen v next1) vars1 ->
        preord_env_P_inj cenv PG (k1 |: FromList vars1) k
                         (id { k1 ~> k2 } <{ vars1 ~> vars2 }>) rho1 rho2 ->
        preord_exp cenv P1 PG k (e1, rho1) (e2, rho2).

    Definition cps_cvt_exps_alpha_equiv k :=
      forall es es1 es2 k1 k2 vars1 vars2 rho1 rho2 next1 next2 next3 next4,
        cps_cvt_exps es vars1 k1 nil next1 cnstrs = Some (es1, next2) ->
        cps_cvt_exps es vars2 k2 nil next3 cnstrs = Some (es2, next4) ->
        NoDup vars1 ->
        ~(k1 \in (FromList vars1)) ->
        List.length vars1 = List.length vars2 ->
        Forall (fun v => lt_symgen v next1) vars1 ->
        preord_env_P_inj cenv PG (k1 |: FromList vars1) k
                         (id { k1 ~> k2 } <{ vars1 ~> vars2 }>) rho1 rho2 ->
        preord_exp cenv P1 PG k (es1, rho1) (es2, rho2). 

    Definition cps_cvt_efnlst_alpha_equiv k :=
      forall efns fdefs1 fdefs2 k1 k2 vars1 vars2 nlst1 nlst2 rho1 rho2
             next1 next2 next3 next4,
        cps_cvt_efnlst efns vars1 nlst1 next1 cnstrs = Some (fdefs1, next2) ->
        cps_cvt_efnlst efns vars2 nlst2 next3 cnstrs = Some (fdefs2, next4) ->
        NoDup vars1 ->
        ~(k1 \in (FromList vars1)) ->
        List.length vars1 = List.length vars2 ->
        Forall (fun v => lt_symgen v next1) vars1 ->
        preord_env_P_inj cenv PG (k1 |: FromList vars1) k
                         (id {k1 ~> k2 } <{ vars1 ~> vars2 }>) rho1 rho2 ->
        preord_env_P_inj cenv PG (k1 |: (FromList vars1 :|: FromList nlst1)) k
                         (id {k1 ~> k2 } <{ vars1 ~> vars2 }> <{ nlst1 ~> nlst2}>)
                         (def_funs fdefs1 fdefs1 rho1 rho1)
                         (def_funs fdefs2 fdefs2 rho2 rho2).

    Definition cps_cvt_branches_alpha_equiv k :=
      forall bs bs1 bs2 k1 k2 r1 r2 vars1 vars2 rho1 rho2 next1 next2 next3 next4,
        cps_cvt_branches bs vars1 k1 r1 next1 cnstrs = Some (bs1, next2) ->
        cps_cvt_branches bs vars1 k2 r2 next3 cnstrs = Some (bs2, next4) ->
        NoDup vars1 ->
        ~(k1 \in (FromList vars1)) ->
        List.length vars1 = List.length vars2 ->
        Forall (fun v => lt_symgen v next1) vars1 ->
        preord_env_P_inj cenv PG (k1 |: FromList vars1) k
                         (id {k1 ~> k2 } <{ vars1 ~> vars2 }>) rho1 rho2 ->
        Forall2 (fun '(c1, e1) '(c2, e2) =>
                   c1 = c2 /\ preord_exp cenv P1 PG k (e1, rho1) (e2, rho2))
                bs1 bs2.

    Definition cps_cvt_alpha_equiv_statement k :=
      cps_cvt_exp_alpha_equiv k /\
      cps_cvt_exps_alpha_equiv k /\
      cps_cvt_efnlst_alpha_equiv k /\
      cps_cvt_branches_alpha_equiv k.

    Definition cps_cvt_val_alpha_equiv_statement k :=
      forall v v1 v2 next1 next2 next3 next4,
        cps_cvt_val v next1 cnstrs = Some (v1, next2) ->
        cps_cvt_val v next3 cnstrs = Some (v2, next4) ->
        preord_val cenv PG k v1 v2.

    Opaque preord_exp'.

    Lemma cps_cvt_env_alpha_equiv :
      forall vs k vs1 vs2 next1 next2 next3 next4,
        cps_cvt_val_alpha_equiv_statement k ->
        cps_cvt_env vs next1 cnstrs = Some (vs1, next2) ->
        cps_cvt_env vs next3 cnstrs = Some (vs2, next4) ->
        Forall2 (preord_val cenv PG k) vs1 vs2.
    Proof.
      induction vs; intros k vs1 vs2 next1 next2 next3 next4 IH Hcvt1 Hcvt2.
      - simpl in Hcvt1, Hcvt2. inv Hcvt1. inv Hcvt2. econstructor.
      - simpl in Hcvt1.
        destruct (cps_cvt_val a next1 cnstrs) eqn:Hval1. 2: { inv Hcvt1. } 
        destruct p. destruct (cps_cvt_env vs s cnstrs) eqn:Henv1. 2: { inv Hcvt1. } 
        destruct p. inv Hcvt1.
        simpl in Hcvt2.
        destruct (cps_cvt_val a next3 cnstrs) eqn:Hval2. 2: { inv Hcvt2. }
        destruct p. destruct (cps_cvt_env vs s0 cnstrs) eqn:Henv2. 2: { inv Hcvt2. }
        destruct p. inv Hcvt2.
        econstructor.
        + eapply IH. eassumption. eassumption.
        + eapply IHvs. eassumption. eassumption. eassumption.
    Qed.

    Definition leq_symgen := 
    fun (v1 : var) (next : symgen) =>
      match next with
      | SG (v2, _) => (v1 <= v2)%positive
      end.

    Definition lt_symgen_compare :=
      fun (next1 : symgen) (next2 : symgen) =>
      match next1, next2 with
      | SG (v1, _), SG (v2, _) => (v1 <= v2)%positive
      end.

    Lemma nth_error_Some_eq_nth :
      forall l n v,
        nth_error l n = Some v ->
        nth l n = v.
    Proof.
      induction l; intros n v H.
      - destruct n.
        simpl in *. inv H.
        simpl in *. inv H.
      - unfold nth. unfold nth_default. destruct n.
        simpl in *. inv H. reflexivity.
        simpl in *. rewrite H. reflexivity.
    Qed. 

    Lemma cps_cvt_efnlst_find_def :
      forall fn l1 l2 l3 l4 l1' l3' next1 next2 next3 next4 n f1 f2 tg xs1 e1
             na1 efn v1,
        NoDup l1 ->
        NoDup l3 ->
        Datatypes.length l1 = Datatypes.length l3 ->
        cps_cvt_efnlst fn (l1' ++ l2) l1 next1 cnstrs = Some (f1, next2) ->
        cps_cvt_efnlst fn (l3' ++ l4) l3 next3 cnstrs = Some (f2, next4) ->
        (nth_error (efnlst_as_list fn) n) = Some (na1, efn) ->
        nth_error l1 n = Some v1 ->
        find_def v1 f1 = Some (tg, xs1, e1) ->
        exists e2 v2 x1 k1 x2 k2 next5 next6 next7 next8
               na1' na2 esrc1,
          geq_symgen x1 next1 /\ geq_symgen x2 next3 /\
          (k1 > x1)%positive /\ (k2 > x2)%positive /\
          lt_symgen k1 next5 /\ lt_symgen k2 next7 /\
          nth_error l3 n = Some v2 /\
          find_def v2 f2 = Some (tg, [k2; x2], e2) /\
          xs1 = [k1; x1] /\
          efn = Lam_e na1' esrc1 /\
          (nth_error (efnlst_as_list fn) n) = Some (na2, (Lam_e na1' esrc1)) /\ 
          cps_cvt esrc1 (x1 :: (l1' ++ l2)) k1 next5 cnstrs = Some (e1, next6)
          /\
          cps_cvt esrc1 (x2 :: (l3' ++ l4)) k2 next7 cnstrs = Some (e2, next8).
    Proof.
      induction fn; intros l1 l2 l3 l4 l1' l3' next1 next2 next3 next4 n'
                           f1 f2 tg xs1 e1 na1 efn v1
                           Hdup1 Hdup2 Hlen Hcvt_fn1 Hcvt_fn2 Herror Hnth Hfind.
      - simpl in Hcvt_fn1. inv Hcvt_fn1. simpl in Hfind. inv Hfind.
      - simpl in *.
        destruct (gensym next1 (nNamed "fix_x")) eqn:Hgen_x1.
        destruct (gensym s (nNamed "fix_k")) eqn:Hgen_k1.
        destruct e eqn:He1; inv Hcvt_fn1.
        destruct (cps_cvt e0 (v :: l1' ++ l2) v0 s0 cnstrs) eqn: Hcvt1.
        2: { inv H0. } destruct p.
        destruct (cps_cvt_efnlst fn (l1' ++ l2) (tl l1) s1 cnstrs) eqn:Hrec1.
        2: { inv H0. } destruct p. inv H0.
        destruct (gensym next3 (nNamed "fix_x")) eqn:Hgen_x2.
        destruct (gensym s2 (nNamed "fix_k")) eqn:Hgen_k2. 
        destruct (cps_cvt e0 (v2 :: l3' ++ l4) v3 s3 cnstrs) eqn:Hcvt2.
        2: { inv Hcvt_fn2. } destruct p.
        destruct (cps_cvt_efnlst fn (l3' ++ l4) (tl l3) s4 cnstrs) eqn:Hrec2.
        2: { inv Hcvt_fn2. } destruct p. inv Hcvt_fn2.
        destruct n' eqn:Hn'.
        + simpl in *. inv Herror. unfold nth in *.
          unfold nth_default in *. simpl in *. destruct l1 eqn:Hl1.
          * destruct l3 eqn:Hl3.
            -- simpl in *. inv Hnth. 
            -- simpl in *. inv Hnth.
          * destruct l3 eqn:Hl3.
            -- inv Hlen. 
            -- simpl in *. inv Hnth.
               rewrite peq_true in *. inversion Hfind.
               repeat eexists.
               eapply geq_gensym. eassumption.
               eapply geq_gensym. eassumption.
               eapply geq_gensym in Hgen_k1.
               destruct next1. destruct p. eapply lt_symgen_gensym_2 in Hgen_x1.
               unfold lt_symgen in Hgen_x1. unfold geq_symgen in Hgen_k1.
               destruct s. destruct p. zify. lia.
               5: { rewrite <- H2. eassumption. }
               5: { eassumption. }
               admit.
               eapply lt_symgen_gensym_2. eassumption.
               eapply lt_symgen_gensym_2. eassumption.
               rewrite peq_true. reflexivity. 
        + simpl in *. destruct l1 eqn:Hl1.
          simpl in Hfind. inv Hnth.
          destruct l3 eqn:Hl3. inv Hlen.
          simpl in *. rewrite peq_false in *.
          inv Hdup1. inv Hdup2. edestruct IHfn.
          eapply H2. eapply H4.
          inv Hlen. reflexivity.
          eassumption. 
          eassumption.
          eassumption.
          eassumption.
          eassumption.
          destructAll.
          repeat eexists; try eauto. admit. admit.
          rewrite peq_false. eassumption.
          admit. admit. 
    Admitted.


    Lemma cps_cvt_efnlst_nth_error :
      forall fnl l1 l2 n v f next1 next2,
        N.to_nat (efnlst_length fnl) = Datatypes.length l1 ->
        cps_cvt_efnlst fnl l2 l1 next1 cnstrs = Some (f, next2) ->
        nth_error l1 n = Some v ->
        exists na e,
          nth_error (efnlst_as_list fnl) n = Some (na, e).
    Proof.
      induction fnl; intros l1 l2 n' v f next1 next2 Hlen Hcvt Hnth.
      - simpl in *. inv Hcvt.
        destruct n'.
        simpl in *. destruct l1. inv Hnth. inv Hlen.
        simpl in *. destruct l1. inv Hnth. inv Hlen.
      - destruct l1. destruct n'.
        inv Hnth. inv Hnth. 
        simpl in Hcvt.
        destruct (gensym next1 (nNamed "fix_x")) eqn:Hgen_x.
        destruct (gensym s (nNamed "fix_k")) eqn:Hgen_k.
        destruct e eqn:He; inv Hcvt.
        destruct (cps_cvt e0 (v1 :: l2) v2 s0 cnstrs) eqn:Hcvt. 2: { inv H0. } 
        destruct p.
        destruct (cps_cvt_efnlst fnl l2 l1 s1 cnstrs) eqn:Hcvt2. 2: { inv H0. }
        destruct p. inv H0.
        simpl. destruct n'.
        + simpl in *. repeat eexists.
        + simpl in *. eapply IHfnl.
          destruct (efnlst_length fnl). simpl in Hlen.
          rewrite Pos2Nat.inj_1 in Hlen.
          inv Hlen. simpl. eassumption. 
          simpl in *. destruct p; try (zify; lia). 
          eassumption. eassumption.
    Qed. 

    Lemma cps_val_alpha_equiv :
      forall k,
        (forall m, (m < k)%nat -> cps_cvt_alpha_equiv_statement m) ->
        cps_cvt_val_alpha_equiv_statement k.
    Proof.
      induction k using lt_wf_rec. intros IH.
      intros v. induction v using value_ind';
                  intros v1 v2 next1 next2 next3 next4 Hv1 Hv2;
                  rewrite cps_cvt_val_eq in *.
      - simpl in Hv1, Hv2.
        destruct (cps_cvt_env vs next1 cnstrs) eqn:Henv1. destruct p. inv Hv1.
        destruct (cps_cvt_env vs next3 cnstrs) eqn:Henv2. destruct p. inv Hv2.
        rewrite preord_val_eq. simpl. split. reflexivity.
        induction H0. admit.
        simpl in Henv1, Henv2.
        admit. admit. admit.
      - admit.
      - simpl in Hv1, Hv2.
        destruct (cps_cvt_env vs next1 cnstrs) eqn:Henv1; inv Hv1.
        destruct p eqn:Hp.
        destruct (gensym_n s (rho_names vs)) eqn:Hgen_n1.
        destruct (set_lists l0 l (M.empty cps.val)) eqn:Hset. 2: { inv H2. }
        destruct (gensym s0 (nNamed "k_lam")) eqn:Hgen_k1.
        destruct (gensym s1 (nNamed "x_lam")) eqn:Hgen_x1.
        destruct (gensym s2 na) eqn:Hen_f1.
        destruct (cps_cvt e (v0 :: l0) v s3 cnstrs) eqn:Hcvt1. 2: { inv H2. }
        destruct p0. inv H2.
        destruct (cps_cvt_env vs next3 cnstrs) eqn:Henv2; inv Hv2.
        destruct p eqn:Hp.
        destruct (gensym_n s4 (rho_names vs)) eqn:Hgen_n2.
        destruct (set_lists l2 l1 (M.empty cps.val)) eqn:Hset2. 2: { inv H2. }
        destruct (gensym s5 (nNamed "k_lam")) eqn:Hgen_k2.
        destruct (gensym s6 (nNamed "x_lam")) eqn:Hgen_x2.
        destruct (gensym s7 na) eqn:Hen_f2.
        destruct (cps_cvt e (v4 :: l2) v1 s8 cnstrs) eqn:Hcvt2. 2: { inv H2. } 
        destruct p0. inv H2.
        rewrite preord_val_eq. unfold preord_val'.
        { intros vs1 vs2 j tg xs1 e2 rho1' Hlen_eq Hfind Hsetl.
          simpl in Hfind. simpl.
          rewrite peq_true in *.
          inv Hfind.
          pose proof (set_lists_length2) as Hsetl2.
          edestruct Hsetl2 with (rho := (def_funs (Fcons v3 func_tag [v; v0] e2 Fnil)
                                                       (Fcons v3 func_tag [v; v0] e2 Fnil) t t))
                                     (xs1 := [v; v0]) (vs1 := vs1)
                                     (xs2 := [v5; v5]) (vs2 := vs2); clear Hsetl2.
          econstructor.
          eassumption.
          symmetry. eapply Hsetl.
          simpl in Hsetl.
          destruct vs1. inv Hsetl.
          destruct vs1. inv Hsetl.
          destruct vs1; inv Hsetl.
          simpl in H1.
          destruct vs2. inv H1.
          destruct vs2. inv H1.
          destruct vs2. 2: { inv H1. } 
          eexists. eexists. eexists. split.
          reflexivity. split.
          reflexivity.
          intros Hlt2 Hall.
          eapply preord_exp_post_monotonic.
          eapply HinclG.
          eapply preord_exp_monotonic.
          unfold cps_cvt_alpha_equiv_statement in IH.
          edestruct IH with (m := j) as (IHstep & _). eassumption.
          eapply IHstep. 
          eassumption.
          eassumption.
          admit. admit.
          simpl. f_equal. (* similar to gensym_n_length_eq *) admit.  
          admit.
          simpl.
          (* Zoe: Something broke here from flipping the args *)
          (* eapply preord_env_P_inj_set_alt. *)
          (* rewrite Setminus_Union_distr. *)
          (* rewrite FromList_cons. (* normalize_sets *) *)
          (* assert (Hsets: ([set v] \\ [set v0] :|: (v0 |: FromList l0 \\ [set v0])) *)
          (*                  <--> ([set v] :|: (FromList l0))). *)
          (* { rewrite Setminus_Union_distr. *)
          (*   rewrite Setminus_Same_set_Empty_set. normalize_sets. *)
          (*   rewrite Setminus_Disjoint. rewrite Setminus_Disjoint. *)
          (*   reflexivity. admit. admit. } *)
          (* rewrite Hsets. clear Hsets. *)
          (* rewrite extend_extend_lst_commut. *)
          (* eapply preord_env_P_inj_set_alt. *)
          (* rewrite Setminus_Union_distr at 1. *)
          (* rewrite Setminus_Same_set_Empty_set. *)
          (* rewrite Setminus_Disjoint. normalize_sets. *)
          (* eapply preord_env_P_inj_set_not_In_P_l. *)
          (* eapply preord_env_P_inj_set_not_In_P_r. *)
          (* eapply preord_env_P_inj_set_lists_alt. *)
          (* 7: { eassumption. } 7: { eassumption. } *)
          (* econstructor. rewrite M.gempty in H3. inv H3. *)
          (* eapply cps_cvt_env_alpha_equiv. *)
          (* eapply H. eassumption. intros m Hlt3. *)
          (* eapply IH. lia. eassumption. eassumption.  *)
          (* admit. admit. admit. *)
          (* rewrite Setminus_Same_set_Empty_set. rewrite image_Empty_set. *)
          (* eapply Disjoint_Empty_set_l. *)
          (* admit. *)
          (* admit. admit.  *)
          (* inversion Hall. inversion H7. eassumption. *)
          (* admit. *)
          (* admit. admit. admit. *)
          (* inversion Hall. eassumption. *)
          admit.
          lia.
        }

      - simpl in Hv1, Hv2.
        destruct (cps_cvt_env vs next1 cnstrs) eqn:Henv1. 2: { inv Hv1. }
        destruct p. destruct (gensym_n s (rho_names vs)) eqn:Hgen_n1.
        destruct (set_lists l0 l (M.empty cps.val)) eqn:Hset1. 2: { inv Hv1. }
        destruct (efnlst_names fnl) eqn:Hefns1.
        destruct (gensym_n s0 l1) eqn:Hgen_lst1.
        destruct (cps_cvt_efnlst fnl (l2 ++ l0) l2 s1 cnstrs) eqn:Hcvt_efns1.
        2: { inv Hv1. } destruct p. inv Hv1.
        destruct (cps_cvt_env vs next3 cnstrs) eqn:Henv2. 2: { inv Hv2. }
        destruct p. destruct (nth_error l2 (N.to_nat n)) eqn:Herr1; inv H2.
        destruct (gensym_n s3 (rho_names vs)) eqn:Hgen_n2.
        destruct (set_lists l4 l3 (M.empty cps.val)) eqn:Hset2. 2: { inv Hv2. } 
        destruct (gensym_n s2 l1) eqn:Hgen_lst2.
        destruct (cps_cvt_efnlst fnl (l5 ++ l4) l5 s4 cnstrs) eqn:Hcvt_efns2.
        2: { inv Hv2. } destruct p.
        destruct (nth_error l5 (N.to_nat n)) eqn:Herr2; inv Hv2.
        rewrite preord_val_eq. unfold preord_val'.
        { intros vs1 vs2 j tg xs1 e2 rho1' Hlen_eq Hfind Hsetl.
          edestruct (cps_cvt_efnlst_nth_error).
          admit. eapply Hcvt_efns1. eassumption.
          edestruct H1.  
          pose proof (cps_cvt_efnlst_find_def) as Hexists.
          edestruct Hexists; clear Hexists.
          4: { eapply Hcvt_efns1. } 4: { eapply Hcvt_efns2. } 
          eapply gensym_n_NoDup. eassumption.
          eapply gensym_n_NoDup. eassumption.
          admit.
          2: { eassumption. } 
          eassumption.
          eassumption. 
          destructAll. 
          pose proof (set_lists_length2) as Hsetl2.
          edestruct Hsetl2 with (xs1 := [x4; x3]) (vs1 := vs1)
                                (vs2 := vs2); clear Hsetl2. admit. eassumption.
          symmetry. eassumption.
          eexists. eexists. eexists. split.
          rewrite Herr2 in H9. inv H9. eassumption. split. 
          symmetry. eassumption.
          intros Hlt Hall.
          unfold cps_cvt_alpha_equiv_statement in IH.
          edestruct IH with (m := j) as (IHstep & _). eassumption.
          unfold cps_cvt_exp_alpha_equiv in IHstep.
          eapply preord_exp_post_monotonic. eapply HinclG. eapply IHstep.
          eassumption.
          eassumption.
    Abort.

    Lemma f_eq_subdomain_extend_lst
          (A : Type) (S : Ensemble positive) (f f' : positive -> A)
          (xs : list positive) (ys : list A) :
      length xs = length ys -> 
      f_eq_subdomain S f f' ->
      f_eq_subdomain (FromList xs :|: S) (f <{xs ~> ys}>) (f' <{xs ~> ys}>).
    Proof.
      revert A S f f' ys.
      induction xs; intros.
      - simpl. normalize_sets. rewrite Union_Empty_set_neut_l. eassumption.
      - destruct ys; simpl. inv H. inv H. simpl.
        normalize_sets. rewrite <- Union_assoc. eapply f_eq_subdomain_extend. 
        eapply IHxs; eauto.
    Qed. 

    Lemma cps_cvt_alpha_equiv :
      forall k, cps_cvt_alpha_equiv_statement k.
    Proof.
      induction k using lt_wf_rec.
      eapply my_exp_ind. 
      - intros n e1 e2 k1 k2 vars1 vars2 rho1 rho2
               next1 next2 next3 next4 He1 He2 Hdup Hnot Hlen Hlt Henv.
        simpl in He1, He2.
        destruct (nth_error vars1 (N.to_nat n)) eqn:Hnth1. 2: { inv He1. }
        destruct (nth_error vars2 (N.to_nat n)) eqn:Hnth2. 2: { inv He2. } 
        inv He1. inv He2.
        eapply preord_exp_app_compat.
        + admit.
        + admit.
        + assert (Heq: k2 = ((id {k1 ~> k2}) <{ vars1 ~> vars2 }>) k1).
          { rewrite extend_lst_gso.
            rewrite extend_gss. reflexivity.
            eassumption. }
          rewrite Heq.
          eapply Henv. left. reflexivity.
        + econstructor.
          * assert (Heq: ((id {k1 ~> k2}) <{ vars1 ~> vars2 }>) v = v0). 
            { eapply id_vars_nth_error; eassumption. }
            rewrite <- Heq.
            eapply Henv. right.
            eapply nth_FromList. eassumption. 
          * econstructor. 
      - intros na e IH e1 e2 k1 k2 vars1 vars2 rho1 rho2 next1 next2 next3 next4
               He1 He2 Hdup Hnot Hlen Hlt Henv.
        simpl in He1, He2.
        destruct (gensym next1 (nNamed "k_lam")) eqn:Hgen_k1.
        destruct (gensym s (nNamed "x_lam")) eqn:Hgen_x1.
        destruct (gensym s0 na) eqn:Hgen_f1.
        destruct (cps_cvt e (v0 :: vars1) v s1 cnstrs) eqn:Hcvt_e1.
        2: { inv He1. } 
        destruct p eqn:Hp. inv He1.
        destruct (gensym next3 (nNamed "k_lam")) eqn:Hgen_k2.
        destruct (gensym s2 (nNamed "x_lam")) eqn:Hgen_x2.
        destruct (gensym s3 na) eqn:Hgen_f2.
        destruct (cps_cvt e (v3 :: vars2) v2 s4 cnstrs) eqn:Hcvt_e2.
        2: { inv He2. } 
        destruct p eqn:Hp. inv He2.
        eapply preord_exp_fun_compat.
        + admit.
        + admit.
        + { eapply preord_exp_monotonic. 
            simpl. eapply preord_exp_app_compat.
            - admit.
            - admit.
            - assert (Heq: k2 = ((id {k1 ~> k2}) <{ vars1 ~> vars2 }>) k1).
              { rewrite extend_lst_gso.
                rewrite extend_gss. reflexivity.
                eassumption. }
              rewrite Heq.
              eapply preord_env_P_inj_set_not_In_P_l.
              eapply preord_env_P_inj_set_not_In_P_r.
              eassumption. 
              admit. admit. left. reflexivity. 
            - econstructor. 2: { econstructor. }
              simpl. unfold preord_var_env.
              intros v5 Hset.
              rewrite M.gss in Hset. inv Hset.
              eexists. split.
              rewrite M.gss. reflexivity.              
              rewrite preord_val_eq. unfold preord_val'.
              { intros vs1 vs2 j tg xs1 e2 rho1' Hlen_eq Hfind Hset.
                simpl in Hfind. simpl.
                rewrite peq_true in *.
                inv Hfind.
                pose proof (set_lists_length2) as Hset2.
                edestruct Hset2 with (rho := (def_funs (Fcons v1 func_tag [v; v0] e2 Fnil)
                                                       (Fcons v1 func_tag [v; v0] e2 Fnil) rho1 rho1))
                                     (xs1 := [v; v0]) (vs1 := vs1)
                                     (xs2 := [v3; v2]) (vs2 := vs2); clear Hset2.
                econstructor. 
                eassumption.
                symmetry. eapply Hset.
                simpl in Hset.
                destruct vs1. inv Hset.
                destruct vs1. inv Hset.
                destruct vs1; inv Hset.
                simpl in H0.
                destruct vs2. inv H0.
                destruct vs2. inv H0.
                destruct vs2. 2: { inv H0. } inv H0. 
                eexists. eexists. eexists. split.
                reflexivity. split.
                reflexivity.
                intros Hlt2 Hall.
                eapply preord_exp_post_monotonic.
                eapply HinclG.
                eapply preord_exp_monotonic.
                edestruct H with (m := j) as (IHstep & _). eassumption.
                eapply IHstep.
                eassumption.
                eassumption.
                admit. admit.
                simpl. f_equal. eassumption.
                admit. simpl.
                (* Zoe: Something broke here because of argument flip *)
                (* eapply preord_env_P_inj_set_alt. *)
                (* rewrite Setminus_Union_distr at 1. *)
                (* rewrite FromList_cons. (* normalize_sets *) *)
                (* assert (Hsets: ([set v] \\ [set v0] :|: *)
                (*                         (v0 |: FromList vars1 \\ [set v0])) *)
                (*                  <--> ([set v] :|: (FromList vars1))). *)
                (* { rewrite Setminus_Union_distr. *)
                (*   rewrite Setminus_Same_set_Empty_set. normalize_sets. *)
                (*   rewrite Setminus_Disjoint. rewrite Setminus_Disjoint. *)
                (*   reflexivity. admit. admit. } *)
                (* rewrite Hsets. clear Hsets. *)
                (* rewrite extend_extend_lst_commut. *)
                (* eapply preord_env_P_inj_set_alt. *)
                (* rewrite Setminus_Union_distr at 1. *)
                (* rewrite Setminus_Same_set_Empty_set. *)
                (* rewrite Setminus_Disjoint. normalize_sets. *)
                (* eapply preord_env_P_inj_set_not_In_P_l. *)
                (* eapply preord_env_P_inj_set_not_In_P_r. *)
                (* (* follows from Henv? *) *)
                (* eapply preord_env_P_inj_f_eq_subdomain. *)
                (* eapply preord_env_P_inj_antimon. *)
                (* eapply preord_env_P_inj_monotonic. *)
                (* 2: { eassumption. } lia. *)
                (* sets. *)
                (* assert (Hsets : (FromList vars1 :|: Empty_set _) <--> *)
                (*                                                  (FromList vars1)). *)
                (* { sets. } *)
                (* rewrite <- Hsets. *)
                (* eapply f_eq_subdomain_extend_lst. *)
                (* eassumption. intros x Hin. inv Hin.  *)
                (* admit. *)
                (* admit. admit.  *)
                (* inversion Hall. inversion H6. eassumption. *)
                (* admit. *)
                (* admit. admit. eassumption. *)
                (* inversion Hall. eassumption. *)
                admit. 
                lia.
              }
            - lia. }
      - intros e1 IHe1 e2 IHe2 e1' e2' k1 k2 vars1 vars2 rho1 rho2
               next1 next2 next3 next4 He1 He2 Hdup Hnot Hlen Hlt Henv.
        simpl in He1, He2.
        destruct (gensym next1 (nNamed "k1")) eqn:Hgen1_k1.
        destruct (gensym s (nNamed "x1")) eqn:Hgen1_x1.
        destruct (cps_cvt e1 vars1 v s0 cnstrs) eqn:Hcvt1_e1. 2: { inv He1. }
        destruct p. destruct (gensym s1 (nNamed "k2")) eqn:Hgen1_k2.
        destruct (gensym s2 (nNamed "x2")) eqn:Hgen1_x2.
        destruct (cps_cvt e2 vars1 v1 s3 cnstrs) eqn:Hcvt1_e2. 2: { inv He1. }
        destruct p. inv He1.
        destruct (gensym next3 (nNamed "k1")) eqn:Hgen2_k1.
        destruct (gensym s4 (nNamed "x1")) eqn:Hgen2_x1.
        destruct (cps_cvt e1 vars2 v3 s5 cnstrs) eqn:Hcvt2_e1. 2: { inv He2. }
        destruct p. destruct (gensym s6 (nNamed "k2")) eqn:Hgen2_k2.
        destruct (gensym s7 (nNamed "x2")) eqn:Hgen2_x2.
        destruct (cps_cvt e2 vars2 v5 s8 cnstrs) eqn:Hgen2_e2. 2: { inv He2. }
        destruct p. inv He2.
        eapply preord_exp_fun_compat.
        + admit.
        + admit.
        + simpl. eapply preord_exp_monotonic.
          eapply IHe1. eassumption. eassumption. eassumption.
          admit. eassumption. admit.
          rewrite extend_extend_lst_commut.
          eapply preord_env_P_inj_set_alt.
          rewrite Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set.
          rewrite Setminus_Disjoint. normalize_sets.
          (* from Henv *) admit. admit.
          rewrite preord_val_eq. unfold preord_val'.
          { intros vs1 vs2 j tg xs1 e5 rho1' Hlen_eq Hfind Hset.
            simpl in Hfind. simpl.
            rewrite peq_true in *.
            inv Hfind.
            pose proof (set_lists_length2) as Hset2.
            set(tg:= kon_tag).
            edestruct Hset2 with (rho := (def_funs
                                            (Fcons v tg [v0]
                                                   (Efun (Fcons v1 tg [v2]
                                                                (Eapp v0 func_tag
                                                                      [k1; v2]) Fnil)
                                                         e0) Fnil)
                                            (Fcons v tg [v0]
                                                   (Efun (Fcons v1 tg [v2]
                                                                (Eapp v0 func_tag
                                                                      [k1; v2]) Fnil)
                                                         e0) Fnil)
                                            rho1 rho1))
                                     (xs1 := [v0]) (vs1 := vs1)
                                     (xs2 := [v4]) (vs2 := vs2); clear Hset2.
            now econstructor. eassumption.
            symmetry. eassumption.
            simpl in Hset. destruct vs1. inv Hset.
            destruct vs1; inv Hset.
            eexists. eexists. eexists. split.
            reflexivity. split.
            symmetry. eassumption.
            simpl in H0. destruct vs2. inv H0.
            destruct vs2. 2: { inv H0. } inv H0. 
            intros Hlt2 Hall.  
            eapply preord_exp_fun_compat.
            - admit.
            - admit.
            - simpl. eapply preord_exp_monotonic.
              eapply IHe2.
              eassumption. eassumption. eassumption.
              admit.
              eassumption. admit.
              { rewrite extend_extend_lst_commut.
                eapply preord_env_P_inj_set_alt. rewrite Setminus_Union_distr.
                rewrite Setminus_Same_set_Empty_set. rewrite Setminus_Disjoint.
                normalize_sets.
                eapply preord_env_P_inj_set_not_In_P_l.
                eapply preord_env_P_inj_set_not_In_P_r.
                eapply preord_env_P_inj_set_not_In_P_l.
                eapply preord_env_P_inj_set_not_In_P_r.
                (* from Henv *) admit.
                admit. admit. admit. admit. admit.
                rewrite preord_val_eq. unfold preord_val'.
                intros vs1 vs2 l tg' xs1 e5 rho1' Hlen_eq2 Hfind Hset.
                simpl in *.
                rewrite peq_true in *. inv Hfind.
                pose proof (set_lists_length2) as Hset2.
                edestruct Hset2 with (xs1 := [v2]) (vs1 := vs1)
                                     (xs2 := [v6]) (vs2 := vs2); clear Hset2.
                now econstructor. eassumption.
                symmetry. eassumption.
                eexists. eexists. eexists. split.
                reflexivity. split.
                symmetry. eassumption.
                intros Hlt3 Hall2.
                eapply preord_exp_app_compat.
                - admit.
                - admit.
                - admit.
                - econstructor. admit. admit.
                - admit.
                - admit.
                - admit.
                - eassumption. }
              lia. }
          admit.
          admit.
          admit. eassumption. lia.
      - intros dc es IH e1 e2 k1 k2 vars1 vars2 rho1 rho2
               next1 next2 next3 next4 He1 He2 Hdup Hnot Hlen Hlt Henv.
        simpl in He1, He2.
        destruct (gensym next1 (nNamed "k'")) eqn:Hgen_k1.
        destruct (gensym s (nNamed "x'")) eqn:Hgen_x1.
        destruct (gensym_n_nAnon s0 (N.to_nat (exps_length es))) eqn:Hgen_n_es1.
        destruct (cps_cvt_exps es vars1 v [] s1 cnstrs) eqn:Hcvt_exps1.
        2: { inv He1. } 
        destruct p eqn:Hp. inv He1.
        destruct (gensym next3 (nNamed "k'")) eqn:Hgen_k2.
        destruct (gensym s2 (nNamed "x'")) eqn:Hgen_x2.
        destruct (gensym_n_nAnon s3 (N.to_nat (exps_length es))) eqn:Hgen_n_es2.
        destruct (cps_cvt_exps es vars2 v1 [] s4 cnstrs) eqn:Hcvt_exps2.
        2: { inv He2. } 
        destruct p eqn:Hp. inv He2.
        eapply preord_exp_fun_compat.
        + admit.
        + admit.
        + eapply preord_exp_monotonic.
          { eapply IH.
            - eassumption.
            - eassumption.
            - eassumption.
            - eapply lt_symgen_In_lst. eassumption. eassumption.
            - eassumption.
            - eapply Forall_lt_symgen_gensym_n.
              eapply Forall_lt_symgen_gensym.
              eapply Forall_lt_symgen_gensym.
              eassumption. eassumption. eassumption. eassumption. 
            - simpl.
              rewrite extend_extend_lst_commut. 
              eapply preord_env_P_inj_set_alt.
              rewrite Setminus_Union_distr at 1.
              eapply preord_env_P_inj_f_eq_subdomain.
              eapply preord_env_P_inj_antimon.
              eassumption. sets.
              admit.
              rewrite preord_val_eq. unfold preord_val'.
              { intros vs1 vs2 j tg xs1 e1 rho1' Hlen_eq Hfind Hset.
                simpl in Hfind. simpl.
                rewrite peq_true in *. 
                inv Hfind.
                pose proof (set_lists_length2) as Hset2.
                simpl in Hset.
                edestruct Hset2 with (rho := (M.set v
                                                    (Vfun rho1
                                                          (Fcons v kon_tag xs1
                                                                 (Econstr v0 (dcon_to_tag dc cnstrs) xs1 (Eapp k1 kon_tag [v0]))
                                                                 Fnil) v) rho1))
                                     (xs1 := xs1) (vs1 := vs1) (xs2 := l0) (vs2 := vs2);
                  clear Hset2. 
                eapply gensym_n_nAnon_length_eq. eassumption. eassumption. 
                eassumption.
                symmetry. eapply Hset.
                eexists. eexists. eexists. split.
                reflexivity. split.
                symmetry. eassumption.
                intros Hlt2 Hall.
                eapply preord_exp_constr_compat.
                admit.
                admit.
                rewrite <- map_extend_lst_same with (xs := xs1) (xs' := l0)
                                                    (f := id).
                eapply Forall2_preord_var_env_map.
                2: { reflexivity. }
                eapply preord_env_P_inj_set_lists_alt.
                rewrite Setminus_Same_set_Empty_set.
                intros x' Hin. inv Hin.
                eassumption.
                eapply gensym_n_nAnon_NoDup. eassumption.
                eapply gensym_n_nAnon_NoDup. eassumption.
                eapply gensym_n_nAnon_length_eq. eassumption. eassumption.
                rewrite image_id.  rewrite Setminus_Same_set_Empty_set.
                now sets.
                now eauto.
                eassumption.
                eapply gensym_n_nAnon_NoDup. eassumption.
                eapply gensym_n_nAnon_length_eq. eassumption. eassumption.
                intros m vs0 vs3 Hlt3 Hall2.
                eapply preord_exp_app_compat.
                admit.
                admit.
                assert (Heq: k2 = ((id {k1 ~> k2}) <{ vars1 ~> vars2 }>) k1).
                { rewrite extend_lst_gso.
                  rewrite extend_gss. reflexivity.
                  eassumption. }
                rewrite Heq.
                eapply preord_env_P_inj_set_not_In_P_l.
                eapply preord_env_P_inj_set_not_In_P_r.
                eapply preord_env_P_inj_set_lists_l_Disjoint.
                2: { now eauto. }
                eapply preord_env_P_inj_set_lists_r_Disjoint.
                2: { eassumption. }
                eapply preord_env_P_inj_set_not_In_P_l.
                eapply preord_env_P_inj_set_not_In_P_r.
                eapply preord_env_P_inj_monotonic.
                2 : { eassumption. }
                lia.
                admit. admit. admit. admit. admit. admit.
                admit.
                econstructor.
                unfold preord_var_env.
                intros v3 Hv3.
                rewrite M.gss in Hv3. inversion Hv3. rewrite M.gss.
                eexists. split. reflexivity.
                rewrite preord_val_eq. econstructor.
                reflexivity.
                eapply Forall2_Forall2_asym_included. eassumption.
                econstructor. }
              admit.
              admit.
              admit.
              eassumption. }
          lia.
      - admit.
      - intros na e1 IHe1 e2 IHe2 e1' e2' k1 k2 vars1 vars2 rho1 rho2
               next1 next2 next3 next4 He1 He2 Hdup Hnot Hlen Hlt Henv.
        simpl in He1, He2.
        destruct (gensym next1 na) eqn:Hgen_na1.
        destruct (gensym s (nNamed "k")) eqn:Hgen_k1.
        destruct (cps_cvt e2 (v :: vars1) k1 s0 cnstrs) eqn:Hcvt1_e2. 2: { inv He1. }
        destruct p. destruct (cps_cvt e1 vars1 v0 s1 cnstrs) eqn:Hcvt1_e1.
        2: { inv He1. } destruct p. inv He1.
        destruct (gensym next3 na) eqn:Hgen_na2.
        destruct (gensym s2 (nNamed "k")) eqn:Hgen_k2.
        destruct (cps_cvt e2 (v1 :: vars2) k2 s3 cnstrs) eqn:Hcvt2_e2. 2: { inv He2. }
        destruct p. destruct (cps_cvt e1 vars2 v2 s4 cnstrs) eqn:Hcvt2_e1.
        2: { inv He2. } destruct p. inv He2. 
        eapply preord_exp_fun_compat.
        + admit.
        + admit.
        + simpl. eapply preord_exp_monotonic.
          eapply IHe1.
          eassumption. eassumption. eassumption.
          admit.
          eassumption.
          admit.
          rewrite extend_extend_lst_commut. 
          eapply preord_env_P_inj_set_alt.
          rewrite Setminus_Union_distr at 1. rewrite Setminus_Same_set_Empty_set.
          rewrite Setminus_Disjoint. normalize_sets.
          (* from Henv -- how to show? *) admit.
          admit.
          rewrite preord_val_eq. unfold preord_val'.
          { intros vs1 vs2 j tg xs1 e5 rho1' Hlen_eq Hfind Hset.
            simpl in Hfind. simpl.
            rewrite peq_true in *. 
            inv Hfind.
            pose proof (set_lists_length2) as Hset2.
            set(tg := kon_tag).
            edestruct Hset2 with (rho := (M.set v0
                                                (Vfun rho1
                                                      (Fcons v0 tg [v] e5 Fnil) v0)
                                                rho1))
                                 (xs1 := [v]) (vs1 := vs1)
                                 (xs2 := [v1]) (vs2 := vs2);
              clear Hset2.
            simpl. reflexivity.
            eassumption.
            simpl in Hset. destruct vs1. inv Hset.
            destruct vs1. simpl. symmetry. eassumption. 
            inv Hset.
            eexists. eexists. eexists. split.
            reflexivity. split.
            symmetry. eassumption.
            intros Hlt2 Hall.
            eapply preord_exp_post_monotonic. eapply Hprops.
            eapply preord_exp_monotonic. eapply IHe2. 
            eassumption. eassumption.
            admit. admit.
            simpl. f_equal. eassumption.
            admit.
            simpl. admit.
            lia. }
          admit. admit. admit.
          eassumption. lia. 
    Abort.

    Lemma cps_cvt_val_diff_symgen :
      forall v v' v'' k next1 next2 next3 next4,
        cps_cvt_val v next1 cnstrs = Some (v', next2) ->
        cps_cvt_val v next3 cnstrs = Some (v'', next4) ->
        preord_val cenv PG k v' v''.
    Proof.
      intros v. 
      induction v using value_ind';
        intros v' v'' k next1 next2 next3 next4 Hv1 Hv2;
        rewrite cps_cvt_val_eq in *.
      - simpl in *.
        destruct (cps_cvt_env vs next1 cnstrs) eqn:Henv1; inv Hv1.
        destruct p eqn:Hp. inversion H1; clear H1.
        destruct (cps_cvt_env vs next3 cnstrs) eqn:Henv2; inv Hv2.
        destruct p0 eqn:Hp0. inversion H1; clear H1.
        eapply preord_val_eq. simpl. 
        split.
        reflexivity.
        { subst. generalize dependent next1.
          generalize dependent next2.
          generalize dependent next3.
          generalize dependent next4.
          generalize dependent l0. 
          induction l; intros l0 next next3 Henv2 next2 next1 Henv1.
          - destruct vs eqn: Hvs. inv Henv2. econstructor.
            inv Henv1.
            destruct (cps_cvt_val v next1 cnstrs) eqn:Hv; inv H1.
            destruct p eqn: Hp.
            match type of H2 with match ?a with _ => _ end _ = _ =>
                                  destruct a eqn: Henv end; inv Henv.
            destruct p0 eqn: Hp0. inv H2. discriminate. 
          - destruct vs eqn: Hvs. inv Henv1.
            destruct l0. inv Henv2.
            destruct (cps_cvt_val v next3 cnstrs) eqn:Hval; inv H1.
            destruct p eqn:Hp. destruct (cps_cvt_env l1 s cnstrs) eqn:Hl1; inv H2.
            destruct p0 eqn:Hp0. inv H1. 
            inv Henv1. destruct (cps_cvt_val v next1 cnstrs) eqn:Hval1; inv H1.
            destruct p eqn:Hp.
            destruct (cps_cvt_env l1 s cnstrs) eqn:Hl1; inv H2.
            destruct p0 eqn:Hp0.
            inv Henv2.
            destruct (cps_cvt_val v next3 cnstrs) eqn:Hval2; inv H2.
            destruct p eqn:Hp.
            destruct (cps_cvt_env l1 s1 cnstrs) eqn:Henv2; inv H3.
            destruct p0 eqn:Hp0.
            simpl. inv H.
            inv H1. inv H2. 
            admit. }
      - simpl in *. inv Hv1. inv Hv2.
        eapply preord_val_refl; admit.
      - simpl in *.
        destruct (cps_cvt_env vs next1 cnstrs) eqn:Henv1; inv Hv1.
        destruct p eqn:Hp.
        destruct (gensym_n s (rho_names vs)) eqn:Hgen_n.
        destruct (set_lists l0 l (M.empty cps.val)) eqn:Hset. 2: { inv H1. } 
        unfold gensym in H1. destruct s0 eqn:Hs0.
        destruct p0 eqn:Hp0.
        match type of H1 with match ?a with _ => _ end _ = _ =>
                              destruct a eqn:Hcps_cvt end; inv H1.
        destruct p1 eqn:Hp1.
        destruct (cps_cvt_env vs next3 cnstrs) eqn:Henv2; inv Hv2.
        destruct p eqn:Hp.
        destruct (gensym_n s1 (rho_names vs)) eqn:Hgen_n2.
        destruct (set_lists l2 l1 (M.empty cps.val)) eqn:Hset2. 2: {inv H1. }
        unfold gensym in H1. destruct s2 eqn:Hs2.
        destruct p0 eqn:Hp0.
        match type of H1 with match ?a with _ => _ end _ = _ =>
                              destruct a eqn:Hcps_cvt2 end; inv H1.
        destruct p1 eqn:Hp1.
        inv H2. inv H3.
        eapply preord_val_eq.
        simpl. intros.
        destruct (M.elt_eq (Pos.succ (Pos.succ v)) (Pos.succ (Pos.succ v))) eqn:Heq;
          inv H1. 
        repeat eexists.
        + destruct (M.elt_eq (Pos.succ (Pos.succ v0)) (Pos.succ (Pos.succ v0))) eqn:Heq2.
          reflexivity.
          congruence.
        + simpl. destruct vs2 eqn:Hvs2. destruct vs1 eqn:Hvs1.
          simpl in H2. inv H2.
          inv H0.
          destruct vs1 eqn:Hvs1.
          simpl in H2. inv H2.
          simpl in H2. admit.
        + admit.
      - admit.
    Admitted.    

    Lemma cps_cvt_env_and_val :
      forall rho rho' next next1,
        cps_cvt_env rho next cnstrs = Some (rho', next1) ->
        forall next2 next3 v'' k,
          Forall2 (fun v v' => cps_cvt_val v next2 cnstrs = Some (v'', next3) ->
                               preord_val cenv PG k v' v'') rho rho'.
    Proof.
      intros rho rho' next next1 Henv next2 next3 v'' k.
      generalize dependent rho'.
      generalize dependent next.
      induction rho; intros next rho' Henv.
      - inv Henv. econstructor.
      - destruct rho' eqn:Hrho.
        + inv Henv. destruct (cps_cvt_val a next cnstrs) in H0.
          destruct p in H0. destruct (cps_cvt_env rho s cnstrs) in H0.
          destruct p.
          inv H0.
          inv H0.
          inv H0.
        + inv Henv. 
          destruct (cps_cvt_val a next cnstrs) eqn:Hval.
          destruct p eqn:Hp. destruct (cps_cvt_env rho s cnstrs) eqn:Hcpsenv.
          destruct p0 eqn:Hp0. econstructor.
          * intros Hval2. inv H0.
            (* lemma needed *) admit.
          * inv H0. eapply IHrho. eapply Hcpsenv. 
          * inv H0.
          * inv H0. 
    Admitted.

    Lemma cps_val_rel_is_env_rel' :
      forall vs,
        Forall
          (fun v : value =>
             forall (v' : cps.val) (next1 next2 : symgen),
               cps_cvt_val v next1 cnstrs = Some (v', next2) -> cps_val_rel' v v') vs ->
        exists vs',
          (fix cps_env_rel' (rho : list value) (vs0 : list cps.val) {struct rho} : Prop :=
             match rho with
             | [] => match vs0 with
                     | [] => True
                     | _ :: _ => False
                     end
             | v2 :: rho0 =>
               match vs0 with
               | [] => False
               | v3 :: vs1 =>
                 (forall (v'' : cps.val) (k : nat),
                     cps_val_rel' v2 v'' -> preord_val cenv PG k v'' v3) /\
                 cps_env_rel' rho0 vs1
               end
             end) vs vs'.
    Proof.
      induction vs; intros Hall.
      - exists []. reflexivity.
      - inv Hall. eapply IHvs in H2.
        edestruct H2.
        eexists.
    Abort.

    Lemma cps_val_rel_is_env_rel :
      forall vs l next1 next2,
        Forall
          (fun v : value =>
             forall (v' : cps.val) (next1 next2 : symgen),
               cps_cvt_val v next1 cnstrs = Some (v', next2) -> cps_val_rel' v v') vs ->
        cps_cvt_env vs next1 cnstrs = Some (l, next2) ->
        cps_env_rel vs l.
    Proof. 
      induction vs; intros l next1 next2 Hall Henv.
      - simpl in Henv. inv Henv. econstructor.
      - inv Hall.
        simpl in Henv.
        destruct (cps_cvt_val a next1 cnstrs) eqn:Hcvt_val. 2: { inv Henv. }
        destruct p eqn:Hp.
        destruct (cps_cvt_env vs s cnstrs) eqn:Hcvt_env. 2: { inv Henv. } 
        destruct p0 eqn:Hp0.
        inv Henv. simpl. split.
        + intros. 
          admit.
    Admitted. 


    Lemma cps_cvt_val_impl_rel :
      forall v v' next1 next2,
        cps_cvt_val v next1 cnstrs = Some (v', next2) ->
        cps_val_rel' v v'.
    Proof. 
      intros v.
      induction v using value_ind'; intros v' next1 next2 Hval;
        rewrite cps_cvt_val_eq in Hval.
      - simpl in Hval.
        destruct (cps_cvt_env vs next1 cnstrs) eqn:Henv. 2: { inv Hval. } 
        destruct p eqn:Hp.
        inv Hval.
        simpl. split.
        reflexivity.    
        generalize dependent l.
        generalize dependent next1. generalize dependent next2. 
        induction vs; intros next2 next1 l Henv. 
        + simpl in Henv. inv Henv. reflexivity.
        + simpl in Henv.
          destruct (cps_cvt_val a next1 cnstrs) eqn:Hcvt_val. 2: { inv Henv. } 
          destruct p eqn:Hp.
          destruct (cps_cvt_env vs s cnstrs) eqn:Hcvt_env. 2: { inv Henv. }
          destruct p0 eqn:Hp0.
          inv Henv. inv H. split.
          * eapply H2. eapply Hcvt_val.
          * eapply IHvs. eassumption. eapply Hcvt_env.
      - simpl in *. inv Hval. reflexivity.
      - simpl in Hval.
        destruct (cps_cvt_env vs next1 cnstrs) eqn:Hcvt_env. 2: { inv Hval. }
        destruct p eqn:Hp.
        destruct (gensym_n s (rho_names vs)) eqn:Hgen_vars.
        destruct (set_lists l0 l (M.empty cps.val)) eqn:Hset. 2: { inv Hval. }
        destruct (gensym s0 (nNamed "k_lam")) eqn:Hgen_k.
        destruct (gensym s1 (nNamed "x_lam")) eqn:Hgen_x.
        destruct (gensym s2 na) eqn:Hgen_f.
        destruct (cps_cvt e (v0 :: l0) v s3 cnstrs) eqn:Hcvt_e. 2: { inv Hval. }
        destruct p0 eqn:Hp0.
        inv Hval.
        simpl.
    Abort.        
    
    Lemma cps_val_rel_preord :
      forall rho rho' next1 next2 v n k,        
        cps_env_rel rho rho' ->
        cps_cvt_val (List.nth n rho Prf_v) next1 cnstrs = Some (v, next2) ->
        preord_val cenv PG k v (List.nth n rho' (Vint 0)).
    Proof.
      intros rho.
      induction rho; intros rho' next1 next2 v n k Hrel Hval.
      - simpl in *.
        destruct rho' eqn:Hrho'. 2: { destruct Hrel. }
        destruct n eqn:Hn; admit.
      - simpl in *.
        destruct rho' eqn:Hrho'. destruct Hrel.
        destruct Hrel.
        destruct n eqn:Hn.
        + simpl. eapply H.
          simpl in Hval.
          admit.
        +
    Abort.

    Lemma env_obs_rel_preord :
      forall rho rho' n v1 v2 k,
        env_obs_rel rho rho' ->
        obs_rel' (List.nth n rho Prf_v) v1 ->
        List.nth n rho' (Vint 0) = v2 ->
        preord_val cenv PG k v1 v2.
    Proof.
      induction rho; intros rho' n v1 v2 k Henv Hrel Hv2.
      - simpl in Henv. destruct rho'.
        admit.
        destruct Henv.
      - simpl in Henv. destruct rho' eqn:Hrho'.
        destruct Henv.
        destruct Henv.
        simpl in Hrel. destruct n eqn:Hn.
        + simpl in Hv2. rewrite <- Hv2.
          eapply H. eassumption.
        + simpl in Hv2. eapply IHrho; try eassumption.
    Admitted.    

    (* Lemma cps_val_rel_preord_2 : *)
    (*   forall rho rho' n k , *)
    (*     cps_env_rel rho rho' -> *)
    (*     cps_val_rel (List.nth n rho Prf_v) (List.nth n rho' (Vint 0)) -> *)
    (*     preord_val cenv PG k (List.nth n rho Prf_v) (List.nth n rho' (Vint 0)).  *)


    Definition cps_cvt_correct_e c :=
      forall e e' rho rho' rho_m v v' x k vk vars
             next1 next2 next3,
        eval_env rho e v ->
        ~(x = k) ->
        (lt_symgen k next1) /\ (lt_symgen x next1) ->
        (* (lt_symgen x next4) /\ (lt_symgen k next4) -> *)
        cps_env_rel rho rho' -> 
        gensym_n_nAnon next1 (List.length rho') = (vars, next2) ->
        set_lists vars rho' (M.empty cps.val) = Some rho_m ->
        cps_cvt e vars k next2 cnstrs = Some (e', next3) ->
        (* cps_cvt_val v next4 cnstrs = Some (v', next5) -> *)
        obs_rel' v v' ->
        preord_exp cenv P1 PG c
                   ((Eapp k kon_tag (x::nil)), (M.set x v' (M.set k vk (M.empty cps.val))))
                   (e', (M.set k vk rho_m)).

    Definition cps_cvt_correct_es c :=
      forall es es' rho rho' rho_m vs vs' x k vk vars 
             next1 next2 next3 next4 next5,
        Forall2 (fun e v => eval_env rho e v) (exps_to_list es) vs ->
        ~(x = k) ->
        (lt_symgen x next1) /\ (lt_symgen x next1) /\
        (lt_symgen x next4) /\ (lt_symgen k next4) ->
        cps_env_rel rho rho' ->
        gensym_n_nAnon next1 (List.length rho') = (vars, next2) ->
        set_lists vars rho' (M.empty cps.val) = Some rho_m ->
        cps_cvt_exps' es vars k next2 cnstrs = Some (es', next3) ->
        Forall2 (fun v v' => cps_cvt_val v next4 cnstrs = Some (v', next5)) vs vs' ->
        Forall2
          (fun e' v' =>
             preord_exp cenv P1 PG c
                        ((Eapp k kon_tag (x::nil)),
                         (M.set x v' (M.set k vk (M.empty cps.val))))
                        (e', (M.set k vk rho_m)))
          es' vs'.

    Definition cps_cvt_correct_efnlst c :=
      forall efns efns' rho rho' rho_m vfns vfns' x k vk vars 
             next1 next2 next3 next4 next5,
        Forall2 (fun p v => let (na, e) := p : (name * expression.exp) in
                            eval_env rho e v) (efnlst_as_list efns) vfns ->
        ~(x = k) ->
        (lt_symgen x next1) /\ (lt_symgen x next1) /\
        (lt_symgen x next4) /\ (lt_symgen k next4) ->
        cps_env_rel rho rho' ->
        gensym_n_nAnon next1 (List.length rho') = (vars, next2) ->
        set_lists vars rho' (M.empty cps.val) = Some rho_m ->
        cps_cvt_efnlst' efns vars k next2 cnstrs = Some (efns', next3) ->
        Forall2 (fun v v' => cps_cvt_val v next4 cnstrs = Some (v', next5)) vfns vfns' ->
        Forall2
          (fun e' v' =>
             preord_exp cenv P1 PG c
                        (e', (M.set k vk rho_m))
                        ((Eapp k kon_tag (x::nil)),
                         (M.set x v' (M.set k vk (M.empty cps.val)))))
          efns' vfns'.


    Definition cps_cvt_correct_branches c :=
      forall bs bs' rho rho' rho_m vs vs' x k vk vars 
             next1 next2 next3 next4 next5,
        Forall2 (fun p v => let '(dc, (n, l), e) := p in
                            eval_env rho e v) (branches_as_list bs) vs ->
        ~(x = k) ->
        (lt_symgen x next1) /\ (lt_symgen x next1) /\
        (lt_symgen x next4) /\ (lt_symgen k next4) ->
        cps_env_rel rho rho' ->
        gensym_n_nAnon next1 (List.length rho') = (vars, next2) ->
        set_lists vars rho' (M.empty cps.val) = Some rho_m ->
        cps_cvt_branches' bs vars k next2 cnstrs = Some (bs', next3) ->
        Forall2 (fun v v' => cps_cvt_val v next4 cnstrs = Some (v', next5)) vs vs' ->
        Forall2
          (fun e' v' =>
             preord_exp cenv P1 PG c
                        (e', (M.set k vk rho_m))
                        ((Eapp k kon_tag (x::nil)),
                         (M.set x v' (M.set k vk (M.empty cps.val)))))
          bs' vs'.

    
    Lemma cps_cvt_correct:
      forall k,
        (cps_cvt_correct_e k) /\
        (cps_cvt_correct_es k) /\
        (cps_cvt_correct_efnlst k) /\
        (cps_cvt_correct_branches k).
    Proof.
      intros k. induction k as [k IHk] using lt_wf_rec1. eapply my_exp_ind.
      - intros n e' rho rho' rho_m v v' x k0 vk vars 
               next1 next2 next3 H H0 H1 H2 H3 H4 H5 H6.
        inv H. simpl in H5.
        destruct (nth_error vars (N.to_nat n)) eqn:Heqn. 2:{ congruence. }
        inv H5.
        eapply preord_exp_app_compat.
        + eapply HPost_app. eapply Hprops. 
        + eapply HPost_OOT. eapply Hprops. 
        + unfold preord_var_env.
          intros v1 Hgetv1. rewrite M.gso in Hgetv1.
          -- rewrite M.gss in Hgetv1. inv Hgetv1.
             eexists. rewrite M.gss. split.
             reflexivity.
             eapply preord_val_refl. eapply HpropsG. 
          -- unfold not in *.
             intros Hfalse. symmetry in Hfalse.
             apply H0 in Hfalse. destruct Hfalse. 
        + econstructor.
          -- unfold preord_var_env.
             intros v1 Hgetv1. rewrite M.gss in Hgetv1.
             inv Hgetv1. eexists. admit.
          -- econstructor.
      - intros na e IH e' rho rho' rho_m v v' x k0 vk vars
               next1 next2 next3 Heval Hneq Hlt Hrel Hgen Hset Hcvt Hcvt_val.
        inv Heval. simpl in Hcvt. 
        destruct (gensym next2 (nNamed "k_lam")) eqn: Hgen_k.
        destruct (gensym s (nNamed "x_lam")) eqn: Hgen_x.
        destruct (gensym s0 na) eqn:Hgen_f.
        destruct (cps_cvt e (v0 :: vars) v s1 cnstrs) eqn:Hcvt_e.
        destruct p eqn:Hp. inv Hcvt.
        2 : { inv Hcvt. }
        (* Zoe: commneting out because some stuff have changed *) 
        (* 
    rewrite cps_cvt_val_eq in Hcvt_val. simpl in Hcvt_val.
    destruct (cps_cvt_env rho next4 cnstrs) eqn:Hcps_env.
    2: { inv Hcvt_val. } 
    destruct p eqn:Hp.
    destruct (gensym_n s2 (rho_names rho)) eqn:Hgen_vars.
    destruct (set_lists l0 l (M.empty cps.val)) eqn:Hset2.
    2: { inv Hcvt_val. }
    destruct (gensym s3 (nNamed "k_lam")) eqn:Hgen_k2.
    destruct (gensym s4 (nNamed "x_lam")) eqn:Hgen_x2.
    destruct (gensym s5 na) eqn:Hgen_f2.
    destruct (cps_cvt e (v3 :: l0) v2 s6 cnstrs) eqn:Hcvt_e_2.
    destruct p0 eqn:Hp0. inv Hcvt_val.
    2: { inv Hcvt_val. } *)
        (* 
       RHS:
       (Efun v1 [v0; v] e0 (Eapp k0 [v1]), [k0 -> vk]rho_m) ==>
       
       (Eapp k0 [v1], [v1 -> Vfun rho_m (Fun v1 [v0; v] e0) v1, k0 -> vk]rho_m

       Then apply preord_exp_app_compat

       Okay to use v1 in (Eapp k0 [v1], or should we use a different variable?

         *)
        
        admit.
      - admit.
      - admit.
      - admit.
      - intros na e IH1 e0 IH2 e' rho rho' rho_m v v' x k0 vk vars
               next1 next2 next3 Heval Hneq Hlt Hrel Hgen Hset Hcvt Hcvt_val.
        simpl in Hcvt.
        destruct (gensym next2 na) eqn: Hgen_x.
        destruct (gensym s (nNamed "k")) eqn: Hgen_k.
        destruct (cps_cvt e0 (v0 :: vars) k0 s0 cnstrs) eqn: Hcvt_e0.
        2 : { congruence. } 
        destruct p eqn: Hp.
        destruct (cps_cvt e vars v1 s1 cnstrs) eqn: Hcvt_e.
        2 : { congruence. } 
        destruct p0 eqn: Hp0.
        inv Hcvt.
        inv Heval.
        (* Zoe: commneting out because some stuff have changed *) 
    (* 

    assert (Hex: exists v2' next6,
                 cps_cvt_val v2 next5 cnstrs = Some (v2', next6)) by admit.
    destruct Hex as (v2' & next6 & Hval). 
    eapply preord_exp_post_monotonic. eapply Hincl.
    eapply preord_exp_trans.
    eapply HpropsG.
    admit. admit. admit.
    { eapply IH2 with (rho' := (v2' :: rho')) (rho_m := map_util.M.set v0 v2' rho_m).
      7 : { eassumption. } 
      - eassumption.
      - eassumption.
      - eassumption.
      - admit.
      - admit. 
      - simpl. rewrite Hset. reflexivity. 
      - eassumption. }
    { intros m. clear IH2.
      
      assert (Hpre :
                preord_exp' cenv (preord_val cenv) P1 PG m
                            (e1, M.set k0 vk (map_util.M.set v0 v2' rho_m))
                            (e2, (M.set v1 (Vfun (M.set k0 vk rho_m)
                                                 (Fcons v1 kon_tag [v0] e1 Fnil) v1)
                                        (M.set k0 vk rho_m))) ->
                preord_exp' cenv (preord_val cenv) P1 PG m
                            (e1, M.set k0 vk (map_util.M.set v0 v2' rho_m))
                            (Efun (Fcons v1 kon_tag [v0] e1 Fnil) e2,
                             M.set k0 vk rho_m)) by admit. 
      eapply Hpre. clear Hpre. 

      specialize IH1 with (k0 := v1) (vk := (Vfun (M.set k0 vk rho_m)
                                                (Fcons v1 kon_tag [v0] e1 Fnil) v1))
                        (v' := v2') (e' := e2).

      (* Adding mapping for v1 in the environment *)
      assert (Hpre:
                preord_exp' cenv (preord_val cenv) P1 PG m
                            (e1, M.set v1 (Vfun (M.set k0 vk rho_m)
                                                (Fcons v1 kon_tag [v0] e1 Fnil) v1)
                                       (M.set k0 vk (map_util.M.set v0 v2' rho_m)))
                            (e2, M.set v1 (Vfun (M.set k0 vk rho_m)
                                                (Fcons v1 kon_tag [v0] e1 Fnil) v1)
                                       (M.set k0 vk rho_m)) ->
                preord_exp' cenv (preord_val cenv) P1 PG m
                            (e1, M.set k0 vk (map_util.M.set v0 v2' rho_m))
                            (e2, M.set v1 (Vfun (M.set k0 vk rho_m)
                                                (Fcons v1 kon_tag [v0] e1 Fnil) v1)
                                       (M.set k0 vk rho_m))) by admit.
      eapply Hpre. clear Hpre.

      (* Reduction required to apply IH1, x mapped to v2' in environment *)
      assert (Hpre:
                 preord_exp' cenv (preord_val cenv) P1 PG m
                             (Eapp v1 kon_tag [x],
                              M.set x v2'
                                    (M.set v1
                                           (Vfun (M.set k0 vk rho_m)
                                                 (Fcons v1 kon_tag [v0] e1 Fnil) v1)
                                           (M.empty cps.val)))
                             (e2, M.set v1 (Vfun (M.set k0 vk rho_m)
                                                 (Fcons v1 kon_tag [v0] e1 Fnil) v1)
                                        (M.set k0 vk rho_m)) ->
                 preord_exp' cenv (preord_val cenv) P1 PG m
                             (e1, M.set v1 (Vfun (M.set k0 vk rho_m)
                                                 (Fcons v1 kon_tag [v0] e1 Fnil) v1)
                                        (M.set k0 vk (map_util.M.set v0 v2' rho_m)))
                             (e2, M.set v1 (Vfun (M.set k0 vk rho_m)
                                                 (Fcons v1 kon_tag [v0] e1 Fnil) v1)
                                        (M.set k0 vk rho_m))) by admit.
      eapply Hpre. clear Hpre. 
      eapply preord_exp_monotonic.
      eapply IH1.
      - eassumption.
      - (* x < next1 < next2 < s < v1 *) admit.
      - admit.
      - eassumption.
      - eassumption.
      - (* use some other rho? *) admit.
      - admit.
      - eassumption.
      - (* ? *) *)
    Abort. 

    
    (* cenv needs to related to dcon? *)
    Lemma cps_cvt_correct':
      forall e m rho rho' rhomap x k vk e' v v' v'' v''' penv cenv
             vars cnstrs next1 next2 next3 next4 next5,
        eval_env rho e v ->
        cps_cvt_env rho next1 cnstrs = Some (rho', next2) ->
        gensym_n_nAnon next2 (List.length rho') = (vars, next3) ->
        set_lists vars rho' (M.empty cps.val) = Some rhomap ->
        cps_cvt e vars k next3 cnstrs = Some (e', next4) ->
        cps_cvt_val v next1 cnstrs = Some (v', next5) ->
        bstep_e penv cenv (M.set x v' (M.set k vk (M.empty cps.val))) (Eapp k kon_tag (x::nil)) v'' m ->
        exists n, bstep_e penv cenv (M.set k vk rhomap) e' v''' n /\
                  exists f, (Alpha_conv_val v'' v''' f).
    Proof.
      intros e. 
      eapply my_exp_ind.
      
    Abort. 
    

    Inductive bigStepResult {Term Value : Type} : Type :=
      Result : Value -> bigStepResult 
    | OutOfTime : Term -> bigStepResult 
    | Error : string -> option Term -> bigStepResult.

    (* Definition L6_evaln_fun n p : @bigStepResult (env * exp) cps.val := *)
    (*   let '((penv, cenv, nenv, fenv), (rho, e)) := p *)
    (*   : ((prims * ctor_env * name_env * fun_env) * (env * cps.exp)) in *)
    (*   match bstep_f penv cenv rho e n with *)
    (*   | exceptionMonad.Exc s => Error s None *)
    (*   | Ret (inl t) => OutOfTime t *)
    (*   | Ret (inr v) => Result v *)
    (*   end. *)

    (* Definition print_BigStepResult_L6 p n := *)
    (*   let '((penv, cenv, nenv, fenv), (rho, e)) := *)
    (*       p : ((M.t (list cps.val -> option cps.val) * ctor_env * name_env * fun_env) * *)
    (*            (M.t cps.val * cps.exp)) in *)
    (*   L7.L6_to_Clight.print ( *)
    (*       match (bstep_f penv cenv rho e n) with *)
    (*       | exceptionMonad.Exc s => s *)
    (*       | Ret (inl t) => *)
    (*         let (rho', e') := t : (env * cps.exp) in *)
    (*         "Out of time:" ++ (show_cenv cenv) ++ (show_env nenv cenv false rho') ++ *)
    (*                        (show_exp nenv cenv false e') *)
    (*       | Ret (inr v) => show_val nenv cenv false v *)
    (*       end). *)

    (* Definition print_BigStepResult_L6Val p := *)
    (*   let '((penv, cenv, nenv, fenv), (rho, v)) := *)
    (*       p : ((M.t (list cps.val -> option cps.val) * ctor_env * name_env * fun_env) * *)
    (*            (M.t cps.val * cps.val)) in *)
    (*   L7.L6_to_Clight.print ((show_cenv cenv) ++ (show_env nenv cenv false rho) ++ *)
    (*                                           (show_val nenv cenv false v)). *)

End Post.
(*
Quote Recursively Definition test1_program :=
  ((fun x =>
      match x with
      | nil => 3%nat
      | cons h x' => h
      end) ((1%nat)::nil)).

Definition id_f (x : nat) := x.

Definition match_test (l : list nat) :=
  match l with
  | nil => false
  | cons el l' => true
  end.

Quote Recursively Definition test2_program := (match_test (1%nat::nil)).

Definition add_test := Nat.add 1%nat 0%nat.

Fixpoint id_nat (n : nat) :=
  match n with
  | O => O
  | S n' => S (id_nat n')
  end.

Definition plus_1 (l : list nat) :=
  let fix plus_1_aux l k :=
    match l with
    | nil => k nil
    | cons n l' => plus_1_aux l' (fun s => k ((Nat.add n 1%nat)::s))
    end
  in
  plus_1_aux l (fun s => s).

Definition hd_test := (@List.hd nat 0%nat (1%nat::nil)).

Definition let_simple :=
  let x := 3%nat in Nat.add x 0%nat.

Quote Recursively Definition test3_program := hd_test.

Quote Recursively Definition test4_program :=
  (List.hd 0%nat (plus_1 (0%nat::1%nat::nil))).

Quote Recursively Definition test5_program := (List.hd_error (false::nil)).


(* Quote Recursively Definition test3_program := *)


Definition test_eval :=
  Eval native_compute in (translateTo (cTerm certiL4) test5_program).

Print test_eval.

Definition test :=
  match test_eval with
  | exceptionMonad.Ret p => p
  | exceptionMonad.Exc s => (nil, expression.Prf_e)
  end.

Definition test_result :=
  match (convert_top test) with
  | Some (cenv, nenv, _, ctg, itg, e) =>
    let pr := cps.M.empty (list val -> option val) in
    let fenv := cps.M.empty fTyInfo in
    let env := cps.M.empty val in
    print_BigStepResult_L6 ((pr, cenv, nenv, fenv), (env, e)) 250%nat
  | None =>
    L7.L6_to_Clight.print ("Failed during comp_L6")
  end.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOcamlZInt.
Require Import ExtrOcamlNatInt.

Extract Inductive Decimal.int =>
unit [ "(fun _ -> ())" "(fun _ -> ())" ] "(fun _ _ _ -> assert false)".

Extract Constant L6_to_Clight.print =>
"(fun s-> print_string (String.concat """" (List.map (String.make 1) s)))".


Extract Constant   varImplDummyPair.varClassNVar =>
" (fun f (p:int*bool) -> varClass0 (f (fst p)))".

Extraction "test1.ml" test_result.

*) *) 
End CPS.
