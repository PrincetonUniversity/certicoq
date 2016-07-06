Require Import cps cps_util set_util relations hoisting identifiers ctx
        Ensembles_util List_util alpha_conv.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Lists.List Coq.MSets.MSets Coq.MSets.MSetRBT Coq.Numbers.BinNums
        Coq.NArith.BinNat Coq.PArith.BinPos Coq.Sets.Ensembles.
Require Import ExtLib.Structures.Monads ExtLib.Data.Monads.StateMonad.
Import ListNotations Nnat MonadNotation.
Require Maps.

Open Scope ctx_scope.

(** * Closure conversion as a relation  *)

Inductive project_var :
  Ensemble var -> (* Variables in the current scope *)
  Ensemble var -> (* Names of the functions in the current function block *)
  var -> (* The environment argument *)
  list var -> (* The environment *)
  Ensemble var -> (* The free set *)
  var -> (* Before projection *)
  var -> (* After projection *)
  exp_ctx -> (* Context that will perform the projection *)
  Ensemble var -> (* The new free set *)
  Prop :=
| Var_in_Scope :
    forall Scope Funs Γ FVs S x,
      In _ Scope x ->
      project_var Scope Funs Γ FVs S x x Hole_c S
| Var_in_Funs :
    forall Scope Funs Γ FVs S x y t tau,
      ~ In _ Scope x ->
      In _ Funs x ->
      In _ S y ->
      project_var Scope Funs Γ FVs S x y
                  (Econstr_c y t tau [x; Γ] Hole_c) (Setminus _ S (Singleton _ y))
| Var_in_FVs :
    forall Scope Funs Γ FVs S x y N tau,
      ~ In _ Scope x ->
      ~ In _ Funs x -> 
      nthN FVs N = Some x ->
      In _ S y ->
      project_var Scope Funs Γ FVs S x y
                  (Eproj_c y tau N Γ Hole_c) (Setminus _ S (Singleton _ y)).

Inductive project_vars :
  Ensemble var -> (* Variables in the current scope *)
  Ensemble var -> (* Names of the functions in the current function block *)
  var -> (* The environment argument *)
  list var -> (* The free variables *)
  Ensemble var -> (* The free set *)
  list var -> (* Before projection *)
  list var -> (* After projection *)
  exp_ctx -> (* Context that will perform the projection *)
  Ensemble var -> (* The new free set *)
  Prop :=
| VarsNil :
    forall Scope Funs Γ FVs S,
      project_vars Scope Funs Γ FVs S [] [] Hole_c S
| VarsCons :
    forall Scope Funs Γ FVs y y' ys ys' C1 C2 S1 S2 S3,
      project_var Scope Funs Γ FVs S1 y y' C1 S2 ->
      project_vars Scope Funs Γ FVs S2 ys ys' C2 S3 ->
      project_vars Scope Funs Γ FVs S1 (y :: ys) (y' :: ys') (comp_ctx_f C1 C2) S3.

Inductive make_closures : fundefs -> var -> exp_ctx -> Prop :=
| closures_Fnil :
    forall Γ,
      make_closures Fnil Γ Hole_c
| closures_Fcons :
    forall f xs tau e B Γ C tau' t',
      make_closures B Γ C ->
      make_closures (Fcons f tau xs e B) Γ
                    (Econstr_c f tau' t' [f; Γ] C).

Inductive Closure_conversion :
  Ensemble var -> (* Variables in the current scope *)
  Ensemble var -> (* Names of the functions in the current function block *)
  var -> (* The environment argument *)
  list var -> (* The free variables - needs to be ordered *)
  exp -> (* Before cc *)
  exp -> (* After cc *)
  Prop :=
| CC_Econstr :
    forall Scope Funs Γ FVs S' S x ys ys' C tau tau' t e e',
      (* Variables for projected vars should not shadow the variables in
         scope, i.e. Scope U FV U { Γ } *)
      Disjoint _ S (Union _ Scope
                          (Union _ Funs
                                 (Union _ (FromList FVs) (Singleton _ Γ)))) ->
      project_vars Scope Funs Γ FVs S ys ys' C S' ->
      (* We do not care about ys'. Should never be accessed again so do not
         add them aτ the current scope *)
      Closure_conversion (Union _ (Singleton _ x) Scope) Funs Γ FVs e e' ->
      Closure_conversion Scope Funs Γ FVs (Econstr x tau t ys e)
                         (C |[ Econstr x tau' t ys' e' ]|)
| CC_Ecase :
    forall Scope Funs Γ FVs x x' C S S' pats pats',
      Disjoint _ S (Union _ Scope
                          (Union _ Funs
                                 (Union _ (FromList FVs) (Singleton _ Γ)))) ->
      project_var Scope Funs Γ FVs S x x' C S' ->
      Forall2 (fun (pat pat' : tag * exp) =>
                 (fst pat) = (fst pat') /\
                 Closure_conversion Scope Funs Γ FVs (snd pat) (snd pat'))
              pats pats' ->
      Closure_conversion Scope Funs Γ FVs (Ecase x pats) (C |[ Ecase x' pats']|)
| CC_Eproj :
    forall Scope Funs Γ FVs S S' x y y' C tau tau' N e e',
      Disjoint _ S (Union _ Scope
                          (Union _ Funs
                                 (Union _ (FromList FVs) (Singleton _ Γ)))) ->
      project_var Scope Funs Γ FVs S y y' C S' ->
      Closure_conversion (Union _ (Singleton _ x) Scope) Funs Γ FVs e e' ->
      Closure_conversion Scope Funs Γ FVs (Eproj x tau N y e)
                         (C |[ Eproj x tau' N y' e' ]|)
| CC_Efun :
    forall Scope Funs Γ Γ' FVs FVs' FVs'' B B' e e' C C' S S' tau t,
      (* The environment contains all the variables that are free in B *)
      Same_set _ (occurs_free_fundefs B) (FromList FVs') ->
      (* Γ' is the variable that will hold the record of the environment *)
      ~ In _ (Union _ (name_in_fundefs B)
                    (Union _ Scope
                           (Union _ Funs
                                  (Union _ (FromList FVs) (Singleton _ Γ))))) Γ' ->
      Closure_conversion_fundefs (name_in_fundefs B) FVs' B B' ->
      Closure_conversion (Union _ (name_in_fundefs B) Scope) Funs Γ FVs e e' ->
      make_closures B Γ' C ->
      Disjoint _ S (Union _ Scope
                          (Union _ Funs
                                 (Union _ (FromList FVs) (Singleton _ Γ)))) ->
      project_vars Scope Funs Γ FVs S FVs' FVs'' C' S' ->
      Closure_conversion Scope Funs Γ FVs (Efun B e)
                         (C' |[ Econstr Γ' tau t FVs'' (Efun B' (C |[ e' ]|)) ]|)
| CC_Eapp :
    forall Scope Funs Γ FVs f f' f'' env' ys ys' C S S' tau tau',
      Disjoint _ S (Union _ Scope
                          (Union _ Funs
                                 (Union _ (FromList FVs) (Singleton _ Γ)))) ->
      (* Project the function name and the actual parameter *)
      project_vars Scope Funs Γ FVs S (f :: ys) (f' :: ys') C S' ->
      (* (* Project the actual parameters *) *)
      (* project_vars Scope Funs Γ FVs S1 ys ys' C2 S2 -> *)
      (* The name of the function pointer and the name of the environment
         should not shadow the variables in the current scope and the
         variables that where used in the projections *)
      In _ S' f'' -> In _ S' env' -> f'' <> env' ->
      Closure_conversion Scope Funs Γ FVs (Eapp f ys)
                         (C |[ Eproj f'' tau 0%N f'
                                     (Eproj env' tau' 1%N f'
                                            (Eapp f'' (env' :: ys'))) ]| )
| CC_Eprim :
    forall Scope Funs Γ FVs S S' x ys ys' C tau tau' f e e',
      Disjoint _ S (Union _ Scope
                          (Union _ Funs
                                 (Union _ (FromList FVs) (Singleton _ Γ)))) ->
      project_vars Scope Funs Γ FVs S ys ys' C S' ->
      Closure_conversion (Union _ (Singleton _ x) Scope) Funs Γ FVs e e' ->
      Closure_conversion Scope Funs Γ FVs (Eprim x tau f ys e)
                         (C |[ Eprim x tau' f ys' e' ]|)
with Closure_conversion_fundefs :
  Ensemble var -> (* The function names in the current block *)
  list var -> (* The environment *)
  fundefs -> (* Before cc *)
  fundefs -> (* After cc *)
  Prop :=
| CC_Fcons :
    forall Funs Γ' FVs f tau tau' ys e e' defs defs',
      (* The environment binding should not shadow the current scope
         (i.e. the names of the mut. rec. functions and the other arguments) *)
      ~ In _ (Union _ Funs (Union _ (FromList ys) (bound_var e))) Γ' ->
      Closure_conversion_fundefs Funs FVs defs defs' ->
      Closure_conversion (FromList ys) Funs Γ' FVs e e' ->
      Closure_conversion_fundefs Funs FVs (Fcons f tau ys e defs )
                                 (Fcons f tau' (Γ' :: ys) e' defs')
| CC_Fnil :
    forall Funs FVs,
      Closure_conversion_fundefs Funs FVs Fnil Fnil.


Definition Closure_conversion_alpha (Scope Funs : Ensemble var) (Γ : var)
           (FVs : list var) sbst
: relation exp  :=
  relations.compose (Closure_conversion Scope Funs Γ FVs) (fun e e' => Alpha_conv e e' sbst).

Definition Closure_conversion_fundefs_alpha (Funs : Ensemble var) (FVs : list var) sbst
: relation fundefs  :=
  relations.compose (Closure_conversion_fundefs Funs FVs) (fun B B' => Alpha_conv_fundefs B B' sbst).


(** * Computational defintion of closure conversion *)

Record FunInfo : Type :=
  mkFunInfo
    { (* free variables of the function definition block *)
      fv_set_def : FVSet;
      (* the names of the functions in the block *)
      rec_names  : FVSet }.

(** Maps function name to [FunInfo] *)
Definition FunInfoMap := Maps.PTree.t FunInfo.

Definition TypeMap := Maps.PTree.t type.

Inductive VarInfo : Type :=
(* A free variable, i.e. a variable outside the scope of the current function.
   The first argument is position of a free variable in the env record and the
   second its type *)
| FVar : N -> type -> VarInfo
(* A function defined in the current block of function definitions. The first
   argument is the new name of the function (code pointer), the second its the
   type of the function and the third the type of the
   closure *)
| MRFun : var -> type -> type -> VarInfo
(* A variable declared in the scope of the current function *)
| BoundVar : type -> VarInfo.

(* Maps variables to [VarInfo] *)
Definition VarInfoMap := Maps.PTree.t VarInfo.

(** The state is the next available free variable and the type dictionary *)
Definition ccstate := state (var * TDict.t).

(** Get a fresh name *)
Definition get_name : ccstate var :=
  p <- get ;;
  let '(n, d) := p in
  put ((n+1)%positive, d) ;;
  ret n.

(** Setter and getter for types *)
Definition set_typeinfo (t : typeinfo) : ccstate type :=
  p <- get ;;
  let '(n, d) := p in
  let (h, d') := TDict.hash t d in
  put (n, d') ;;
  ret h.

Definition get_typeinfo (i : type) : ccstate typeinfo :=
  p <- get ;;
  let '(n, d) := p in
  match TDict.get i d with
    | Some typinfo => ret typinfo
    | None => ret Tunknown (* should not happen *)
  end.

(** Construct the [FunInfo] map *)
Fixpoint exp_info (e : exp) (acc : FunInfoMap) : FunInfoMap :=
  match e with
    | Econstr x tau c ys e =>
      exp_info e acc
    | Ecase x pats =>
      fold_left (fun map te => exp_info (snd te) map) pats acc 
    | Eproj x tau n y e =>
      exp_info e acc
    | Efun defs e =>
      let names := fundefs_names defs in
      let acc' := fundefs_info defs (fundefs_fv defs names) names acc in
      exp_info e acc'
    | Eapp x xs => acc
    | Eprim x tau prim ys e =>
      exp_info e acc
  end
with fundefs_info (defs : fundefs) (fv : FVSet) (names : FVSet)
                  (acc : FunInfoMap) : FunInfoMap :=
       match defs with
         | Fcons f tau ys e defs' =>
           let acc' := Maps.PTree.set f
                                      {| fv_set_def := fv;
                                         rec_names := names |}
                                      acc in
           let acc'' := exp_info e acc' in
           fundefs_info defs' names fv acc'' 
         | Fnil => acc
       end.

Section CC.
  Context (utag : tag) (* Tag for types with unique constructor *)
          (env_tag : tag) (* Tag for the type of environments *)
          (tag_bij : tag -> tag) (* mapping from function tags to closure 
                                    records tags *)
          (unknown_type : type).

  (** Looks up a variable in the map and handles it appropriately *) 
  Definition get_var (x : var) (map : VarInfoMap) (Γ : var)
  : ccstate (var * type * (exp -> exp)) :=
    match Maps.PTree.get x map with
      | Some entry =>
        match entry with
          | FVar pos typ =>
            (* pick a fresh name *)
            y <- get_name ;;
            ret (y, typ, fun e => Eproj y typ pos Γ e)   
          | MRFun code_ptr typ cl_typ =>
            (* get the new name of the function and pack it together with the
               current environment argument to construct the closure *)
            y <- get_name ;;
            ret (y, cl_typ, fun e => Econstr y cl_typ utag [code_ptr; Γ] e)
          | BoundVar typ => ret (x, typ, id)
        end
      | None => ret (x, 1%positive, id) (* should never reach here *)
    end.

  Fixpoint get_vars (xs : list var) (map : VarInfoMap)
           (cl : var) : ccstate (list var * (exp -> exp)) :=
    match xs with
      | [] => ret ([], id)
      | x :: xs =>
        t1 <- get_var x map cl ;;
        let '(y, f) := t1 in
        t2 <- get_vars xs map cl ;; 
        let '(ys, f') := t2 in
        ret (fst y :: ys, fun e => f (f' e))
    end.

  Definition get_vars_with_types (xs : list var) (map : VarInfoMap) (cl : var)
  : ccstate (list (var * type) * (exp -> exp)) :=
    fold_right (fun x t =>
                  t1 <- get_var x map cl ;;
                  let '(y, f) := t1 in
                  t2 <- t ;; 
                  let '(ys, f') := t2 in
                  ret (y :: ys, fun e => (f (f' e)))
               ) (ret ([], id)) xs.

  (** Construct the closure environment and the new variable map *)
  Definition make_env (fv : FVSet) (mapfv_new : VarInfoMap)
             (mapfv_old : VarInfoMap) (Γ_new Γ_old : var)
  : ccstate (type * VarInfoMap * (exp -> exp)) :=
    (* put the free variables in a new map *)
    let (map_new', _) :=
        PS.fold (fun x arg =>
                   let '(map, n) := arg in
                   let typ :=
                       match Maps.PTree.get x mapfv_old with
                         | Some entry  =>
                           match entry with
                             | FVar _ t | BoundVar t
                             | MRFun _ _ t => t
                           end
                         | None => 1%positive (* should not happen *)
                       end
                   in
                   (Maps.PTree.set x (FVar n typ) map, (n + 1)%N))
                fv (mapfv_new, 0%N)
    in
    t1 <- get_vars_with_types (PS.elements fv) mapfv_old Γ_old ;;
    let '(fv', g') :=  t1 in
    env_typ <- set_typeinfo (Tdata [(env_tag, List.map snd fv')]) ;;
    ret (env_typ, map_new',
         fun e => g' (Econstr Γ_new env_typ utag (List.map fst fv') e)).

(* recursive lookup for types -- needs termination proof *)
(* Fixpoint closure_type (fun_typ env_type : type) : ccstate type := *)
(*   ftyp <- get_typeinfo fun_typ ;; *)
(*   match ftyp with *)
(*     | Tfun tag lst => *)
(*       lst' <- mapM (fun f => closure_type f env_type) lst ;; *)
(*       let ptr_inf := Tfun tag (env_type :: lst') in *)
(*       ptr_typ <- set_typeinfo ptr_inf ;;  *)
(*       let clo_inf := Tdata [(tag_bij tag, [ptr_typ; env_type])] in *)
(*       typ <- set_typeinfo clo_inf ;; *)
(*       ret typ *)
(*     | _ => ret fun_typ *)
(*   end. *)
  
  (** Construct closures after a function definition block *)
  Fixpoint make_full_closure (defs : fundefs) (mapfv_new mapfv_old : VarInfoMap)
           (Γ : var) (env_type : type)
  : ccstate (VarInfoMap * VarInfoMap * (exp -> exp)) :=
    match defs with
      | Fcons f typ xs e defs' =>
        t <- make_full_closure defs' mapfv_new mapfv_old Γ env_type ;;
        let '(mapfv_new', mapfv_old', g') := t in
        (* The new name of the function *)
        code_ptr <- get_name ;;
        tinf <- get_typeinfo typ ;;
        p <- match tinf with
               | Tfun tag args =>
                 (* The new type of the code pointer *)
                 (* XXX change args type - This is wrong *)
                 let tinf' := Tfun tag (env_type :: args) in
                 typ' <- set_typeinfo tinf' ;;
                 (* The type of the closure *)
                 let tinf'' := Tdata [(tag_bij tag, [typ'; unknown_type])] in
                 typ'' <- set_typeinfo tinf'' ;;
                  ret (typ', typ'') 
               | _ => ret (1%positive, 1%positive)
             end ;;
        let (typ', typ'') := p in (* (type of code ptr * type of closure) *)
        (* update the new map *)
        let mapfv_new'' :=
            Maps.PTree.set f (MRFun code_ptr typ' typ'') mapfv_new'
        in
        (* update the old map *)
        let mapfv_old'' :=
            Maps.PTree.set f (BoundVar typ'') mapfv_old'
        in
        ret (mapfv_new'', mapfv_old'',
             (fun e => Econstr f typ'' utag [code_ptr; Γ] (g' e)))
      | Fnil => ret (mapfv_new, mapfv_old, id)
    end.

  (** Add some bound variables in the map *)
  Definition add_params args args_typ (mapfv : VarInfoMap) : VarInfoMap :=
    fold_left (fun map p =>
                 let '(var, typ) := p in
                 Maps.PTree.set var (BoundVar typ) map)
              (combine args args_typ) mapfv.
  
  Fixpoint mapM {M : Type -> Type} {A B : Type} `{Monad M} (f : A -> M B)
           (l : list A)  : M (list B) :=
    match l with
      | [] => ret []
      | x :: xs =>
        let sx' := f x in
        x' <- sx';;
        xs' <- mapM f xs ;;
        ret (x' :: xs')
    end.

  Fixpoint sequence {M : Type -> Type} {A : Type} `{Monad M}
           (l : list (M A))  : M (list A) :=
    match l with
      | [] => ret []
      | x :: xs =>
        x' <- x ;;
        xs' <- sequence xs ;;
        ret (x' :: xs')
    end.

  (* Todo : Fix argument type bug *)
  Fixpoint exp_closure_conv (e : exp) (mapfv : VarInfoMap)
           (Γ : var) : ccstate exp := 
    match e with
      | Econstr x typ c ys e' =>
        t1 <- get_vars ys mapfv Γ ;;
        let '(ys', f) := t1 in
        e'' <- exp_closure_conv e' (Maps.PTree.set x (BoundVar typ) mapfv) Γ ;;
        ret (f (Econstr x typ c ys' e''))
      | Ecase x pats =>
        t1 <- get_var x mapfv Γ ;;
        let pats_st := List.map (fun (p : tag * exp) =>
                                  let (t, e) := p in
                                  e' <- exp_closure_conv e mapfv Γ ;;
                                     ret (t, e')) pats in
        pats' <- sequence pats_st ;;
        (* could do [mapM] here but it stops guessing the decreasing arg :( *) 
        (* pats' <- mapM (fun (p : tag * exp) => *)
        (*                 let (t, e) := p in *)
        (*                 let e_st := exp_closure_conv e mapfv Γ in *)
        (*                 e' <-  e_st ;; *)
        (*                 ret (t, e')) pats ;; *)
        let '(x', _, f1) := t1 in           
        ret (f1 (Ecase x' pats'))
      | Eproj x typ n y e' =>
        t1 <- get_var y mapfv
           Γ ;;
        let '(y', _, f) := t1 in
        e'' <- exp_closure_conv e' (Maps.PTree.set x (BoundVar typ) mapfv) Γ ;;
        ret (f (Eproj x typ n y' e''))
      | Efun defs e =>
        let names := fundefs_names defs in
        let fv := fundefs_fv defs names in
        Γ' <- get_name ;;
        t1 <- make_env fv (Maps.PTree.empty VarInfo) mapfv Γ' Γ ;;
        let '(env_type, mapfv_new, g1) := t1 in
        t2 <- make_full_closure defs mapfv_new mapfv Γ' env_type ;;
        let '(mapfv_new', mapfv_old', g2) := t2 in
        e' <- exp_closure_conv e mapfv_old' Γ ;;
        defs' <- fundefs_closure_conv defs mapfv_new' ;;
        ret (g1 (Efun defs' (g2 e')))
      | Eapp f xs =>
        t1 <- get_var f mapfv Γ ;;
        let '(f', typ, g1) := t1 in     
        t2 <- get_vars xs mapfv Γ ;;
        let '(xs', g2) := t2 in
        ptr <- get_name ;;
        Γ <- get_name ;;
        typinf <- get_typeinfo typ;;    
        let ftyp :=
            match typinf with
              | Tdata [(_, (ftyp :: _))] => ftyp
              | _ => 1%positive (* should not happen *) 
            end
        in
        ret (g1 (g2 (Eproj ptr ftyp 0 f'
                           (Eproj Γ unknown_type 1 f'
                                  (Eapp ptr (Γ :: xs'))))))
    | Eprim x typ prim ys e' =>
      t1 <- get_vars ys mapfv Γ ;;
      let '(ys', f) := t1 in
      e'' <- exp_closure_conv e' (Maps.PTree.set x (BoundVar typ) mapfv) Γ ;;
      ret (f (Eprim x typ prim ys' e''))
    end
  with fundefs_closure_conv (defs : fundefs) (mapfv : VarInfoMap)
       : ccstate fundefs  :=
         match defs with
           | Fcons f typ ys e defs' =>
             typinf <- get_typeinfo typ ;;
             let args_typ :=
                 match typinf with
                   | Tfun _ typs => typs
                   | _ => []
                 end
             in
             (* Add arguments to the map *)
             (* TODO pad args_typ so that it has always the same length with ys *)
             let mapfv' := add_params ys args_typ mapfv in
             (* formal parameter for the environment pointer *)
             Γ <- get_name ;;
             e' <- exp_closure_conv e mapfv' Γ ;;
             defs'' <- fundefs_closure_conv defs' mapfv ;;
             (* find the new name of the function *)
             let (code_ptr, typ') :=
                 match Maps.PTree.get f mapfv with
                   | Some entry =>
                     match entry with
                       | MRFun ptr typ _ => (ptr, typ)
                       | _ => (f, 1%positive) (* should never reach here *)
                     end
                   | None => (f, 1%positive) (* should never reach here *)
                 end
             in
             ret (Fcons code_ptr typ' (Γ::ys) e' defs'')
           | Fnil => ret Fnil
         end.

End CC.


Fixpoint max_list ls : positive :=
  let fix aux ls (n : positive) :=
      match ls with
        | nil => n
        | cons x xs => aux xs (Pos.max x n)
      end
  in
    aux ls 1%positive.

Fixpoint max_var e z :=
  match e with
  | Econstr x _ _ ys e => max_var e (max_list (z::x::ys)) 
  | Ecase x ys => max_list (z::x::(List.map fst ys))
  | Eproj x _ _ y e => max_var e (max_list (z::x::y::nil))
  | Efun defs e =>
    let z' := max_var_fundefs defs z in
    max_var e z'
  | Eapp f xs => max_list (z::f::xs)
  | Eprim x _ _ ys e => max_var e (max_list (z::x::ys))
  end
with max_var_fundefs defs z :=
       match defs with
         | Fcons f _ ys e defs =>
           let z' := max_var e z in
           max_var_fundefs defs (max_list (z::f::ys))
         | Fnil => z
       end.


(* XXX closure conversion does not currently handles the types right. *)
(* types are bogus because they rely on parameters instantiated with dummies *)
Definition closure_conversion (e : exp) : exp :=
  let next :=
      let x := max_var e 1%positive in
      if Pos.leb x 3%positive then 3%positive else (x+1)%positive
  in
  let state := (next, TDict.empty) in
  exp_hoist (fst (runState
                    (exp_closure_conv 1%positive 1%positive id 1%positive
                                      e (Maps.PTree.empty VarInfo) 1%positive)
                    state)).
