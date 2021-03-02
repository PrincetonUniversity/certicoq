(* Conversion from L4.expression to L6.cps *)

Require Import Coq.ZArith.ZArith Coq.Strings.String Coq.Lists.List.
Require Import ExtLib.Data.String.
Require Import Common.AstCommon Common.compM.
Require Import Znumtheory.
Require Import Bool.
Require compcert.lib.Maps.
Require Recdef.
Import Nnat.

Import ListNotations.
Require Import L4.expression L6.state L6.cps
        L6.cps_show L6.ctx L6.List_util.

Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Structures.Monads.
  
Import Monad.MonadNotation.
Open Scope monad_scope.

Section Tags.

  Context (prim_map : M.t (kername * string (* C definition *) * bool (* tinfo *) * nat (* arity *))) 
          (fun_tag : fun_tag) (* Unary function tag *)  
          (default_tag : ctor_tag)
          (default_itag : ind_tag)
          (next_id : positive). 
  
  Definition anfM := @compM' unit.
  
  
  (* Converting a DeBruijn index to named variable *)
  (** The actual map grows from 1 onward. We keep the pointer p to the last entry of the map. 
    When we have to lookup DeBruijn index i in the map, we lookup (p - i). *)

  Definition consume_fun (f x : var) : exp_ctx :=
    Efun1_c (Fcons f fun_tag [x] (Ehalt f) Fnil) Hole_c. 

  Definition var_map := (M.t var * N)%type.

  Definition get_var_name (vmp : var_map) (x : N) :=
    let (vm, p) := vmp in
    match p - x with
    | N0 => None
    | Npos pos => M.get pos vm
    end.

  Definition add_var_name (vmp : var_map) (x' : var) :=
    let (vm, p) := vmp in
    let p' := N.succ_pos p in
    (M.set p' x' vm, Npos p').

  Definition new_var_map := (M.empty var, 0%N). 


  Inductive anf_value :=
  | Anf_Var (x : var)
  | Anf_App (f x : var)
  | Constr (c : ctor_tag) (xs : list var)
  | Proj (c : ctor_tag) (n : N) (y : var)
  | Fun (ft : cps.fun_tag) (x : var) (e : cps.exp)
  | Prim (pr : positive) (xs : list var).

  Definition anf_term : Type := anf_value * exp_ctx.

  Definition anf_term_to_exp (t : anf_term) : anfM cps.exp :=
    let '(v, C) := t in
    match v with
    | Anf_Var x => ret (C |[ Ehalt x ]|)
    | Anf_App f x => ret (C |[ Eapp f fun_tag [x] ]|)
    | Constr c xs =>
      x' <- get_named_str "y" ;; (* Get variable for interim result *)
      ret (C |[ Econstr x' c xs (Ehalt x') ]|)
    | Proj c n y =>
      x' <- get_named_str "y" ;; (* Get variable for interim result *)
      ret (C |[ Eproj x' c n y (Ehalt x') ]|)
    | Fun ft x e =>
      x' <- get_named_str" y" ;; (* Get variable for interim result *)
      ret (C |[ Efun (Fcons x' ft [x] e Fnil) (Ehalt x') ]|)
    | Prim pr xs =>
      x' <- get_named_str "y" ;; (* Get variable for interim result *)
      ret (C |[ Eprim x' pr xs (Ehalt x') ]|)
    end.

  Definition anf_term_to_ctx (t : anf_term) (n : name) : anfM (var * exp_ctx) :=
    let '(v, C) := t in
    match v with
    | Anf_Var x => ret (x, C)
    | Anf_App f x =>
      x' <- get_named n ;; (* Get variable for interim result *)
      ret (x', comp_ctx_f C (Eletapp_c x' f fun_tag [x] Hole_c))
    | Constr c xs =>
      x' <- get_named n ;; (* Get variable for interim result *)
      ret (x', comp_ctx_f C (Econstr_c x' c xs Hole_c))
    | Proj c i y =>
      x' <- get_named n ;; (* Get variable for interim result *)
      ret (x', comp_ctx_f C (Eproj_c x' c i y Hole_c))
    | Fun ft x e =>
      x' <- get_named n ;; (* XXX keep n or n'? *)
      ret (x', comp_ctx_f C (Efun1_c (Fcons x' ft [x] e Fnil) (Hole_c)))
    | Prim pr xs =>
      x' <- get_named n ;; (* Get variable for interim result *)
      ret (x', comp_ctx_f C (Eprim_c x' pr xs Hole_c))
    end.

  Definition def_name := nNamed "y".


  (* Conversion to ctags, from L5_to_L6.v *)
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


  Section Convert.

    Context (tgm : conId_map).

    Fixpoint proj_ctx (names : list name) (i : N)
             (scrut : var) (vm : var_map) ct : anfM (exp_ctx * var_map) :=
      match names with
      | [] => ret (Hole_c, vm)
      | n :: ns =>
        x <- get_named n;;
        let vm' := add_var_name vm x in
        cvm <- proj_ctx ns (i+1)%N scrut vm' ct ;; 
        let (C, vm'') := cvm in
        ret (Eproj_c x ct i scrut C, vm'')
      end.

    Fixpoint add_fix_names (B : efnlst) (vm : var_map) : anfM (list var * var_map):=
      match B with
      | eflnil => ret ([], vm)
      | eflcons n _ B' =>
        f_name <- get_named n ;;
        lvm <- add_fix_names B' (add_var_name vm f_name) ;;
        let '(fs, vm') := lvm in
        ret (f_name :: fs, vm')     
      end.

    Fixpoint convert_prim (n : nat) (* arity *)
             (prim : positive) (args : list var) : anfM anf_term :=
      match n with
      | 0%nat =>
        x <- get_named_str "prim" ;; 
        ret (Anf_Var x, Eprim_c x prim (List.rev args) Hole_c)
      | S n =>
        arg <- get_named_str "p_arg" ;; 
        f <- get_named_str "prim_wrapper" ;; 
        '(anf_val, C) <- convert_prim n prim (arg :: args) ;;
        match anf_val with
        | Anf_Var x =>
          ret (Anf_Var f,  Efun1_c (Fcons f fun_tag [arg] (C|[ Ehalt x ]|) Fnil) Hole_c)
        | _ => failwith "Internal error: Expected And_Var but found something else."
        end
      end.


    Fixpoint convert_anf (e : expression.exp) (vm : var_map) : anfM anf_term :=
      match e with
      | Var_e x =>
        match get_var_name vm x with
        | Some v => ret (Anf_Var v, Hole_c)
        | None => failwith  "Unknown DeBruijn index"
        end
      | App_e e1 e2 =>
        a1 <- convert_anf e1 vm ;;
        a2 <- convert_anf e2 vm ;;
        xc1 <- anf_term_to_ctx a1 def_name ;;
        xc2 <- anf_term_to_ctx a2 def_name ;;
        let '(x1, C1) := xc1 in
        let '(x2, C2) := xc2 in
        ret (Anf_App x1 x2, comp_ctx_f C1 C2)
      | Lam_e n e1 =>
        x <- get_named n ;; (* get the name of the argument *)
        a1 <- convert_anf e1 (add_var_name vm x) ;;
        e_body <- anf_term_to_exp a1 ;;
        ret (Fun fun_tag x e_body, Hole_c)
      | Let_e n e1 e2 =>
        a1 <- convert_anf e1 vm ;;
        vC <- anf_term_to_ctx a1 n ;;
        let '(x, C1) := vC in
        a2 <- convert_anf e2 (add_var_name vm x) ;;
        let '(v, C2) := a2 in
        ret (v, comp_ctx_f C1 C2)
      | Con_e dci es =>
        let c_tag := dcon_to_tag dci tgm in
        ts <- convert_anf_exps es vm ;;
        let (ys, C) := ts in
        ret (Constr c_tag ys, C)
      | Fix_e fnlst i =>
        lvm <- add_fix_names fnlst vm ;;
        let (names, vm') := lvm in
        ds <- convert_anf_efnlst fnlst names i vm' ;;
        let (x, defs) := (ds : var * fundefs) in
        ret (Anf_Var x, Efun1_c defs Hole_c)
      | Match_e e1 n bl =>
        (* Zoe: For pattern matching compilation the situation is tricky because they always have to occur in tail
         * position in L6. Our solution currently is to create a function that receives the scrutiny as an arg 
         * pattern matches it, and returns the result of the pattern match. For those that are in tail position
         * these functions will be inlined by shrink reduction yielding the expected compilation result.
         * However, for those that are intermediate results these functions will appear in the C code.
         * Another approach would be to use some form of local continuations (join points) to capture the continuation
         * of the pattern-match. This might be preferable because the join point will always be a tail call. 
         *)
        a <- convert_anf e1 vm ;;
        f <- get_named_str "f_case" ;; (* Case-analysis function *)
        y <- get_named_str "s" ;; (* Scrutinee argument *)
        pats <- convert_anf_branches bl y vm ;;
        xc <- anf_term_to_ctx a def_name ;;
        let (x, C) := xc in
        let C_fun := Efun1_c (Fcons f fun_tag [y] (Ecase y pats) Fnil) C in
        ret (Anf_App f x, C_fun)
      | Prf_e =>
        (* Zoe: Because a lot of dead code is *not* being eliminated *)
        ret (Constr default_tag [], Hole_c)            
        (* f <- get_named_str "f_proof" ;; *)
        (* y <- get_named_str "x" ;; *)
        (* let c := consume_fun f y in              *)
            (* ret (Anf_Var f, c) *)
      | Prim_e p =>
        match M.get p prim_map with
        | Some (nm, s, ar) => convert_prim ar p []
        | None =>failwith "Internal error: identifier for primitive not found"
        end
      end    
    with convert_anf_exps (es : expression.exps) (vm : var_map) : anfM (list var * exp_ctx) :=
           match es with
           | enil => ret ((@nil var), Hole_c)
           | econs e es' =>
             ts <- convert_anf_exps es' vm ;;
             a <- convert_anf e vm ;;
             t <- anf_term_to_ctx a def_name ;;
             let (y, C1) := (t : var * exp_ctx) in
             let (ys, C2) := ts in
             ret (y :: ys, comp_ctx_f C1 C2)
           end
    with convert_anf_efnlst (fdefs : expression.efnlst) (names : list var) (i : N) (vm : var_map) : anfM (var * fundefs) :=
           match fdefs, names with
           | eflnil, nil => ret (1%positive (* dummy var *), Fnil)
           | eflcons n e fdefs', f_name :: names =>
             a1 <- convert_anf e vm ;;
             match a1 with
             | (Fun ft arg e_body, Hole_c) =>
               ds <- convert_anf_efnlst fdefs' names (i - 1)%N vm ;;
               let (fi, defs') := ds in
               let fi' := match i with
                          | 0%N => f_name
                          | Npos _ => fi
                          end in
               ret (fi', Fcons f_name fun_tag [arg] e_body defs')
             | (_, _) => failwith ("Unexpected body of fix in function " ++  print_name n)
             end
           |_, _ => failwith "Wrong number of names for mut. rec. functions"
           end
    with convert_anf_branches (bl : expression.branches_e) (scrut : var) (vm : var_map) : anfM (list (ctor_tag * exp)) :=
           match bl with
           | brnil_e => ret nil
           | brcons_e dc (i, lnames) e bl' =>
             let ctag := dcon_to_tag dc tgm in
             cm <- proj_ctx lnames 0%N scrut vm ctag ;;
             let (Cproj, vm') := cm in
             a <- convert_anf e vm' ;;
             e' <- anf_term_to_exp a ;;
             pats' <- convert_anf_branches bl' scrut vm ;;
             ret ((ctag, Cproj |[ e' ]|) :: pats')
           end.
    
  End Convert.
  
  (* Conversion from ienv from L5_to_L6 *)
  Definition ienv := list (kername * AstCommon.itypPack).
  
  (* returns list of numbers [n, n+m[  and the positive n+m (next available pos) *)
  Fixpoint fromN (n:positive) (m:nat) : list positive * positive :=
    match m with
    | O => (nil, n)
    | S m' =>
      let (l, nm ) := (fromN (n+1) (m')) in
      (n::l, nm)
    end.

  (** process a list of constructors from inductive type ind with ind_tag niT.
    - update the ctor_env with a mapping from the current ctor_tag to the cTypInfo
    - update the conId_map with a pair relating the nCon'th constructor of ind to the ctor_tag of the current constructor

   *)
  Fixpoint convert_cnstrs (tyname:string) (cct:list ctor_tag) (itC:list AstCommon.Cnstr) (ind:BasicAst.inductive) (nCon:N) (unboxed : N) (boxed : N) (niT:ind_tag) (ce:ctor_env) (dcm:conId_map) :=
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
    - process each of the constructor, indicating they are the ith constructor of the nth type of idBundle
   np: number of type parameters for this bundle
   *)
  Fixpoint convert_typack typ (idBundle:kername) (n:nat) (ice:(ind_env * ctor_env*  ctor_tag * ind_tag * conId_map)) : (ind_env * ctor_env * ctor_tag * ind_tag * conId_map) :=
    let '(ie, ce, ncT, niT, dcm) := ice in
    match typ with
    | nil => ice
    | (AstCommon.mkItyp itN itC ) ::typ' =>
      let (cct, ncT') := fromN ncT (length itC) in
      let (ce', dcm') := convert_cnstrs itN cct itC (BasicAst.mkInd idBundle n) 0 0 0 niT ce dcm in
      let ityi := combine cct (map (fun (c:AstCommon.Cnstr) => let (_, n) := c in N.of_nat n) itC) in
      convert_typack typ' idBundle (n+1) (M.set niT ityi ie, ce', ncT', (Pos.succ niT) , dcm')
    end.

  Fixpoint convert_env' (g:ienv) (ice:ind_env * ctor_env * ctor_tag * ind_tag * conId_map) : (ind_env * ctor_env * ctor_tag * ind_tag * conId_map) :=
    let '(ie, ce, ncT, niT, dcm) := ice in
    match g with
    | nil => ice
    | (id, ty)::g' =>
      (* id is name of mutual pack ty is mutual pack *)
      (* constructors are indexed with : name (string) of the mutual pack with which projection of the ty, and indice of the constructor *)
      convert_env' g' (convert_typack ty id 0 (ie, ce, ncT, niT, dcm))
    end.

  (* As we process the L5 inductive environment (ienv), we build:
 - an L6 inductive environment (ind_env) mapping tags (ind_tag) to constructors and their arities
 - an L6 constructor environment (ctor_env) mapping tags (ctor_tag) to information about the constructors
 - a map (conId_map) from L5 tags (conId) to L6 constructor tags (ctor_tag)
convert_env' is called with the next available constructor tag and the next available inductive datatype tag, and inductive and constructor environment containing only the default "box" constructor/type
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


  Definition convert_anf_exp dcm e : anfM cps.exp :=
    a <- convert_anf dcm e new_var_map ;;
    anf_term_to_exp a.

  (** * Top-level convert function *)

  Definition convert_top_anf (ee: ienv * expression.exp) : error cps.exp * comp_data :=
    let '(_, cenv, ctag, itag, dcm) := convert_env (fst ee) in
    let ftag := (fun_tag + 1)%positive in
    let fenv : fun_env := M.set fun_tag (1%N, (0%N::nil)) (M.empty _) in
    let comp_d := pack_data next_id ctag itag ftag cenv fenv (M.empty _) (M.empty nat) [] in
    let '(res_err, (comp_d', _)) := run_compM (convert_anf_exp dcm (snd ee)) comp_d tt in
    (res_err, comp_d').

End Tags.
(* testing code *)

(* 
Require Import Compiler.allInstances. 

(* Require Import L6.cps L6.cps_show instances.
From CertiCoq.L7 Require Import L6_to_Clight. *)

Definition print_BigStepResult_L6 p  n:=
  let '((prim,cenv, nenv, fenv), (rho, e)) := p in
  L7.L6_to_Clight.print (
      match (L6_evaln n p) with
      | Error s _ => s
      | OutOfTime (_, (rho', e')) =>
        "Out of time:"++ (show_cenv cenv)++(show_env nenv cenv false rho') ++
                      (show_exp nenv cenv false e')
      | Result v => show_val nenv cenv false v
      end).

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
*)




                         
                                              
                                     
    
  





