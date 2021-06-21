From CertiCoq.L6 Require Import MockExpr Prototype.

Require Import Coq.Strings.Ascii Coq.Strings.String.
Infix "+++" := append (at level 60, right associativity).

Require Import Coq.Lists.List.
Import ListNotations.

From MetaCoq Require Import Template.All.
Import MCMonadNotation.

From ExtLib.Core Require Import RelDec.
From ExtLib.Data Require Import Nat List Option Pair String.
From ExtLib.Structures Require Import Monoid Functor Applicative Monads Traversable.
From ExtLib.Data.Monads Require Import IdentityMonad EitherMonad StateMonad.

Require Import Coq.NArith.BinNat.
Local Open Scope N_scope.

Require Import Coq.Relations.Relations.

Require Import Ltac2.Ltac2.
Import Ltac2.Notations.

Set Default Proof Mode "Ltac2".

Unset Strict Unquote Universe Mode.

(* ---------- Example ---------- *)

Instance Frame_exp_inj : @Frame_inj exp_univ _.
Proof. unfold Frame_inj; destruct f; simpl; ltac1:(congruence). Defined.

Check frames_nil >:: cons_fundef0 [] >:: fFun2 0%nat [].
Check fun e => framesD <[ cons_fundef0 []; fFun2 0%nat [] ]> e.

Definition used_vars_var : var -> list var := fun x => [x].
Definition used_vars_constr : constr -> list var := fun _ => [].
Definition used_vars_list_var : list var -> list var := fun xs => xs.
Definition used_vars_list {A} (f : A -> list var) (xs : list A) : list var := concat (map f xs).
Definition used_vars_arm' used_vars_exp : constr * exp -> list var := fun '(_, e) => used_vars_exp e.
Fixpoint used_vars_exp (e : exp) : list var :=
  match e with
  | eHalt x => [x]
  | eApp f xs => f :: xs
  | eCons x c ys e => x :: ys ++ used_vars_exp e
  | eProj x y n e => x :: y :: used_vars_exp e
  | eCase x arms => x :: used_vars_list (used_vars_arm' used_vars_exp) arms
  | eFuns fds e => used_vars_list used_vars_fundef fds ++ used_vars_exp e
  end
with used_vars_fundef (fd : fundef) :=
  let 'fFun f xs e := fd in
  f :: xs ++ used_vars_exp e.
Definition used_vars_arm := used_vars_arm' used_vars_exp.

Notation "C '⟦+' x '+⟧'" := (framesD C x) (at level 10).

(* Example: commonly want to track max used vars for fresh name generation *)
Definition used_vars_prop {A : exp_univ} (C : frames_t A exp_univ_exp) (e : univD A) (x : var) : Prop :=
  ~ In x (used_vars_exp (C ⟦+ e +⟧)).

(* When just moving up and down, next fresh var doesn't need to be updated *)

Instance Preserves_S_dn_exp : Preserves_S_dn (@used_vars_prop).
Proof. intros A B C C_ok f x; destruct f; unfold used_vars_prop; simpl; intros; assumption. Defined.

Instance Preserves_S_up_exp : Preserves_S_up (@used_vars_prop).
Proof. intros A B C C_ok f x; destruct f; unfold used_vars_prop; simpl; intros; assumption. Defined.

Extraction Inline Preserves_S_dn_exp Preserves_S_up_exp.

(* ---------- Mock relation + state for testing ---------- *)

Inductive R : exp -> exp -> Prop :=
| R0 : forall (C : frames_t exp_univ_exp exp_univ_exp) x c ys ys' e,
    ys' = ys ++ ys ->
    R (C⟦+ eCons x c ys e+⟧) (C⟦+ eCons x c ys' (Rec e) +⟧)
| R1 : forall (C : frames_t exp_univ_exp exp_univ_exp) x c y ys ys' e,
    #|ys| = 4%nat ->
    (forall D : frames_t exp_univ_exp exp_univ_exp, D >++ C = D >++ C) ->
    e = e ->
    ys' = ys ++ [y; y] ->
    R (C⟦+ eCons x c (y :: ys) e+⟧) (C⟦+eCons x c ys' (Rec e)+⟧)
| R2 : forall (C : frames_t exp_univ_list_fundef exp_univ_exp) f x xs xs' e fds,
    #|xs| = 0%nat ->
    xs ++ [x] = xs' ->
    C = C ->
    BottomUp (R (C⟦+ fFun f (x :: xs) e :: fds +⟧) (C⟦+ fFun f xs' e :: fds+⟧))
| R3 : forall (C : frames_t exp_univ_list_fundef exp_univ_exp) f x x' xs xs' e fds,
    #|xs| = 0%nat ->
    xs ++ [x] = xs' ->
    C = C ->
    BottomUp (R (C⟦+ fFun f (x :: x' :: xs) e :: fds +⟧) (C⟦+ fFun f xs' e :: fds+⟧)).

Definition I_R {A} (C : frames_t A exp_univ_exp) (n : nat) : Prop := C = C.

Definition I_S {A} (C : frames_t A exp_univ_exp) (x : univD A) (n : nat) : Prop := C⟦+x+⟧ = C⟦+x+⟧.

Instance Preserves_R_R_C : Preserves_R (@I_R).
Proof. intros A B C C_ok f [n _]; exists n; unerase; reflexivity. Defined.

Instance Preserves_S_dn_St : Preserves_S_dn (@I_S).
Proof. intros A B C C_ok f x [n _]; exists n; unerase; reflexivity. Defined.

Instance Preserves_S_up_St : Preserves_S_up (@I_S).
Proof. intros A B C C_ok f x [n _]; exists n; unerase; reflexivity. Defined.

Extraction Inline Preserves_R_R_C Preserves_S_dn_St Preserves_S_up_St.

(* Run TemplateProgram (tmPrint =<< parse_rel R). *) (* For some reason, this hangs.. *)

(* ...but this doesn't: *)
Goal True.
  ltac1:(parse_rel 0 R ltac:(fun x n => idtac x)).
Abort.

Goal True.
  ltac1:(
    parse_rel 0 R ltac:(fun rules n =>
    run_template_program (
      fueled' <- tmQuote true ;;
      metric' <- tmQuote tt ;;
      I_D' <- tmQuote (@I_D_plain exp_univ Frame_exp unit) ;;
      D' <- tmQuote unit ;;
      I_D' <- tmQuote (@I_D_plain exp_univ Frame_exp unit) ;;
      R' <- tmQuote nat ;;
      I_R' <- tmQuote (@I_R) ;;
      S' <- tmQuote nat ;;
      I_S' <- tmQuote (@I_S) ;;
      delayD <- tmQuote (@delayD exp_univ Frame_exp unit (@I_D_plain exp_univ Frame_exp unit) _) ;;
      ret (fueled', metric', D', I_D', R', I_R', S', I_S', delayD)) ltac:(fun pack =>
    lazymatch pack with
    | (?fueled', ?metric', ?D', ?I_D', ?R', ?I_R', ?S', ?I_S', ?delayD) =>
      runGM n (
        let! fueled'' := named_of [] fueled' in
        let! metric'' := named_of [] metric' in
        let! D'' := named_of [] D' in
        let! I_D'' := named_of [] I_D' in
        let! delayD' := named_of [] delayD in
        let! R'' := named_of [] R' in
        let! I_R'' := named_of [] I_R' in
        let! S'' := named_of [] S' in
        let! I_S'' := named_of [] I_S' in
        gen_extra_vars_tys AuxData_exp rules D'' I_D'' R'' I_R'' S'' I_S'' delayD') ltac:(fun qobs n =>
        run_template_program (
          (* tmPrint qobs ;; *)
          (* tmReturn tt) *)
          obs' <- monad_map tmUnquote qobs ;;
          tmPrint obs')
          ltac:(fun x => idtac))
    end))).
Abort.

Goal True.
  ltac1:(
    parse_rel 0 R ltac:(fun rules n =>
    run_template_program (
      fueled' <- tmQuote true ;;
      metric' <- tmQuote tt ;;
      I_D' <- tmQuote (@I_D_plain exp_univ Frame_exp unit) ;;
      D' <- tmQuote unit ;;
      I_D' <- tmQuote (@I_D_plain exp_univ Frame_exp unit) ;;
      R' <- tmQuote nat ;;
      I_R' <- tmQuote (@I_R) ;;
      S' <- tmQuote nat ;;
      I_S' <- tmQuote (@I_S) ;;
      delayD <- tmQuote (@delayD exp_univ Frame_exp unit (@I_D_plain exp_univ Frame_exp unit) _) ;;
      ret (fueled', metric', D', I_D', R', I_R', S', I_S', delayD)) ltac:(fun pack =>
    lazymatch pack with
    | (?fueled', ?metric', ?D', ?I_D', ?R', ?I_R', ?S', ?I_S', ?delayD) =>
      runGM n (
        let! fueled'' := named_of [] fueled' in
        let! metric'' := named_of [] metric' in
        let! D'' := named_of [] D' in
        let! I_D'' := named_of [] I_D' in
        let! delayD' := named_of [] delayD in
        let! R'' := named_of [] R' in
        let! I_R'' := named_of [] I_R' in
        let! S'' := named_of [] S' in
        let! I_S'' := named_of [] I_S' in
        gen_run_rule_tys rules fueled'' metric'' R'' I_R'' S'' I_S'') ltac:(fun qobs n =>
        run_template_program (
          (* tmPrint qobs ;; *)
          (* tmReturn tt) *)
          obs' <- monad_map tmUnquote qobs ;;
          tmPrint obs')
          ltac:(fun x => idtac))
    end))).
Abort.

Goal True.
  ltac1:(
    parse_rel 0 R ltac:(fun rules n =>
    run_template_program (
      fueled' <- tmQuote true ;;
      metric' <- tmQuote tt ;;
      I_D' <- tmQuote (@I_D_plain exp_univ Frame_exp unit) ;;
      D' <- tmQuote unit ;;
      I_D' <- tmQuote (@I_D_plain exp_univ Frame_exp unit) ;;
      R' <- tmQuote nat ;;
      I_R' <- tmQuote (@I_R) ;;
      S' <- tmQuote nat ;;
      I_S' <- tmQuote (@I_S) ;;
      delayD <- tmQuote (@delayD exp_univ Frame_exp unit (@I_D_plain exp_univ Frame_exp unit) _) ;;
      ret (fueled', metric', D', I_D', R', I_R', S', I_S', delayD)) ltac:(fun pack =>
    lazymatch pack with
    | (?fueled', ?metric', ?D', ?I_D', ?R', ?I_R', ?S', ?I_S', ?delayD) =>
      runGM n (
        let! fueled'' := named_of [] fueled' in
        let! metric'' := named_of [] metric' in
        let! D'' := named_of [] D' in
        let! I_D'' := named_of [] I_D' in
        let! delayD' := named_of [] delayD in
        let! R'' := named_of [] R' in
        let! I_R'' := named_of [] I_R' in
        let! S'' := named_of [] S' in
        let! I_S'' := named_of [] I_S' in
        gen_constr_delay_tys AuxData_exp rules D'' I_D'' delayD') ltac:(fun qobs n =>
        run_template_program (
          (* tmPrint qobs ;; *)
          (* tmReturn tt) *)
          obs' <- monad_map tmUnquote qobs ;;
          tmPrint obs')
          ltac:(fun x => idtac))
    end))).
Abort.

Goal True.
  ltac1:(
    parse_rel 0 R ltac:(fun rules n =>
    run_template_program (
      fueled' <- tmQuote true ;;
      metric' <- tmQuote tt ;;
      I_D' <- tmQuote (@I_D_plain exp_univ Frame_exp unit) ;;
      D' <- tmQuote unit ;;
      I_D' <- tmQuote (@I_D_plain exp_univ Frame_exp unit) ;;
      R' <- tmQuote nat ;;
      I_R' <- tmQuote (@I_R) ;;
      S' <- tmQuote nat ;;
      I_S' <- tmQuote (@I_S) ;;
      delayD <- tmQuote (@delayD exp_univ Frame_exp unit (@I_D_plain exp_univ Frame_exp unit) _) ;;
      ret (fueled', metric', D', I_D', R', I_R', S', I_S', delayD)) ltac:(fun pack =>
    lazymatch pack with
    | (?fueled', ?metric', ?D', ?I_D', ?R', ?I_R', ?S', ?I_S', ?delayD) =>
      runGM n (
        let! fueled'' := named_of [] fueled' in
        let! metric'' := named_of [] metric' in
        let! D'' := named_of [] D' in
        let! I_D'' := named_of [] I_D' in
        let! delayD' := named_of [] delayD in
        let! R'' := named_of [] R' in
        let! I_R'' := named_of [] I_R' in
        let! S'' := named_of [] S' in
        let! I_S'' := named_of [] I_S' in
        gen_smart_constr_tys AuxData_exp rules fueled'' metric'' R'' I_R'' S'' I_S'') ltac:(fun qobs n =>
        run_template_program (
          (* tmPrint qobs ;; *)
          (* tmReturn tt) *)
          obs' <- monad_map tmUnquote qobs ;;
          tmPrint obs')
          ltac:(fun x => idtac))
    end))).
Abort.

Definition nNamed s := {| binder_name := nNamed s; binder_relevance := Relevant |}.
Definition test_case_tree (pat pat_ty ret_ty success failure : term) : TemplateMonad unit :=
  mlet (ast, nameless) <- runGM (
    let! ast :=
      gen_case_tree exp_aux_data.(aIndInfo) [(tVar "$input", pat)] ret_ty success failure
    in
    let ast := tLambda (nNamed "$input") pat_ty ast in
    let! nameless := indices_of [] ast in
    (* let nameless := tRel 0 in *)
    ret (ast, nameless)) ;;
  (* print_nf nameless ;; *)
  tm <- tmUnquote nameless ;;
  tmPrint tm ;;
  print_nf ast ;;
  ret tt.

(*
Compute runGM' 0 (gen_case_tree exp_aux_data.(aIndInfo)
  [(tVar "discr", mkApps <%S%> [mkApps <%S%> [mkApps <%S%> [tVar "n"]]])] <%nat%> <%true%> <%false%>).

Compute <%(0, eApp 0 [])%>.
Run TemplateProgram (test_case_tree <%3%nat%> <%nat%> <%bool%> <%true%> <%false%>).
Run TemplateProgram (test_case_tree <%@nil nat%> <%list nat%> <%bool%> <%true%> <%false%>).
Run TemplateProgram (test_case_tree <%eApp 0 []%> <%exp%> <%bool%> <%true%> <%false%>).
Run TemplateProgram (test_case_tree <%(0, eApp 0 [])%> <%(constr * exp)%type%>
                                   <%bool%> <%true%> <%false%>).
Run TemplateProgram (test_case_tree <%eCase 1 [(0, eApp 0 [])]%> <%exp%>
                                   <%bool%> <%true%> <%false%>).
Run TemplateProgram (test_case_tree
  (mkApps <%eCase%> [tVar "$n"; mkApps <%@cons (constr * exp)%type%> [
    mkApps <%@pair constr exp%> [tVar "$m";
    mkApps <%eApp%> [<%0%>; <%@nil var%>]]; <%@nil (constr * exp)%type%>]])
  <%exp%> <%nat%> (mkApps <%plus%> [tVar "$n"; tVar "$m"]) <%O%>).
*)

Goal True.
  ltac1:(
    parse_rel 0 R ltac:(fun rules n =>
    run_template_program (
      fueled' <- tmQuote true ;;
      metric' <- tmQuote tt ;;
      I_D' <- tmQuote (@I_D_plain exp_univ Frame_exp unit) ;;
      D' <- tmQuote unit ;;
      I_D' <- tmQuote (@I_D_plain exp_univ Frame_exp unit) ;;
      R' <- tmQuote nat ;;
      I_R' <- tmQuote (@I_R) ;;
      S' <- tmQuote nat ;;
      I_S' <- tmQuote (@I_S) ;;
      delayD <- tmQuote (@delayD exp_univ Frame_exp unit (@I_D_plain exp_univ Frame_exp unit) _) ;;
      ret (fueled', metric', D', I_D', R', I_R', S', I_S', delayD)) ltac:(fun pack =>
    lazymatch pack with
    | (?fueled', ?metric', ?D', ?I_D', ?R', ?I_R', ?S', ?I_S', ?delayD) =>
      runGM n (
        let! fueled'' := named_of [] fueled' in
        let! metric'' := named_of [] metric' in
        let! D'' := named_of [] D' in
        let! I_D'' := named_of [] I_D' in
        let! delayD' := named_of [] delayD in
        let! R'' := named_of [] R' in
        let! I_R'' := named_of [] I_R' in
        let! S'' := named_of [] S' in
        let! I_S'' := named_of [] I_S' in
        gen_inspect_tys AuxData_exp rules D'' I_D'' R'' I_R'' S'' I_S'' delayD') ltac:(fun qobs n =>
        run_template_program (
          let '(topdown, bottomup) := qobs in
          topdown' <- monad_map tmUnquote topdown ;;
          bottomup' <- monad_map tmUnquote bottomup ;;
          tmPrint "-------------------- topdown --------------------" ;;
          tmPrint topdown' ;;
          tmPrint "-------------------- bottomup --------------------" ;;
          tmPrint bottomup')
          ltac:(fun x => idtac))
    end))).
Abort.

(* Context (opaque_delay_t : forall {A : exp_univ}, univD A -> Set) *)
(*        `{Hopaque_delay : @Delayed exp_univ Frame_exp (@opaque_delay_t)}. *)
Definition opaque_delay_t {A : exp_univ} (e : univD A) := unit.

Definition const_fun {A B} (x : A) (y : B) : B := y.

Inductive R' : exp -> exp -> Prop :=
| R'0 : forall (C : frames_t exp_univ_exp exp_univ_exp) x c ys ys' e,
    ys' = ys ++ ys ->
    R' (C⟦+eCons x c ys e+⟧) (C⟦+eCons x c ys' (Rec (const_fun tt e))+⟧)
| R'1 : forall (C : frames_t exp_univ_exp exp_univ_exp) x c y ys ys' e,
    #|ys| = 4%nat /\
    (forall D : frames_t exp_univ_exp exp_univ_exp, D >++ C = D >++ C) /\
    e = e /\
    ys' = ys ++ [y; y] ->
    R' (C⟦+eCons x c (y :: ys) e+⟧) (C⟦+eCons x c ys' (Rec e)+⟧)
| R'4 : forall (C : frames_t exp_univ_exp exp_univ_exp) x c ys e,
    R' (C⟦+eCons x c ys e+⟧) (C⟦+eCons x c ys (eCons x c ys (Rec e))+⟧)
| R'2 : forall (C : frames_t exp_univ_list_fundef exp_univ_exp) f x xs xs' e fds,
    #|xs| = 0%nat /\
    xs ++ [x] = xs' /\
    C = C ->
    BottomUp (R' (C⟦+fFun f (x :: xs) e :: fds+⟧) (C⟦+fFun f xs' e :: fds+⟧))
| R'3 : forall (C : frames_t exp_univ_list_fundef exp_univ_exp) f x x' xs xs' e fds,
    #|xs| = 0%nat /\
    xs ++ [x] = xs' /\
    C = C ->
    BottomUp (R' (C⟦+fFun f (x :: x' :: xs) e :: fds+⟧) (C⟦+fFun f xs' e :: fds+⟧)).

Goal True.
  ltac1:(
  parse_rel 0 R' ltac:(fun rules n => idtac rules n)).
Abort.

Definition rw_R : rewriter exp_univ_exp true tt R' unit (I_D_plain (U:=exp_univ) (D:=unit)) nat (@I_R) nat (@I_S).
Proof.
  ltac1:(mk_rw';
    try lazymatch goal with
    | |- SmartConstr _ -> _ => mk_smart_constr
    | |- RunRule _ -> _ => mk_run_rule
    | |- Topdown _ -> _ => mk_topdown
    | |- Bottomup _ -> _ => mk_bottomup
    end;
    (* This particular rewriter's delayed computation is just the identity function, *)
    (* so ConstrDelay is easy *)
    try lazymatch goal with
    | |- ConstrDelay _ -> _ => mk_easy_delay
    end;
    (* try lazymatch goal with *)
    (* | |- ExtraVars _ -> _ => admit *)
    (* end; *)
    [..|mk_rewriter];
    idtac).
  { cbn; intros; ltac1:(cond_success success).
    eapply success; eauto.
    ltac1:(unshelve econstructor; [exact O|unerase; reflexivity]). }
  { cbn; intros; ltac1:(cond_failure). }
  { cbn; intros; ltac1:(cond_success success); eapply success; eauto.
    ltac1:(unshelve econstructor; [exact O|unerase; reflexivity]). }
  { cbn; intros; ltac1:(cond_failure). }
  { cbn; intros; ltac1:(cond_failure). }
Defined.

Set Extraction Flag 2031. (* default + linear let + linear beta *)
Recursive Extraction rw_R.
(* - is directly recursive (fixpoint combinator gone) 
   - context parameter erased *)

Definition size_ctor : constr -> nat := fun _ => 1%nat.
Definition size_var : var -> nat := fun _ => 1%nat.
Definition size_list {A} (size : A -> nat) (xs : list A) : nat :=
  (fold_right (fun x n => 1 + size x + n) 1 xs)%nat.
Definition size_vars := size_list size_var.
Fixpoint size_exp (e : exp) : nat :=
  match e with
  | eHalt x => 1 + size_var x
  | eApp f xs => 1 + size_var f + size_vars xs
  | eCons x c ys e => 1 + size_var x + size_ctor c + size_vars ys + size_exp e
  | eProj x y n e => 1 + size_var x + size_var y + n + size_exp e
  | eCase x arms => 1 + size_var x + size_list (fun '(c, e) => 1 + size_ctor c + size_exp e) arms
  | eFuns fds e => 1 + size_list size_fd fds + size_exp e
  end%nat
with size_fd (fd : fundef) : nat :=
  let 'fFun f xs e := fd in
  1 + size_var f + size_vars xs + size_exp e.

Definition size {A} : univD A -> nat :=
  match A with
  | exp_univ_prod_constr_exp => fun '(c, e) => 1 + size_ctor c + size_exp e
  | exp_univ_list_prod_constr_exp => size_list (fun '(c, e) => 1 + size_ctor c + size_exp e)
  | exp_univ_fundef => size_fd
  | exp_univ_list_fundef => size_list size_fd
  | exp_univ_exp => size_exp
  | exp_univ_var => size_var
  | exp_univ_constr => size_ctor
  | exp_univ_nat => id
  | exp_univ_list_var => size_vars
  end%nat.

Require Import Lia.

Definition rw_R_m :
  rewriter exp_univ_exp false (fun A C e => size e) R' unit (I_D_plain (U:=exp_univ) (D:=unit)) nat (@I_R) nat (@I_S).
Proof.
  ltac1:(mk_rw';
    try lazymatch goal with
    | |- SmartConstr _ -> _ => mk_smart_constr
    | |- RunRule _ -> _ => mk_run_rule
    | |- Topdown _ -> _ => mk_topdown
    | |- Bottomup _ -> _ => mk_bottomup
    end;
    try lazymatch goal with
    (* This particular rewriter's delayed computation is just the identity function, *)
    (* so ConstrDelay is easy *)
    | |- ConstrDelay _ -> _ => mk_easy_delay
    end;
    (* try lazymatch goal with *)
    (* | |- ExtraVars _ -> _ => admit *)
    (* end; *)
    [..|mk_rewriter];
    try lazymatch goal with
    (* Solve easy obligations about termination *)
    | |- MetricDecreasing -> _ => intros _; cbn; lia
    end;
    idtac).
  { cbn; intros; ltac1:(cond_success success).
    eapply success; eauto.
    ltac1:(unshelve econstructor; [exact O|unerase; reflexivity]). }
  { cbn; intros; ltac1:(cond_failure). }
  { cbn; intros; ltac1:(cond_success success); eapply success; eauto.
    ltac1:(unshelve econstructor; [exact O|unerase; reflexivity]). }
  { cbn; intros; ltac1:(cond_failure). }
  { cbn; intros; ltac1:(cond_failure). }
  { intros _; rewrite <- H1. unfold const_fun; cbn; ltac1:(lia). }
  { intros _; rewrite <- H1. cbn; ltac1:(lia). }
  { intros _; rewrite <- H0. cbn; ltac1:(lia). }
Defined.

Set Extraction Flag 2031. (* default + linear let + linear beta *)
Recursive Extraction rw_R_m.
(* - is directly recursive (fixpoint combinator gone) 
   - context parameter erased
   - no fuel parameter (termination argument erased) *)

(*
Compute rw_R'' (xI xH) exp_univ_exp <[]>
  (eCons 0 0 [] (eApp 1 []))
  tt
  {| envVal := 0; envPrf := eq_refl |}
  {| stVal := 0; stPrf := eq_refl |}. *)

(* -------------------- Another example -------------------- *)

Instance Eq_var : Eq var := {rel_dec := fun n m => n ==? m}.

Definition renaming := var -> var.

Definition one_renaming x y := fun x' => if x ==? x' then y else x'.

Definition subst_arm' (subst_exp : (var -> var) -> exp -> exp) (σ : var -> var)
  : _ -> constr * exp := fun '(c, e) => (c, subst_exp σ e).
Fixpoint subst_exp σ e :=
  match e with
  | eHalt x => eHalt (σ x)
  | eApp f xs => eApp (σ f) (map σ xs)
  | eCons x c ys e => eCons (σ x) c (map σ ys) (subst_exp σ e)
  | eProj x y n e => eProj (σ x) (σ y) n (subst_exp σ e)
  | eCase x arms => eCase (σ x) (map (subst_arm' subst_exp σ) arms)
  | eFuns fds e => eFuns (map (subst_fd σ) fds) (subst_exp σ e)
  end
with subst_fd σ fd :=
  let 'fFun f xs e := fd in
  fFun (σ f) (map σ xs) (subst_exp σ e).
Definition subst_arm := subst_arm' subst_exp.

Lemma map_id {A} (f : A -> A) xs : (forall x, f x = x) -> map f xs = xs.
Proof. induction xs as [|x xs IHxs]; auto; simpl; intros; now rewrite IHxs. Defined.

Lemma subst_exp_id σ e : (forall x, σ x = x) -> subst_exp σ e = e
with subst_fd_id σ fd : (forall x, σ x = x) -> subst_fd σ fd = fd.
Proof.
  - intros Hσ; destruct e; simpl.
    + now rewrite Hσ.
    + now rewrite Hσ, map_id.
    + now rewrite Hσ, map_id, subst_exp_id.
    + now rewrite Hσ, subst_exp_id.
    + induction arms as [|[] arms Harms]; simpl; try ltac1:(congruence).
      rewrite Hσ in *; do 2 f_equal.
      * now rewrite subst_exp_id.
      * ltac1:(congruence).
    + rewrite subst_exp_id > [|assumption]; f_equal.
      induction fds; auto; simpl.
      rewrite subst_fd_id > [|assumption]; f_equal; assumption.
  - intros Hσ; destruct fd; simpl.
    now rewrite Hσ, map_id, subst_exp_id.
Defined.

Lemma map_comp {A} (f g : A -> A) xs : map (f ∘ g) xs = map f (map g xs).
Proof. induction xs as [|x xs IHxs]; auto; simpl; intros; now rewrite IHxs. Defined.

Lemma subst_exp_comp σ1 σ2 e : subst_exp (σ1 ∘ σ2) e = subst_exp σ1 (subst_exp σ2 e)
with subst_fd_comp σ1 σ2 fd : subst_fd (σ1 ∘ σ2) fd = subst_fd σ1 (subst_fd σ2 fd).
Proof.
  - destruct e; simpl; f_equal; try (now (rewrite map_comp)); try (now (apply subst_exp_comp)).
    + induction arms as [|[] arm Harm]; auto; simpl.
      rewrite subst_exp_comp; now f_equal.
    + induction fds as [|[] fd Hfd]; auto; simpl.
      rewrite subst_exp_comp, map_comp; now f_equal.
  - destruct fd; simpl; f_equal > [now rewrite map_comp|now rewrite subst_exp_comp].
Defined.

Definition I_renaming A (e : univD A) (d : renaming) : Prop := True.
Instance Delayed_renaming : Delayed (I_renaming).
Proof.
  ltac1:(unshelve econstructor).
  - destruct A; simpl; intros x [σ _].
    + exact (subst_arm σ x).
    + exact (map (subst_arm σ) x).
    + exact (subst_fd σ x).
    + exact (map (subst_fd σ) x).
    + exact (subst_exp σ x).
    + exact (σ x).
    + exact x.
    + exact x.
    + exact (map σ x).
  - intros. exists id; exact I.
  - intros [] []; simpl;
      try ltac1:(match goal with p : constr * exp |- _ => destruct p; simpl end);
      repeat (rewrite map_id);
      repeat (rewrite subst_exp_id);
      repeat (rewrite subst_fd_id);
      try ltac1:(match goal with |- forall _ : constr * exp, _ => intros []; simpl end);
      repeat (rewrite subst_exp_id);
      try (now (intros; apply subst_fd_id; auto));
      auto.
Defined.
Extraction Inline Delayed_renaming.

Inductive cp_fold : exp -> exp -> Prop :=
| cp_case_fold : forall (C : frames_t exp_univ_exp exp_univ_exp) x c ces e,
    (exists D E ys, C = D >:: eCons3 x c ys >++ E) /\
    (exists l r, ces = l ++ (c, e) :: r) ->
    cp_fold
      (C ⟦+ eCase x ces +⟧)
      (C ⟦+ Rec e +⟧)
| cp_proj_fold : forall (C : frames_t exp_univ_exp exp_univ_exp) x y y' ys n e,
    (exists D E c, C = D >:: eCons3 y c ys >++ E) /\
    nth_error ys n = Some y' ->
    cp_fold
      (C ⟦+ eProj x y n e +⟧)
      (C ⟦+ Rec (subst_exp (one_renaming x y') e) +⟧).

Definition I_cp_env {A} (C : frames_t A exp_univ_exp) (ρ : var -> option (constr × list var)) : Prop :=
  forall x c ys, ρ x = Some (c, ys) ->
  exists D E, C = D >:: eCons3 x c ys >++ E.

Lemma eq_var_spec (x y : var) : Bool.reflect (x = y) (x ==? y).
Proof.
  simpl. destruct (PeanoNat.Nat.eqb_spec x y); constructor; ltac1:(congruence).
Defined.

Instance Preserves_cp_env : Preserves_R (@I_cp_env).
Proof.
  unfold I_cp_env; intros A B C C_ok f [ρ Hρ]; destruct f eqn:Heqf;
  ltac1:(
    match type of Heqf with
    (* The case we care about *)
    | _ = eCons3 _ _ _ => idtac
    (* All other cases: just preserve the invariant *)
    | _ =>
      exists ρ; unerase; intros;
      edestruct Hρ as [D [E Hctx]]; eauto;
      rewrite Hctx; exists D; eexists;
      match goal with
      | |- ?C >++ ?D >:: ?e = _ =>
        now change (C >++ D >:: e) with (C >++ (D >:: e))
      end
    end).
  exists (fun v' => if v' ==? v then Some (c, l) else ρ v'); unerase.
  intros v'; destruct (eq_var_spec v' v); intros c' l' Heq.
  - inversion Heq; subst.
    now exists C, <[]>.
  - edestruct Hρ as [D [E Hctx]]; eauto.
    rewrite Hctx.
    do 2 eexists.
    ltac1:(match goal with
    | |- ?C >:: ?f1 >++ ?E >:: ?f2 = _ =>
      now change (C >:: f1 >++ E >:: f2) with (C >:: f1 >++ (E >:: f2))
    end).
Defined.
Extraction Inline Preserves_cp_env.

Instance Eq_constr : Eq constr := {rel_dec := fun n m => n ==? m}.
Lemma eq_constr_spec (x y : constr) : Bool.reflect (x = y) (x ==? y).
Proof.
  simpl.
  destruct (PeanoNat.Nat.eqb_spec x y); constructor; ltac1:(congruence).
Defined.

Fixpoint find_arm (c : constr) (ces : list (constr * exp)) : option exp :=
  match ces with
  | [] => None
  | (c', e) :: ces => if c ==? c' then Some e else find_arm c ces
  end.

Lemma find_arm_In : forall c e ces, find_arm c ces = Some e -> exists l r, ces = l ++ (c, e) :: r.
Proof.
  induction ces as [|[c' e'] ces Hces] > [inversion 1|].
  unfold find_arm; fold find_arm.
  destruct (eq_constr_spec c c'); intros Heq.
  - inversion Heq; subst; now exists [], ces.
  - destruct (Hces Heq) as [l [r Hlr]]; subst.
    now exists ((c', e') :: l), r.
Defined.

Lemma app_as_ctx :
  forall l ces c r e, ces = l ++ (c, e) :: r ->
  exists C : frames_t exp_univ_exp exp_univ_list_prod_constr_exp, ces = C ⟦+ e +⟧.
Proof.
  induction l; simpl; intros.
  - subst; now exists <[cons_prod_constr_exp0 r; pair_constr_exp1 c]>.
  - subst; edestruct IHl as [C HC]; eauto.
    exists (<[cons_prod_constr_exp1 a]> >++ C).
    rewrite frames_compose_law.
    now rewrite HC; simpl.
Defined.

Lemma In_map_eq {A} (f : A -> A) x xs : In x xs -> f x = x -> In x (map f xs).
Proof.
  induction xs; auto; simpl.
  intros [Heq|Hin]; auto.
  try ltac1:(intuition congruence).
Defined.

Lemma subst_var_size σ x : size_var (σ x) = size_var x. Proof. reflexivity. Qed.
Lemma subst_ctor_size σ x : size_ctor (σ x) = size_ctor x. Proof. reflexivity. Qed.
Lemma subst_vars_size σ xs : size_vars (map σ xs) = size_vars xs.
Proof.
  induction xs as [|x xs IHxs] > [reflexivity|].
  unfold size_vars, size_list, size_var in *; cbn in *; now rewrite IHxs.
Qed.

Fixpoint subst_exp_size σ e : size_exp (subst_exp σ e) = size_exp e
with subst_fd_size σ e : size_fd (subst_fd σ e) = size_fd e.
Proof.
  - destruct e; cbn;
    rewrite ?subst_var_size, ?subst_vars_size, ?subst_ctor_size, ?subst_exp_size, ?subst_fd_size;
    try reflexivity.
    + induction arms as [|[c e] ces IHces] > [reflexivity|cbn in *].
      unfold size_list in IHces; inversion IHces as [IHces']; clear IHces.
      now rewrite subst_exp_size, IHces'.
    + ltac1:(repeat match goal with |- context [S (?n + ?m)] => change (S (n + m))%nat with (S n + m)%nat end).
      do 2 f_equal; induction fds as [|fd fds IHfds] > [reflexivity|cbn in *].
      unfold size_list in IHfds; inversion IHfds as [IHfds']; clear IHfds.
      now rewrite subst_fd_size.
  - destruct e as [f xs e]; cbn; now rewrite subst_vars_size, subst_exp_size.
Qed.

Definition rw_cp :
  rewriter exp_univ_exp false (fun A C e => size e) cp_fold
  renaming (I_renaming) _ (@I_cp_env) unit (I_S_plain (S:=unit)).
Proof.
  ltac1:(mk_rw;
    try lazymatch goal with
    (* Explain how to incrementalize substitutions *)
    | |- ConstrDelay _ -> _ =>
      clear; intros _; intros;
      lazymatch goal with
      | d : Delay _ _, H : forall _, _ |- _ =>
        destruct d as [d Hd]; cbn in H; unshelve eapply H;
        try lazymatch goal with |- Delay _ _ => eexists end;
        try lazymatch goal with |- _ = _ => reflexivity end;
        try lazymatch goal with |- I_renaming _ _ _ => exact I end
      end
    (* Solve easy obligations about termination *)
    | |- MetricDecreasing -> _ =>
      intros _; cbn; repeat match goal with |- context [let '_ := ?e in _] => destruct e end; lia
    end).
  - (* Case folding *)
    intros _ R C C_ok x ces [d []] r s success failure.
    destruct r as [ρ Hρ] eqn:Hr.
    destruct (ρ (d x)) as [[c ys]|] eqn:Hx > [|ltac1:(cond_failure)].
    destruct (find_arm c ces) as [e|] eqn:Hc > [|ltac1:(cond_failure)].
    ltac1:(cond_success success).
    specialize (success e (exist _ d I) (d x) (map (subst_arm d) ces) c (subst_exp d e)).
    apply success; auto; unerase; split.
    + edestruct Hρ as [D [E Hctx]]; eauto.
    + apply find_arm_In in Hc; destruct Hc as [l [r_arms Hlr]].
      exists (map (subst_arm d) l), (map (subst_arm d) r_arms); subst ces.
      now rewrite !map_app.
  - (* Projection folding *)
    clear; intros _ R C C_ok e x y n [d []] r s success failure.
    destruct r as [ρ Hρ] eqn:Hr.
    destruct (ρ (d y)) as [[c ys]|] eqn:Hx > [|ltac1:(cond_failure)].
    destruct (nth_error ys n) as [y'|] eqn:Hn > [|ltac1:(cond_failure)].
    ltac1:(cond_success success); apply (success (subst_exp d e)
                                                 (exist _ (fun e => one_renaming (d x) y' (d e)) I)
                                                 (d x) (d y) n y' ys); auto; unerase.
    + edestruct Hρ as [D [E Hctx]]; eauto.
    + now rewrite <- subst_exp_comp.
  - (* In case folding, the selected case arm is smaller than the case expression we started with *)
    intros _. rewrite <- H1. clear - H; destruct H as [_ [l [r Hin]]]; subst ces; cbn.
    ltac1:(match goal with |- (?x < S (S ?y))%nat => enough (x < y)%nat by lia end).
    induction l as [|[c' e] ces IHces] > [cbn; ltac1:(lia)|].
    eapply PeanoNat.Nat.lt_trans > [ltac1:(eassumption)|].
    unfold size_list; cbn; ltac1:(lia).
  - (* In proj folding, the subexpression is smaller than what we started with *)
    rewrite <- H1, subst_exp_size; cbn; ltac1:(lia).
Defined.

Set Extraction Flag 2031. (* default + linear let + linear beta *)
Recursive Extraction rw_cp. (* no fuel parameter *)

Definition rw_cp_top e : result (Root:=exp_univ_exp) cp_fold (I_S_plain (S:=unit)) (erase <[]>) e.
Proof.
  ltac1:(replace e with (delayD ((exist _ (fun x => x) I) : (Delay I_renaming e)))
        by (cbn; rewrite subst_exp_id; auto)).
  ltac1:(unshelve eapply (rw_cp I);
  try lazymatch goal with |- erased nat => refine (erase _) end;
  try lazymatch goal with
  | |- e_ok (erase _) => apply erase_ok
  | |- Param _ _ => exists (fun _ => None); unerase; unfold I_cp_env; intros; congruence
  | |- State _ _ _ => exists tt; exact I
  | |- «_» => unerase; reflexivity
  | |- _ = _ => reflexivity
  end).
Defined.

(*
Compute (rw_cp_top (
  let x0 := 0 in
  let x1 := 1 in
  let x2 := 2 in
  let x3 := 3 in
  let x4 := 4 in
  let x5 := 5 in
  let x6 := 6 in
  let c1 := 1 in
  let c2 := 2 in
  let c3 := 3 in
  eCons x0 c2 [x5; x5; x1; x5; x5]
  (eCons x2 c1 [x0; x3]
  (eCase x0 [
    (c1, eApp x0 [x0]);
    (c2,
      (eProj x4 x0 (2%nat)
      (eProj x5 x2 (1%nat)
      (eApp x4 [x5]))));
    (c3, (eApp x0 [x0]))])))).
*)
