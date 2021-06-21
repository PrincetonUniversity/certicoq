Require Import Coq.Strings.Ascii Coq.Strings.String.
Open Scope string_scope.
Infix "+++" := append (at level 60, right associativity).

Require Import Coq.Lists.List.
Import ListNotations.

From MetaCoq Require Import Template.All.
Import MCMonadNotation.
Module TM := MetaCoq.Template.monad_utils.

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

Set Universe Polymorphism.

Require Export CertiCoq.L6.Rewriting.
Require Export CertiCoq.L6.PrototypeGenFrame.

Open Scope list_scope.

(* -------------------- Converting between named and indices --------------------
   Indices are a real pain for some of the things we want to do.
   Hack: quoted ASTs will never contain names starting with $, so we're free to use
   names like $1, $2, and $3 internally. So, to stay sane, we'll use tVar + nNamed
   binders for naming.
   Before unquoting, all internally generated names will be replaced by the proper
   indices. *)

Fail MetaCoq Run (tmUnquote (tLambda (nNamed "$oof") <%nat%> (tRel 0))).

Definition gensym (suffix : string) : GM string :=
  let! n := get in
  let! _ := modify (fun n => 1 + n) in
  ret (string_of_N n +++ "$" +++ suffix).

Definition add_sigils (x : aname) : GM string :=
  match binder_name x with
  | BasicAst.nAnon => gensym ""
  | BasicAst.nNamed s => gensym s
  end.

Fixpoint remove_sigils (s : string) : aname :=
  match s with
  | EmptyString => nNamed s
  | "$" => nAnon
  | String "$" s => nNamed s
  | String _ s => remove_sigils s
  end.

Fixpoint remove_sigils' (s : string) : string :=
  match s with
  | EmptyString => s
  | "$" => ""
  | String "$" s => s
  | String _ s => remove_sigils' s
  end.

Definition named_of (Γ : list string) (tm : term) : GM term :=
  let fix go (n : nat) (Γ : list string) (tm : term) : GM term :=
    match n with O => raise "named_of: OOF" | S n =>
      let go := go n in
      let go_mfix mfix : GM (mfixpoint term) :=
        let! names := mapM (fun d => add_sigils d.(dname)) mfix in
        let Γ' := rev names ++ Γ in
        mapM
          (fun '(s, d) =>
            mkdef _ (nNamed s)
              <$> go Γ d.(dtype)
              <*> go Γ' d.(dbody)
              <*> ret d.(rarg))
          (combine names mfix)
      in
      match tm with
      | tRel n => tVar <$> nthM_nat n Γ
      | tVar id => ret tm
      | tEvar ev args => ret tm
      | tSort s => ret tm
      | tCast t kind v => tCast <$> go Γ t <*> ret kind <*> go Γ v
      | tProd na ty body =>
        let! s := add_sigils na in
        tProd (nNamed s) <$> go Γ ty <*> go (s :: Γ) body
      | tLambda na ty body =>
        let! s := add_sigils na in
        tLambda (nNamed s) <$> go Γ ty <*> go (s :: Γ) body
      | tLetIn na def def_ty body =>
        let! s := add_sigils na in
        tLetIn (nNamed s) <$> go Γ def <*> go Γ def_ty <*> go (s :: Γ) body
      | tApp f args => mkApps <$> go Γ f <*> mapM (go Γ) args
      | tConst c u => ret tm
      | tInd ind u => ret tm
      | tConstruct ind idx u => ret tm
      | tCase ind_and_nbparams type_info discr branches =>
        tCase ind_and_nbparams
          <$> go Γ type_info <*> go Γ discr
          <*> mapM (fun '(n, t) => pair n <$> go Γ t) branches
      | tProj proj t => tProj proj <$> go Γ t
      | tFix mfix idx => tFix <$> go_mfix mfix <*> ret idx
      | tCoFix mfix idx => tCoFix <$> go_mfix mfix <*> ret idx
      | tInt _ => ret tm
      | tFloat _ => ret tm
      end
    end
  in go 1000%nat Γ tm.

(*
Compute runGM' 0 (named_of [] <%
  fun x y z w : nat =>
  match x, y with
  | S x, S y => z * x + y * w
  | O, y => z + z
  | _, _ => w
  end%nat%>).
Compute runGM' 0 (named_of [] <%forall x y z : nat, x = y -> y = z -> x = z%>).
*)

Definition find_str (s : string) (ss : list string) : GM nat :=
  let fix go n ss :=
    match ss with
    | [] => raise ("find_str: " +++ s)
    | s' :: ss => if s ==? s' then ret n else go (S n) ss
    end
  in go O ss.

Definition indices_of (Γ : list string) (t : term) : GM term :=
  let index_of Γ s := find_str s Γ in
  let go_name (x : aname) : (aname × string) :=
    match binder_name x with
    | BasicAst.nAnon => (nAnon, "anon") (* can never be referred to in named rep, so don't care if there are clashes *)
    | BasicAst.nNamed s => (remove_sigils s, s)
    end
  in
  let fix go (n : nat) (Γ : list string) (tm : term) : GM term :=
    match n with O => raise "named_of: OOF" | S n =>
      let go := go n in
      let go_mfix mfix : GM (mfixpoint term) :=
        let nass := map (fun d => go_name d.(dname)) mfix in
        let '(names, strings) := split nass in
        let Γ' := rev strings ++ Γ in
        mapM
          (fun '(na, d) =>
            mkdef _ na
              <$> go Γ d.(dtype)
              <*> go Γ' d.(dbody)
              <*> ret d.(rarg))
          (combine names mfix)
      in
      match tm with
      | tRel n => ret tm
      | tVar id => tRel <$> index_of Γ id
      | tEvar ev args => ret tm
      | tSort s => ret tm
      | tCast t kind v => tCast <$> go Γ t <*> ret kind <*> go Γ v
      | tProd na ty body =>
        let '(na, s) := go_name na in tProd na <$> go Γ ty <*> go (s :: Γ) body
      | tLambda na ty body =>
        let '(na, s) := go_name na in tLambda na <$> go Γ ty <*> go (s :: Γ) body
      | tLetIn na def def_ty body =>
        let '(na, s) := go_name na in tLetIn na <$> go Γ def <*> go Γ def_ty <*> go (s :: Γ) body
      | tApp f args => mkApps <$> go Γ f <*> mapM (go Γ) args
      | tConst c u => ret tm
      | tInd ind u => ret tm
      | tConstruct ind idx u => ret tm
      | tCase ind_and_nbparams type_info discr branches =>
        tCase ind_and_nbparams
          <$> go Γ type_info <*> go Γ discr
          <*> mapM (fun '(n, t) => pair n <$> go Γ t) branches
      | tProj proj t => tProj proj <$> go Γ t
      | tFix mfix idx => tFix <$> go_mfix mfix <*> ret idx
      | tCoFix mfix idx => tCoFix <$> go_mfix mfix <*> ret idx
      | tInt _ => ret tm
      | tFloat _ => ret tm
      end
    end
  in go 1000%nat [] t.

Definition check_roundtrip (Γ : list string) (t : term) : GM (option (term × term)) :=
  let! named := named_of Γ t in
  let! t' := indices_of Γ named in
  ret (if string_of_term t ==? string_of_term t' then None else Some (t, t')).

Compute runGM' 0 (check_roundtrip [] <%
  fun x y z w : nat =>
  match x, y with
  | S x, S y => z * x + y * w
  | O, y => z + z
  | _, _ => w
  end%nat%>).
Compute runGM' 0 (check_roundtrip [] <%forall x y z : nat, x = y -> y = z -> x = z%>).
Compute runGM' 0 (check_roundtrip [] <%
  fix ev n :=
    match n with
    | 0 => true
    | S n => odd n
    end%nat
  with odd n :=
    match n with
    | 0 => false
    | S n => ev n
    end%nat
  for ev%>).

(* Renames binders too, and doesn't respect scoping rules at all *)
Definition rename (σ : Map string string) : term -> term :=
  let go_str (s : string) : string := find_d s s σ in
  let go_name (na : aname) : aname :=
    match binder_name na with
    | BasicAst.nAnon => na
    | BasicAst.nNamed id => nNamed (go_str id)
    end
  in
  fix go (tm : term) : term :=
    let go_mfix (mfix : list (def term)) : list (def term) :=
      map (fun '(mkdef f ty body rarg) => mkdef _ (go_name f) (go ty) (go body) rarg) mfix
    in
    match tm with
    | tRel n => tm
    | tVar id => tVar (go_str id)
    | tEvar ev args => tEvar ev (map go args)
    | tSort s => tm
    | tCast t kind v => tCast (go t) kind (go v)
    | tProd na ty body => tProd (go_name na) (go ty) (go body)
    | tLambda na ty body => tLambda (go_name na) (go ty) (go body)
    | tLetIn na def def_ty body => tLetIn (go_name na) (go def) (go def_ty) (go body)
    | tApp f args => mkApps (go f) (map go args)
    | tConst c u => tm
    | tInd ind u => tm
    | tConstruct ind idx u => tm
    | tCase ind_and_nbparams type_info discr branches =>
      tCase ind_and_nbparams (go type_info) (go discr) (map (on_snd go) branches)
    | tProj proj t => tProj proj (go t)
    | tFix mfix idx => tFix (go_mfix mfix) idx
    | tCoFix mfix idx => tCoFix (go_mfix mfix) idx
    | tInt _ => tm
    | tFloat _ => tm
    end.

(* -------------------- Generation of helper function types -------------------- *)

(* The type of rewriters (AuxData and typeclass instances needed by generator) *)
Definition rewriter {U} `{H : Frame U} `{AuxData U} (Root : U) (fueled : bool)
           (metric : Metric Root fueled)
           (Rstep : relation (univD Root))
           (D : Set) (I_D : forall (A : U), univD A -> D -> Prop)
           `{@Delayed _ H _ I_D}
           (R : Set) (I_R : forall (A : U), frames_t A Root -> R -> Prop)
           (S : Set) (I_S : forall (A : U), frames_t A Root -> univD A -> S -> Prop)
           `{@Preserves_R _ H _ _ I_R}
           `{@Preserves_S_dn _ H _ _ I_S}
           `{@Preserves_S_up _ H _ _ I_S}
  : Type := rewriter' fueled metric Rstep (I_D:=I_D) I_R I_S.

(* ---------- Flags to aid in proof saerch ---------- *)

(* For each rule, *)
Inductive ExtraVars (s : string) : Prop := MkExtraVars.
Inductive RunRule (s : string) : Prop := MkRunRule.
Inductive Success (s : string) : Prop := MkSuccess.
Inductive Failure (s : string) : Prop := MkFailure.

(* For each constructor, *)
Inductive ConstrDelay {A} (c : A) : Prop := MkConstrDelay.
Inductive SmartConstr {A} (c : A) : Prop := MkSmartConstr.
Inductive SmartConstrCase {A} (e : A) : Prop := MkSmartConstrCase.

(* For each nonatomic type, *)
Inductive Topdown {A} (u : A) : Prop := MkTopdown.
Inductive Bottomup {A} (u : A) : Prop := MkBottomup.
Inductive InspectCaseRule (s : string) : Prop := MkInspectCaseRule.
Inductive InspectCaseCongruence {A} (c : A) : Prop := MkInspectCaseCongruence.
Inductive Active (s : string) : Prop := MkActive.
Inductive Congruence {A} (c : A) : Prop := MkCongruence.
Inductive Fallback : Prop := MkFallback.
Inductive Impossible : Prop := MkImpossible.

Record RwObligations A := mk_obs {
  (* For each rule, *)
  obExtraVars : list A;
  obRunRules : list A;
  (* For each constructor, *)
  obConstrDelays : list A;
  obSmartConstrs : list A;
  (* For each nonatomic type, *)
  obTopdowns : list A;
  obBottomups : list A }.
Arguments mk_obs {_}.

(* ---------- MetaCoq helpers ---------- *)

Fixpoint quote_pos (n : positive) : term :=
  match n with
  | xH => <%xH%>
  | xI n => mkApps <%xI%> [quote_pos n]
  | xO n => mkApps <%xO%> [quote_pos n]
  end.

Definition quote_N (n : N) : term :=
  match n with
  | N0 => <%N0%>
  | Npos n => mkApps <%Npos%> [quote_pos n]
  end.

Definition quote_nat (n : nat) : term :=
  Nat.iter n (fun t => mkApps <%S%> [t]) <%O%>.

Definition quote_bool (b : bool) : term := if b then <%true%> else <%false%>.

Definition quote_char (c : ascii) : term :=
  match c with
  | Ascii x x0 x1 x2 x3 x4 x5 x6 =>
    tApp <%Ascii%> (map quote_bool [x; x0; x1; x2; x3; x4; x5; x6])
  end.

Fixpoint quote_string (s : string) : term :=
  match s with
  | EmptyString => <%EmptyString%>
  | String c s => tApp <%String%> [quote_char c; quote_string s]
  end.

MetaCoq Run (tmPrint =<< tmUnquote (quote_string "abc")).

(* abbreviate = map head . splitOn "_" *)
Fixpoint abbreviate s :=
  let fix skip_to_underscore s := 
    match s with
    | "" => s
    | String "_" s => abbreviate s
    | String _ s => skip_to_underscore s
    end
  in
  match s with
  | "" => s
  | String "_" s => abbreviate s
  | String c s => String c (skip_to_underscore s)
  end.
Compute abbreviate "list_var".

Fixpoint vars_of (t : term) : Set' string :=
  match t with
  | tRel n => empty
  | tVar id => sing id tt
  | tEvar ev args => union_all (map vars_of args)
  | tSort s => empty
  | tCast t kind v => vars_of t ∪ vars_of v
  | tProd na ty body => vars_of ty ∪ vars_of body
  | tLambda na ty body => vars_of ty ∪ vars_of body
  | tLetIn na def def_ty body => vars_of def ∪ vars_of def_ty ∪ vars_of body
  | tApp f args => vars_of f ∪ union_all (map vars_of args)
  | tConst c u => empty
  | tInd ind u => empty
  | tConstruct ind idx u => empty
  | tCase ind_and_nbparams type_info discr branches =>
    vars_of type_info ∪ vars_of discr ∪ union_all (map (fun '(_, t) => vars_of t) branches)
  | tProj proj t => vars_of t
  | tFix mfix idx => union_all (map (fun def => vars_of def.(dtype) ∪ vars_of def.(dbody)) mfix)
  | tCoFix mfix idx => union_all (map (fun def => vars_of def.(dtype) ∪ vars_of def.(dbody)) mfix)
  | tInt _ => empty
  | tFloat _ => empty
  end.

(* ---------- Parsing the inductive relation ---------- *)

Definition named_ctx := list (string × context_decl).

Definition named_of_context (Γ : context) : GM named_ctx :=
  foldrM
    (fun d m =>
      match binder_name d.(decl_name) with
      | BasicAst.nAnon => raise "named_of_context: nAnon"
      | BasicAst.nNamed s => ret ((s, d) :: m)
      end)
    []
    Γ.

Definition drop_names : named_ctx -> context := map snd.

Inductive rule_direction := dTopdown | dBottomup.
Definition path_step := (string × list term) × nat.
Record rule_t := mk_rule {
  rName : string;
  rType : term;
  rArity : nat;
  rDir : rule_direction;
  rHoleU : nat; (* index into the inductive type rw_univ *)
  rΓ : named_ctx; (* 
   C can only be used to construct Props.
   - C : A replaced by C : erased A.
   - Each assumption H : P where C ∈ FV(P) replaced by H : «e_map (fun C => P) C». *)
  rC : term;
  rLhs : term;
  rRhs : term;
  rLhsVars : Set' string;
  rRecVars : Map string (option term); (* Each variable associated with function call pending at that node *)
  rSpecialVars : Map string (option term); }.
Record rules_t := mk_rules {
  rR : inductive;
  rRules : list rule_t;
  rUniv : inductive;
  rRootU : nat;
  rHFrame : term; }.

Definition ctor_ty := (string × term) × nat.
Definition ctors_ty := list ctor_ty.

Section GoalGeneration.

(* Check if a term is a variable if you strip off casts *)
Fixpoint is_var (x : term) : option string :=
  match x with
  | tVar x => Some x
  | tCast x _ _ => is_var x
  | _ => None
  end.

(* Rec (f .. x) *)
(* NOTE: This is a hack and depends on the _CoqProject file+name of this file *)
Compute <%@Rec%>.
Definition prefix := ltac:(
   let e := constr:(<%@Rec%>) in
   match e with
   | tConst ?s [] => let s' := eval cbv in (fst s) in exact s'
   end).
Print prefix.
Definition rec_rhs_vars_of : term -> Map string (option term).
  ltac1:(refine(
  let fix go tm :=
    match tm with
    | tApp (tConstruct _ _ _) args => union_all (map go args)
    | tApp (tConst func []) args =>
      if func ==? (prefix, "Rec") then
        match args with
        | [_A; x] =>
          match is_var x with
          | Some x => sing x None
          | None =>
            match x with
            | tApp (tConstruct _ _ _) _ => empty
            | tApp f ((x :: _) as xs) =>
              match is_var (last xs x) with
              | Some x => sing x (Some (tApp f (removelast xs)))
              | None => empty
              end
            | _ => empty
            end
          end
        | _ => empty
        end
      else empty
    | _ => empty
    end
  in go
)).
Defined.

(* Does x occur in non-binding position? *)
Fixpoint has_var (x : BasicAst.ident) (e : term) {struct e} : bool. ltac1:(refine(
  match e with
  | tRel n => false
  | tVar x' => x ==? x'
  | tEvar ev args => anyb (has_var x) args
  | tSort s => false
  | tCast t kind v => has_var x t || has_var x v
  | tProd na ty body => has_var x ty || has_var x body
  | tLambda na ty body => has_var x ty || has_var x body
  | tLetIn na def def_ty body => has_var x def || has_var x def_ty || has_var x body
  | tApp f args => has_var x f || anyb (has_var x) args
  | tConst c u => false
  | tInd ind u => false
  | tConstruct ind idx u => false
  | tCase ind_and_nbparams type_info discr branches =>
    has_var x type_info || has_var x discr || anyb (fun '(_, e) => has_var x e) branches
  | tProj proj t => has_var x t
  | tFix mfix idx => anyb (fun d => has_var x d.(dtype) || has_var x d.(dbody)) mfix
  | tCoFix mfix idx => anyb (fun d => has_var x d.(dtype) || has_var x d.(dbody)) mfix
  | tInt _ => false
  | tFloat _ => false
  end%bool
)).
Defined.

Definition erase_ctx (C : BasicAst.ident) (Cdecl : context_decl) (Γ : named_ctx) : named_ctx. ltac1:(refine(
  map (fun '(C', d) =>
   if C ==? C' then
     (C, mkdecl d.(decl_name) d.(decl_body) (mkApps <%erased%> [d.(decl_type)]))
   else if has_var C d.(decl_type) : bool then
     let erased_ty :=
       mkApps <%recover%> [mkApps <%@e_map%> [
         Cdecl.(decl_type); <%Prop%>;
         tLambda (nNamed C) Cdecl.(decl_type) d.(decl_type);
         tVar C]]
     in
     (C', mkdecl d.(decl_name) d.(decl_body) erased_ty)
   else (C', d)) Γ
)).
Defined.

Definition rule_of_ind_ctor (ind_ctor : ctor_ty) : GM rule_t. ltac1:(refine(
  let '(name, ctor_ty, arity) := ind_ctor in
  let! ctor_ty :=
    let! name := gensym name in
    named_of [name] ctor_ty
  in
  let '(Γ, rty) := decompose_prod_assum [] ctor_ty in
  let! Γ := named_of_context Γ in
  match rty with
  (* Topdown rule *)
  | tApp (tVar _) [
      tApp (tConst framesD1 []) [
        _univ; _HFrame; tConstruct _univ_ind hole_ut []; _root_univ_ty; tVar C_var as C; lhs];
      tApp (tConst framesD2 []) [_; _; _; _; _; rhs]] =>
    let lhs_vars := vars_of lhs in
    let rec_vars := rec_rhs_vars_of rhs in
    let special_vars := rec_vars in (*∩ lhs_vars in*)
    let! Cdecl := findM C_var Γ in
    ret (mk_rule name ctor_ty arity dTopdown hole_ut (erase_ctx C_var Cdecl Γ) C lhs rhs
      lhs_vars rec_vars special_vars)
  (* Bottomup rule *)
  | tApp (tConst _BottomUp []) [_; tApp (tVar _) [
      tApp (tConst _framesD []) [
        _univ; _HFrame; tConstruct _univ_ind hole_ut []; _root_univ_ty; tVar C_var as C; lhs];
      tApp (tConst _ []) [_; _; _; _; _; rhs]]] =>
    let lhs_vars := vars_of lhs in
    let rec_vars := rec_rhs_vars_of rhs in
    let special_vars := rec_vars ∩ lhs_vars in
    let! Cdecl := findM C_var Γ in
    ret (mk_rule name ctor_ty arity dBottomup hole_ut (erase_ctx C_var Cdecl Γ) C lhs rhs
      lhs_vars rec_vars special_vars)
  | rty => raise ("rule_of_ind_ctor: " +++ string_of_term rty)
  end
)).
Defined.

Definition parse_rel_pure (ind : inductive) (mbody : mutual_inductive_body)
           (body : one_inductive_body) : GM rules_t. ltac1:(refine(
  let! rules :=
    mapiM
      (fun i ctor => rule_of_ind_ctor ctor)
      body.(ind_ctors)
  in
  match rules with
  | [] => raise "parse_rel: empty relation"
  | {| rΓ := Γ; rC := tVar C |} :: _ =>
    let! Cty := findM C Γ in
    match Cty.(decl_type) with
    | tApp (tConst _erased []) [
        tApp (tConst _frames_t []) [
          tInd univ []; HFrame; _hole; tConstruct _univ root []]] =>
      ret (mk_rules ind rules univ root HFrame)
    | _ => raise ("parse_rel: C's type illformed: " +++ string_of_term Cty.(decl_type))
    end
  | _ :: _ => raise "parse_rel: C not tRel"
  end
)).
Defined.

Definition parse_rel {A} (ind : A) : TemplateMonad rules_t :=
  ind <- tmQuote ind ;;
  match ind with
  | tInd ind [] =>
    mbody <- tmQuoteInductive ind.(inductive_mind) ;;
    match mbody.(ind_bodies) with
    | [body] => runGM (parse_rel_pure ind mbody body)
    | _ => tmFail "rel_constr_types: relation has more than one body"
    end
  | _ => tmFail "rel_constr_types: not an inductive relation"
  end.

End GoalGeneration.

Ltac runGM n m k :=
  let res := eval cbv in (runGM' n m) in
  match res with
  | inl ?e => fail 10 "runGM:" e
  | inr (?x, ?n) => k x n
  end.

Ltac parse_rel n R k :=
  run_template_program (
    ind <- tmQuote R ;;
    match ind with
    | tInd ind [] =>
      mbody <- tmQuoteInductive ind.(inductive_mind) ;;
      match mbody.(ind_bodies) with
      | [body] => ret (ind, mbody, body)
      | _ => tmFail "rel_constr_types: relation has more than one body"
      end
    | _ => tmFail "rel_constr_types: not an inductive relation"
    end) ltac:(fun pack =>
  match pack with
  | (?ind, ?mbody, ?body) =>
    runGM n (parse_rel_pure ind mbody body) k
  end).

(* ---------- Types of helpers for computing preconditions/intermediate values ---------- *)

Section GoalGeneration.

Context
  (aux_data : aux_data_t)
  (typename := aux_data.(aTypename))
  (ind_info := aux_data.(aIndInfo))
  (graph := aux_data.(aGraph))
  (univ_of_tyname := aux_data.(aUnivOfTyname))
  (frames_of_constr := aux_data.(aFramesOfConstr)).
Context
  (rules : rules_t)
  (rw_univ := rules.(rUniv))
  (HFrame := rules.(rHFrame))
  (root := rules.(rRootU))
  (* specialize to univD rw_univ -> univD rw_univ -> Set *)
  (frames_t := mkApps <%@frames_t%> [tInd rw_univ []; HFrame])
  (* specialize to rw_univ -> Set *)
  (univD := mkApps <%@univD%> [tInd rw_univ []; HFrame]) 
  (mk_univ := fun n => tConstruct rw_univ n []).
Context
  (D I_D R I_R S I_S : term)
  (Delay := mkApps <%@Delay%> [tInd rw_univ []; HFrame; D; I_D])
  (Param := mkApps <%@Param%> [tInd rw_univ []; HFrame; mk_univ root; R; I_R])
  (State := mkApps <%@State%> [tInd rw_univ []; HFrame; mk_univ root; S; I_S]).
Context (delayD : term) (* specialized to forall {A} (e : univD A), Delay e -> univD A *).

Definition gen_extra_vars_ty (rule : rule_t) : GM term :=
  match rule.(rDir) with
  | dTopdown =>
    let hole := rule.(rHoleU) in
    let lhs := rule.(rLhs) in
    let lhs_vars := rule.(rLhsVars) in
    (* Currently, the context rΓ contains (lhs vars ∪ rhs vars) in unspecified order.
       We will rearrange it to be (lhs vars .. rhs vars ..). *)
    let ctx := map (fun '(x, decl) => (member x lhs_vars, x, decl)) rule.(rΓ) in
    let '(lhs_ctx, rhs_ctx) := partition (fun '(in_lhs, _, _) => in_lhs) ctx in
    (* rhs_ctx also contains C: C will actually be introduced in the outer scope
       already. We'll just borrow its name. *)
    let! C :=
      match rule.(rC) with
      | tVar C => ret C
      | t => raise ("gen_extra_vars_ty: expected tVar, got: " +++ string_of_term t)
      end
    in
    (* Filter to drop C *)
    let rhs_ctx := filter (fun '(_, x, decl) => negb (x ==? C)) rhs_ctx in
    let rhs_ctx := map (fun '(_, x, decl) => (x, decl)) rhs_ctx in
    let! Ans := gensym "Ans" in
    let! C_ok := gensym "C_ok" in
    let! d := gensym "d" in
    let! r := gensym "r" in
    let! s := gensym "s" in
    let hole := mk_univ hole in
    let root := mk_univ root in
    let rule_name := quote_string rule.(rName) in
    let rΓ := filter (fun '(x, decl) => negb (x ==? C)) rule.(rΓ) in
    let! '(extra_vars, σ) :=
      let Γ := map_of_list rΓ in
      mfoldM
        (fun x fn_call '(extras, σ) =>
          let! x' := gensym (remove_sigils' x) in
          let! md' := if member x rule.(rSpecialVars) then Some <$> gensym "d" else ret None in
          let! decl := findM' x Γ "special_var" in
          let ty := decl.(decl_type) in
          let! tyname := mangle ind_info ty in
          let! univ_n := findM' tyname univ_of_tyname "applicable: univ_n" in
          let u := mk_univ (N.to_nat univ_n) in
          ret ((x, fn_call, x', md', ty, u) :: extras, insert x x' σ))
        ([], empty) (rule.(rSpecialVars) ∪ (map (fun '(s, _) => (s, None)) rule.(rLhsVars)))
    in
    let lhs' := rename σ rule.(rLhs) in
    let ctx_ty := mkApps frames_t [hole; root] in
    ret (fn (mkApps <%ExtraVars%> [rule_name])
      (tProd (nNamed Ans) type0 
      (tProd (nNamed C) (mkApps <%erased%> [ctx_ty])
      (tProd (nNamed C_ok) (mkApps <%@e_ok%> [ctx_ty; tVar C])
      (fold_right
        (fun '(x, fn_call, x', md', xty, u) ty =>
          if member x rule.(rLhsVars)
          then tProd (nNamed x') xty ty
          else ty)
        (tProd (nNamed d) (mkApps Delay [hole; lhs'])
        (tProd (nNamed r) (mkApps Param [hole; tVar C])
        (tProd (nNamed s) (mkApps State [hole; tVar C; mkApps delayD [hole; lhs'; tVar d]])
        (fn (fn (mkApps <%Success%> [rule_name])
          (fold_right
            (fun '(x, fn_call, x', md', xty, u) ty =>
              (if member x rule.(rLhsVars) then tProd (nNamed x) xty else tProd (nNamed x') xty)
              match md' with
              | Some d' => tProd (nNamed d') (mkApps Delay [u; tVar x']) ty
              | None => ty
              end)
            (it_mkProd_or_LetIn (drop_names rhs_ctx)
            (fn (mkApps <%@eq%> [mkApps univD [hole]; mkApps delayD [hole; lhs'; tVar d]; rule.(rLhs)])
            (fold_right
              (fun '(x, fn_call, x', md', xty, u) ty =>
                match md' with
                | Some d' =>
                  let lhs :=
                    match fn_call with
                    | Some fn_call => mkApps fn_call [tVar x]
                    | None => tVar x
                    end
                  in
                  fn (mkApps <%@eq%> [xty; lhs; mkApps delayD [u; tVar x'; tVar d']]) ty
                | None => ty
                end)
              (fn (mkApps Param [hole; tVar C]) (fn (mkApps State [hole; tVar C; rule.(rRhs)]) (tVar Ans)))
              extra_vars)))
            extra_vars))
        (fn (fn (mkApps <%Failure%> [rule_name]) (tVar Ans))
        (tVar Ans))))))
        extra_vars)))))
  | dBottomup =>
    let hole := rule.(rHoleU) in
    let lhs := rule.(rLhs) in
    let rhs := rule.(rRhs) in
    let lhs_vars := rule.(rLhsVars) in
    (* Currently, the context rΓ contains (lhs vars ∪ rhs vars) in unspecified order.
       We will rearrange it to be (lhs vars .. rhs vars ..). *)
    let ctx := map (fun '(x, decl) => (member x lhs_vars, x, decl)) rule.(rΓ) in
    let '(lhs_ctx, rhs_ctx) := partition (fun '(in_lhs, _, _) => in_lhs) ctx in
    (* rhs_ctx also contains C: C will actually be introduced in the outer scope
       already. We'll just borrow its name. *)
    let! C :=
      match rule.(rC) with
      | tVar C => ret C
      | t => raise ("gen_extra_vars_ty: expected tVar, got: " +++ string_of_term t)
      end
    in
    (* Filter to drop C *)
    let rhs_ctx := filter (fun '(_, x, decl) => negb (x ==? C)) rhs_ctx in
    let! Ans := gensym "Ans" in
    let! C_ok := gensym "C_ok" in
    let! r := gensym "r" in
    let! s := gensym "s" in
    let hole := mk_univ hole in
    let root := mk_univ root in
    let rule_name := quote_string rule.(rName) in
    let ctx_ty := mkApps frames_t [hole; root] in
    ret (fn (mkApps <%ExtraVars%> [rule_name])
      (tProd (nNamed Ans) type0 
      (tProd (nNamed C) (mkApps <%erased%> [ctx_ty])
      (tProd (nNamed C_ok) (mkApps <%@e_ok%> [ctx_ty; tVar C])
      (fold_right
        (fun '(_, s, d) ty => tProd (nNamed s) d.(decl_type) ty)
         (tProd (nNamed r) (mkApps Param [hole; tVar C])
         (tProd (nNamed s) (mkApps State [hole; tVar C; lhs])
         (fn
           (fn (mkApps <%Success%> [rule_name]) (fold_right
             (fun '(_, s, d) ty => tProd (nNamed s) d.(decl_type) ty)
             (fn (mkApps Param [hole; tVar C]) (fn (mkApps State [hole; tVar C; rhs]) (tVar Ans)))
             (rev rhs_ctx)))
           (fn (fn (mkApps <%Failure%> [rule_name]) (tVar Ans)) (tVar Ans)))))
        (rev lhs_ctx))))))
  end.

Definition gen_extra_vars_tys : GM (list term) :=
  mapM
    (fun r => let! ty := gen_extra_vars_ty r in indices_of [] ty)
    (* (fun r => gen_extra_vars_ty r) *)
    rules.(rRules).

End GoalGeneration.

(* ---------- Types of helpers for taking a single step ---------- *)

Section GoalGeneration.

Context
  (rules : rules_t)
  (rw_rel := tInd rules.(rR) [])
  (rw_univ_i := rules.(rUniv))
  (rw_univ := tInd rw_univ_i [])
  (mk_univ := fun n => tConstruct rw_univ_i n [])
  (HFrame := rules.(rHFrame))
  (root := mk_univ rules.(rRootU)).
Context (fueled metric : term).
Context
  (R I_R S I_S : term)
  (Param := mkApps <%@Param%> [tInd rw_univ_i []; HFrame; root; R; I_R])
  (State := mkApps <%@State%> [tInd rw_univ_i []; HFrame; root; S; I_S])
  (* specialize to univD rw_univ -> univD rw_univ -> Set *)
  (frames_t := mkApps <%@frames_t%> [tInd rw_univ_i []; HFrame])
  (* specialize to Fuel fueled -> forall A, erased (frames_t A root) -> univD A -> Set *)
  (rw_for := mkApps <%@rw_for%> [rw_univ; HFrame; root; fueled; metric; rw_rel; R; I_R; S; I_S]).

Definition gen_run_rule_ty (r : rule_t) : GM term. ltac1:(refine(
  let! emetric := gensym "emetric" in
  let! fuel := gensym "fuel" in
  let! C_ok := gensym "C_ok" in
  let hole := mk_univ r.(rHoleU) in
  ret
    (fn (mkApps <%RunRule%> [quote_string r.(rName)])
    (tProd (nNamed fuel) (mkApps <%Fuel%> [fueled])
    (it_mkProd_or_LetIn (drop_names r.(rΓ))
    (tProd (nNamed C_ok) (mkApps <%@e_ok%> [mkApps frames_t [hole; root]; r.(rC)])
    (fn (mkApps Param [hole; r.(rC)])
    (fn (mkApps State [hole; r.(rC); r.(rRhs)])
    (fn (mkApps rw_for [tVar fuel; hole; r.(rC); r.(rRhs)])
    (mkApps rw_for [tVar fuel; hole; r.(rC); r.(rLhs)]))))))))
)).
Defined.

Definition gen_run_rule_tys : GM (list term) :=
  mapM (fun t => let! t := gen_run_rule_ty t in indices_of [] t) rules.(rRules).

End GoalGeneration.

(* ---------- Types of helpers for incrementalizing delayed computation ---------- *)

Section GoalGeneration.

Context
  (aux_data : aux_data_t)
  (qual := aux_data.(aQual))
  (decls := aux_data.(aEnv))
  (typename := aux_data.(aTypename)) (g := aux_data.(aGraph))
  (univ_of_tyname := aux_data.(aUnivOfTyname)).
Context
  (rules : rules_t)
  (rw_univ := rules.(rUniv))
  (HFrame := rules.(rHFrame))
  (root := rules.(rRootU))
  (mk_univ := fun n => tConstruct rw_univ n []).
Context
  (D I_D : term)
  (Delay := mkApps <%@Delay%> [tInd rw_univ []; HFrame; D; I_D]).
Context
  (delayD : term) (* specialized to forall {A}, univD A -> delay_t -> univD A *).

Definition gen_constr_delay_ty (c : string) : GM term. ltac1:(refine(
  let! '(n, children, rtyname) := findM c g.(mgChildren) in
  let! rty := findM rtyname g.(mgTypes) in
  let! '(ind, pars) := decompose_ind decls rty in
  let ctr := mkApps (tConstruct ind (N.to_nat n) []) pars in
  let univ_name := (qual, snd typename +++ "_univ") in
  let! univ_n := findM rtyname univ_of_tyname in
  let univ := tConstruct (mkInd univ_name 0) (N.to_nat univ_n) [] in
  let! children :=
    mapM
      (fun tyname =>
        let! ty := findM tyname g.(mgTypes) in
        let! old := gensym (abbreviate tyname) in
        let! univ_n := findM tyname univ_of_tyname in
        let univ := tConstruct (mkInd univ_name 0) (N.to_nat univ_n) [] in
        let atomic := member tyname g.(mgAtoms) in
        let! new := if atomic then gensym (abbreviate tyname) else gensym "d" in
        ret (tyname, old, new, ty, univ, atomic))
      children
  in
  let! Ans := gensym "Ans" in
  let! d := gensym "d" in
  let ctr_ty := fold_right (fun '(_, _, _, ty, _, _) res => fn ty res) rty children in 
  let before_delayD := mkApps ctr (map (fun '(_, old, _, _, _, _) => tVar old) children) in
  ret (fn (mkApps <%@ConstrDelay%> [ctr_ty; ctr]) (tProd (nNamed Ans) type0
    (fold_right
      (fun '(_, old, _, ty, _, _) res => tProd (nNamed old) ty res)
      (tProd (nNamed d) (mkApps Delay [univ; before_delayD])
      (fn
        (fold_right
          (fun '(_, old, new, ty, univ, atomic) res =>
            tProd (nNamed new) (if (atomic : bool) then ty else mkApps Delay [univ; tVar old]) res)
          (fn
            (mkApps <%@eq%> [rty;
               mkApps delayD [univ; before_delayD; tVar d];
               mkApps ctr (map
                 (fun '(tyname, old, new, ty, _, atomic) => 
                   if atomic : bool then tVar new
                   else
                     let n := find_d tyname 0 univ_of_tyname in
                     let univ := tConstruct (mkInd univ_name 0) (N.to_nat n) [] in
                     mkApps delayD [univ; tVar old; tVar new])
                 children)])
            (tVar Ans))
          children)
        (tVar Ans)))
      children)))
)).
Defined.

Definition gen_constr_delay_tys : GM (list term) :=
  let constrs :=
    fold_right
      (fun '(_, cs) m =>
         fold_right (fun c m => insert c tt m) m cs)
      empty
      (list_of_map g.(mgConstrs))
  in
  mapM
    (fun constr => let! ty := gen_constr_delay_ty constr in indices_of [] ty)
    (map fst (list_of_map constrs)).

End GoalGeneration.

(* ---------- Types of smart constructors ---------- *)

Section GoalGeneration.

Context
  (aux_data : aux_data_t)
  (qual := aux_data.(aQual))
  (decls := aux_data.(aEnv))
  (typename := aux_data.(aTypename)) (graph := aux_data.(aGraph))
  (univ_of_tyname := aux_data.(aUnivOfTyname))
  (frames_of_constr := aux_data.(aFramesOfConstr)).
Context
  (rules : rules_t)
  (rw_rel := tInd rules.(rR) [])
  (rw_univ_i := rules.(rUniv))
  (rw_univ := tInd rules.(rUniv) [])
  (mk_univ := fun n => tConstruct rw_univ_i n [])
  (HFrame := rules.(rHFrame))
  (root := mk_univ rules.(rRootU)).
Context (fueled metric : term).
Context
  (R I_R S I_S : term)
  (Param := mkApps <%@Param%> [tInd rw_univ_i []; HFrame; root; R; I_R])
  (State := mkApps <%@State%> [tInd rw_univ_i []; HFrame; root; S; I_S]).
Context
  (* specialize to rw_univ -> rw_univ -> Set *)
  (frames_t := mkApps <%@frames_t%> [rw_univ; HFrame])
  (* specialize to rw_univ -> Set *)
  (univD := mkApps <%@univD%> [rw_univ; HFrame]) 
  (* specialize to Fuel fueled -> forall A, erased (frames_t A root) -> univD A -> Set *)
  (rw_for := mkApps <%@rw_for%> [rw_univ; HFrame; root; fueled; metric; rw_rel; R; I_R; S; I_S])
  (frame_ind := mkInd (qual, snd typename +++ "_frame_t") 0)
  (frame_t := tInd frame_ind [])
  (frame_cons := fun n => tConstruct frame_ind n [])
  (univ_ind := mkInd (qual, snd typename +++ "_univ") 0)
  (univ_cons := fun n => tConstruct univ_ind n [])
  (* Specialized to forall A B C, frame_t A B -> frames_t B C -> frames_t A C *)
  (frames_cons := mkApps <%@frames_cons%> [rw_univ; frame_t]).

Definition gen_smart_constr_ty (c : string) : GM term. ltac1:(refine(
  let! '(n_constr, child_tys, rty) := findM' c graph.(mgChildren) "children" in
  let n_constr := N.to_nat n_constr in
  let! rty_term := findM' rty graph.(mgTypes) "types" in
  let! '(ind, pars) := decompose_ind decls rty_term in
  let constr := mkApps (tConstruct ind n_constr []) pars in
  let frames := find_d c [] frames_of_constr in
  let n_frames := map hIndex frames in
  let get_univ_of ty :=
    let! n := findM' ty univ_of_tyname "univ_of_tyname" in
    ret (univ_cons (N.to_nat n))
  in
  let! univ_rty := get_univ_of rty in
  let! xtys := mapM (fun ty => let! x := gensym (abbreviate ty) in ret (x, ty)) child_tys in
  let! xutfs :=
    mapM
      (fun '(n, (lxtys, (x, ty), rxtys)) =>
        let lxs := map fst lxtys in
        let rxs := map fst rxtys in
        let! univ := get_univ_of ty in
        let! ty_term := findM ty graph.(mgTypes) in
        ret (x, univ, ty_term, frame_cons n, lxs, rxs))
      (combine n_frames (holes_of xtys))
  in
  let! fuel := gensym "fuel" in
  let! C := gensym "C" in
  let! C_ok := gensym "C_ok" in
  let C_ty := mkApps frames_t [univ_rty; root] in
  let constr_ty := fold_right (fun '(_, _, ty, _, _, _) res => fn ty res) rty_term xutfs in 
  ret (fn (mkApps <%@SmartConstr%> [constr_ty; constr])
    (tProd (nNamed fuel) (mkApps <%Fuel%> [fueled])
    (tProd (nNamed C) (mkApps <%erased%> [C_ty])
    (tProd (nNamed C_ok) (mkApps <%@e_ok%> [C_ty; tVar C])
    (fold_right
      (fun '(x, _, t, _, _, _) ty => tProd (nNamed x) t ty)
      (fold_right
        (fun '(x, u, t, f, lxs, rxs) ty =>
          fn
            (fn
              (mkApps <%@SmartConstrCase%> [
                rty_term; mkApps <%@frameD%> [
                  rw_univ; HFrame; u; univ_rty;
                  mkApps f (map tVar (lxs ++ rxs)); tVar x]])
              (fold_right
                (fun '(x', _, t, _, _, _) ty => if x ==? x' then ty else tProd (nNamed x') t ty)
                (let mk_ctx_t u := mkApps frames_t [u; root] in
                 mkApps rw_for [
                   tVar fuel;
                   u; mkApps <%@e_map%> [
                     mk_ctx_t univ_rty; mk_ctx_t u;
                     tLambda (nNamed C) (mk_ctx_t univ_rty) (mkApps frames_cons [
                       u; univ_rty; root; 
                       mkApps f (map tVar (lxs ++ rxs)); tVar C]);
                     tVar C];
                   tVar x])
                xutfs))
            ty)
        (mkApps rw_for [
          tVar fuel;
          univ_rty; tVar C; 
          mkApps constr (map (fun '(x, _, _, _, _, _) => tVar x) xutfs)])
        (rev xutfs))
      xutfs)))))
)).
Defined.

Definition gen_smart_constr_tys : GM (list term) :=
  let constrs :=
    fold_right
      (fun '(_, cs) m =>
         fold_right (fun c m => insert c tt m) m cs)
      empty
      (list_of_map graph.(mgConstrs))
  in
  mapM
    (fun constr => let! ty := gen_smart_constr_ty constr in indices_of [] ty)
    (map fst (list_of_map constrs)).

End GoalGeneration.

(* ---------- Types of pattern matching combinators ---------- *)

Fixpoint unwords (ws : list string) : string :=
  match ws with
  | [] => ""
  | [s] => s
  | s :: ss => s +++ " " +++ unwords ss
  end.

(* Elaborate a single pattern match
     match e1, e2, .. with
     | c x (d y ..) .., pat2, .. => success
     | _ => failure
     end : ret_ty
   into the case tree
     match e with
     | c x fresh .. =>
       match fresh with
       | d y .. =>
         match e2 with
         | pat2 => ..
         | .. => failure
         end
       | ..
       | .. => failure
       end
     | ..
     | .. => failure
     end *)

Definition gen_case_tree (ind_info : ind_info) (epats : list (term × term))
           (ret_ty success failure : term) : GM term. ltac1:(refine(
  let find_ind ind := findM' ind.(inductive_mind) ind_info "find_ind" in
  let fix go F epats :=
    match F with O => raise "gen_case_tree: OOF" | S F =>
      let go := go F in
      let go_pat e ind n_constr args epats :=
        let! '(mbody, inds, _) := find_ind ind in
        let! body := nthM_nat ind.(inductive_ind) mbody.(ind_bodies) in
        let nparams := mbody.(ind_npars) in
        let pars := firstn nparams args in
        let args := skipn nparams args in
        let! constrs :=
          mapM
            (fun '(name, constr_ty, arity) =>
              let '(xs, ts, rty) := decompose_prod constr_ty in
              let xs := skipn nparams xs in
              let ts := skipn nparams ts in
              let constr_ty := fold_right (fun '(x, t) ty => tProd x t ty) rty (combine xs ts) in
              let constr_ty := subst0 (rev pars ++ rev_map (fun ind => tInd ind []) inds) constr_ty in
              let! constr_ty := named_of [] constr_ty in
              ret (name, constr_ty, arity))
            body.(ind_ctors)
        in
        tCase ((ind, nparams), Relevant) (tLambda nAnon (mkApps (tInd ind []) pars) ret_ty) e <$>
          mapiM_nat
            (fun i '(_, constr_ty, arity) =>
              let '(xs, ts, rty) := decompose_prod constr_ty in
              let! xs :=
                if i ==? n_constr then
                  mapM
                    (fun '(x, arg) =>
                      match binder_name x, arg with
                      | BasicAst.nAnon, _ => raise "gen_case_tree: name anon"
                      | _, tVar x => ret x
                      | BasicAst.nNamed x, _ => ret x
                      end)
                    (combine xs args)
                else
                  mapM
                    (fun x =>
                      match binder_name x with
                      | BasicAst.nAnon => raise "gen_case_tree: name anon"
                      | BasicAst.nNamed x => ret x
                      end)
                    xs
              in
              let! arm :=
                 if i ==? n_constr
                 then go (combine (map tVar xs) args ++ epats)
                 else ret failure
              in
              let arm :=
                fold_right
                  (fun '(x, t) arm => tLambda (nNamed x) t arm)
                  arm (combine xs ts)
              in
              ret (arity, arm))
            constrs
      in
      match epats with
      | [] => ret success
      | (e, tConstruct ind n_constr []) :: epats => go_pat e ind n_constr [] epats
      | (e, tApp (tConstruct ind n_constr []) args) :: epats => go_pat e ind n_constr args epats
      | (e, tVar _) :: epats => go epats
      | (_, pat) :: _ => raise ("gen_case_tree: bad pat: " +++ string_of_term pat)
      end
    end
  in go 100%nat epats
)).
Defined.

Section GoalGeneration.

Context
  (aux_data : aux_data_t)
  (decls := aux_data.(aEnv))
  (typename := aux_data.(aTypename))
  (ind_info := aux_data.(aIndInfo))
  (graph := aux_data.(aGraph))
  (univ_of_tyname := aux_data.(aUnivOfTyname))
  (frames_of_constr := aux_data.(aFramesOfConstr)).
Context
  (rules : rules_t)
  (rw_rel := tInd rules.(rR) [])
  (rw_univ_i := rules.(rUniv))
  (rw_univ := tInd rw_univ_i [])
  (mk_univ := fun n => tConstruct rw_univ_i n [])
  (HFrame := rules.(rHFrame))
  (root := mk_univ rules.(rRootU))
  (* specialize to univD rw_univ -> univD rw_univ -> Set *)
  (frames_t := mkApps <%@frames_t%> [rw_univ; HFrame])
  (* specialize to rw_univ -> Set *)
  (univD := mkApps <%@univD%> [rw_univ; HFrame]).
Context
  (D I_D R I_R S I_S : term)
  (Delay := mkApps <%@Delay%> [tInd rw_univ_i []; HFrame; D; I_D])
  (Param := mkApps <%@Param%> [tInd rw_univ_i []; HFrame; root; R; I_R])
  (State := mkApps <%@State%> [tInd rw_univ_i []; HFrame; root; S; I_S]).
Context (delayD : term) (* specialized to forall {A} (e : univD A), Delay e -> univD A *).

Definition gen_topdown_ty (t_univ_i : N) : GM term. ltac1:(refine(
  let n_univs := mfold (fun u n m => insert n u m) empty univ_of_tyname in
  let! t_tyname := findM'' t_univ_i n_univs "t_univ_i" in
  let t_univ_i := N.to_nat t_univ_i in
  let! t_ty := findM' t_tyname graph.(mgTypes) "t_tyname" in
  let! '(ind, pars) := decompose_ind decls t_ty in
  let! Ans := gensym "Ans" in
  let! d := gensym "d" in
  let! C := gensym "C" in
  let! C_ok := gensym "C_ok" in
  let! e := gensym (abbreviate t_tyname) in
  let! r := gensym "r" in
  let! s := gensym "s" in
  let t_univ := mk_univ t_univ_i in
  let! constrs := findM' t_tyname graph.(mgConstrs) "t_tyname" in
  let! congruences :=
    mapM
      (fun c =>
        let! '(index, arg_tynames, rty) := findM' c graph.(mgChildren) "constr" in
        let! xts :=
          mapM
            (fun tyname =>
              let atomic := member tyname graph.(mgAtoms) in
              let abbrev_tyname := abbreviate tyname in
              let! x := gensym abbrev_tyname in
              let! x' := gensym abbrev_tyname in
              let! md := if atomic then ret None else Some <$> gensym "d" in
              let! t := findM tyname graph.(mgTypes) in
              let! univ_n := findM tyname univ_of_tyname in
              let u := mk_univ (N.to_nat univ_n) in
              ret (md, x, x', t, u))
            arg_tynames
        in
        let! rty := findM rty graph.(mgTypes) in
        let constr := mkApps (tConstruct ind (N.to_nat index) []) pars in
        let constr_ty := fold_right (fun '(_, _, _, t, _) res => fn t res) rty xts in
        let pat := mkApps constr (map (fun '(_, x, _, _, _) => tVar x) xts) in
        let! header :=
          gen_case_tree ind_info [(tVar e, pat)] type0
            (mkApps <%@Congruence%> [constr_ty; constr])
            <%Impossible%>
        in
        ret (fn (mkApps <%@InspectCaseCongruence%> [constr_ty; constr]) (fn header
          (fold_right
            (fun '(md, x, x', t, u) ty =>
              tProd (nNamed x) t
              (match md with
               | Some d => tProd (nNamed d) (mkApps Delay [u; tVar x]) ty
               | None => tProd (nNamed x') t ty
               end))
            (fn
              (mkApps <%@eq%> [rty;
                mkApps delayD [t_univ; tVar e; tVar d];
                mkApps constr (map
                  (fun '(md, x, x', t, u) =>
                    match md with
                    | None => tVar x'
                    | Some d => mkApps delayD [u; tVar x; tVar d]
                    end)
                  xts)])
              (fn
                (mkApps <%@eq%> [rty; 
                  tVar e;
                  mkApps constr (map (fun '(md, x, x', t, u) => tVar x) xts)])
                (tVar Ans)))
            xts))))
      constrs
  in
  let applicable :=
    filter
      (fun r => match r.(rDir) with dTopdown => r.(rHoleU) ==? t_univ_i | dBottomup => false end)
      rules.(rRules)
  in
  let! applicable :=
    mapM
      (fun r =>
        (* We can't reuse the trick of borrowing the name for C, because this type will have
           multiple continuations corresponding to multiple rules with different names for C.
           So in each rule we have to replace its personal name for C with the C in the outer
           scope. *)
        let! localC :=
          match r.(rC) with
          | tVar C => ret C
          | t => raise ("gen_extra_vars_ty: expected tVar, got: " +++ string_of_term t)
          end
        in
        let rΓ := filter (fun '(x, decl) => negb (x ==? localC)) r.(rΓ) in
        let σ := sing localC C in
        let rΓ := map (on_snd (map_decl (rename σ))) rΓ in
        let! '(extra_vars, σ) :=
          let Γ := map_of_list rΓ in
          mfoldM
            (fun x fn_call '(extras, σ) =>
              let! x' := gensym (remove_sigils' x) in
              let! md' := if member x r.(rSpecialVars) then Some <$> gensym "d" else ret None in
              let! decl := findM' x Γ "special_var" in
              let ty := decl.(decl_type) in
              let! tyname := mangle ind_info ty in
              let! univ_n := findM' tyname univ_of_tyname "applicable: univ_n" in
              let u := mk_univ (N.to_nat univ_n) in
              ret ((x, fn_call, x', md', ty, u) :: extras, insert x x' σ))
            ([], empty) (r.(rSpecialVars) ∪ map (fun '(x, _) => (x, None)) r.(rLhsVars))
        in
        let old_lhs := rename σ r.(rLhs) in
        let! header :=
          gen_case_tree ind_info [(tVar e, r.(rLhs))] type0 
            (mkApps <%Active%> [quote_string r.(rName)])
            <%Impossible%>
        in
        ret (fn (mkApps <%InspectCaseRule%> [quote_string r.(rName)]) (fn header
          (it_mkProd_or_LetIn (drop_names rΓ)
          (fold_right
            (fun '(x, fn_call, x', md', xty, u) ty =>
              tProd (nNamed x') xty
              (match md' with
               | Some d' => tProd (nNamed d') (mkApps Delay [u; tVar x']) ty
               | None => ty
               end))
            (fn (mkApps <%@eq%> [mkApps univD [t_univ]; mkApps delayD [t_univ; tVar e; tVar d]; r.(rLhs)])
            (fold_right
              (fun '(x, fn_call, x', md', xty, u) ty =>
                match md' with
                | Some d' =>
                  let lhs :=
                    match fn_call with
                    | Some fn_call => mkApps fn_call [tVar x]
                    | None => tVar x
                    end
                  in
                  fn (mkApps <%@eq%> [xty; lhs; mkApps delayD [u; tVar x'; tVar d']]) ty
                | None => ty
                end)
              (fn (mkApps <%@eq%> [mkApps univD [t_univ]; tVar e; old_lhs])
              (fn (mkApps Param [t_univ; tVar C]) (fn (mkApps State [t_univ; tVar C; r.(rRhs)]) (tVar Ans))))
              extra_vars))
            extra_vars)))))
      applicable
  in
  let ctx_ty := mkApps frames_t [t_univ; root] in
  ret (fn (mkApps <%@Topdown%> [rw_univ; t_univ])
    (tProd (nNamed Ans) type0 
    (tProd (nNamed C) (mkApps <%erased%> [ctx_ty])
    (tProd (nNamed C_ok) (mkApps <%@e_ok%> [ctx_ty; tVar C])
    (tProd (nNamed e) (mkApps univD [t_univ])
    (tProd (nNamed d) (mkApps Delay [t_univ; tVar e])
    (tProd (nNamed r) (mkApps Param [t_univ; tVar C]) 
    (tProd (nNamed s) (mkApps State [t_univ; tVar C; mkApps delayD [t_univ; tVar e; tVar d]])
    (fold_right fn (fold_right fn (tVar Ans) congruences) applicable)))))))))
)).
Defined.

Definition gen_bottomup_ty (t_univ_i : N) : GM term. ltac1:(refine(
  let n_univs := mfold (fun u n m => insert n u m) empty univ_of_tyname in
  let! t_tyname := findM'' t_univ_i n_univs "t_univ_i" in
  let t_univ_i := N.to_nat t_univ_i in
  let! t_ty := findM' t_tyname graph.(mgTypes) "t_tyname" in
  let! '(ind, pars) := decompose_ind decls t_ty in
  let! Ans := gensym "Ans" in
  let! C := gensym "C" in
  let! C_ok := gensym "C_ok" in
  let! e := gensym (abbreviate t_tyname) in
  let! r := gensym "r" in
  let! s := gensym "s" in
  let t_univ := mk_univ t_univ_i in
  let! constrs := findM' t_tyname graph.(mgConstrs) "t_tyname" in
  let applicable :=
    filter
      (fun r => match r.(rDir) with dBottomup => r.(rHoleU) ==? t_univ_i | dTopdown => false end)
      rules.(rRules)
  in
  let! applicable :=
    mapM
      (fun r =>
        let! localC :=
          match r.(rC) with
          | tVar C => ret C
          | t => raise ("gen_extra_vars_ty: expected tVar, got: " +++ string_of_term t)
          end
        in
        let rΓ := filter (fun '(x, decl) => negb (x ==? localC)) r.(rΓ) in
        let σ := sing localC C in
        let rΓ := map (on_snd (map_decl (rename σ))) rΓ in
        let! header :=
          gen_case_tree ind_info [(tVar e, r.(rLhs))] type0 
            (mkApps <%Active%> [quote_string r.(rName)])
            <%Impossible%>
        in
        ret (fn (mkApps <%InspectCaseRule%> [quote_string r.(rName)]) (fn header
          (it_mkProd_or_LetIn (drop_names rΓ)
          (fn (mkApps <%@eq%> [mkApps univD [t_univ]; tVar e; r.(rLhs)])
          (fn (mkApps State [t_univ; tVar C; r.(rRhs)]) (tVar Ans)))))))
      applicable
  in
  let ctx_ty := mkApps frames_t [t_univ; root] in
  ret (fn (mkApps <%@Bottomup%> [rw_univ; t_univ])
    (tProd (nNamed Ans) type0 
    (tProd (nNamed C) (mkApps <%erased%> [ctx_ty])
    (tProd (nNamed C_ok) (mkApps <%@e_ok%> [ctx_ty; tVar C])
    (tProd (nNamed e) (mkApps univD [t_univ])
    (tProd (nNamed r) (mkApps Param [t_univ; tVar C]) 
    (tProd (nNamed s) (mkApps State [t_univ; tVar C; tVar e])
    (fold_right fn (fn (fn <%Fallback%> (tVar Ans)) (tVar Ans)) (rev applicable)))))))))
)).
Defined.

Definition gen_inspect_tys : GM (list term × list term). ltac1:(refine(
  let! ns :=
    foldrM
      (fun '(ty, _) ns =>
        if member ty graph.(mgAtoms) then ret ns else
        let! n := findM ty univ_of_tyname in
        ret (n :: ns))
      [] (list_of_map graph.(mgTypes))
  in
  let! tynames :=
    foldrM
      (fun '(ty, _) ns =>
        if member ty graph.(mgAtoms) then ret ns else
        ret (ty :: ns))
      [] (list_of_map graph.(mgTypes))
  in
  let! topdown_named := mapM gen_topdown_ty ns in
  let! bottomup_named := mapM gen_bottomup_ty ns in
  let! topdown_tys := mapM (indices_of []) topdown_named in
  let! bottomup_tys := mapM (indices_of []) bottomup_named in
  ret (topdown_tys, bottomup_tys)
)).
Defined.

End GoalGeneration.

(* ---------- Toplevel tactic to generate the above ---------- *)

Section GoalGeneration.

Context (aux : aux_data_t) (rules : rules_t) (fueled metric D I_D R I_R S I_S delayD : term).

Definition gen_all : GM (RwObligations term). ltac1:(refine(
  let! extra_vars := gen_extra_vars_tys aux rules D I_D R I_R S I_S delayD in
  let! run_rules := gen_run_rule_tys rules fueled metric R I_R S I_S in
  let! constr_delays := gen_constr_delay_tys aux rules D I_D delayD in
  let! smart_constrs := gen_smart_constr_tys aux rules fueled metric R I_R S I_S in
  let! '(topdowns, bottomups) := gen_inspect_tys aux rules D I_D R I_R S I_S delayD in
  ret (mk_obs extra_vars run_rules constr_delays smart_constrs topdowns bottomups)
)).
Defined.

(* Danger: running [unquote_all] generates universe constraints between the things inside 
   each typed_term and pretty common monomorphic types like [list], [pair], [option], etc.
   It's safer to unquote each term in obs with ltac. *)
Definition unquote_all (obs : RwObligations term)
 : TemplateMonad (RwObligations typed_term). ltac1:(refine(
  let '(mk_obs extra_vars run_rules constr_delays smart_constrs topdowns bottomups) :=
    obs
  in
  extra_vars <- monad_map tmUnquote extra_vars ;;
  run_rules <- monad_map tmUnquote run_rules ;;
  constr_delays <- monad_map tmUnquote constr_delays ;;
  smart_constrs <- monad_map tmUnquote smart_constrs ;;
  topdowns <- monad_map tmUnquote topdowns ;;
  bottomups <- monad_map tmUnquote bottomups ;;
  ret (mk_obs extra_vars run_rules constr_delays smart_constrs topdowns bottomups)
)).
Abort.

End GoalGeneration.

Ltac unquote_and_assert_terms terms k :=
  lazymatch terms with
  | [] => k tt
  | ?t :: ?rest =>
    run_template_program (tmUnquote t) ltac:(fun t' =>
    match t' with
    | {| my_projT2 := ?t'' |} => assert t''; [|unquote_and_assert_terms rest k]
    end)
  end.

Ltac unquote_and_assert_obs obs k :=
  lazymatch obs with
  | mk_obs ?extra_vars ?run_rules ?constr_delays ?smart_constrs ?topdowns ?bottomups =>
    unquote_and_assert_terms extra_vars ltac:(fun _ =>
    unquote_and_assert_terms run_rules ltac:(fun _ =>
    unquote_and_assert_terms constr_delays ltac:(fun _ =>
    unquote_and_assert_terms smart_constrs ltac:(fun _ =>
    unquote_and_assert_terms topdowns ltac:(fun _ =>
    unquote_and_assert_terms bottomups k)))))
  end.

Ltac mk_rw_obs k :=
  lazymatch goal with
  | |- @rewriter ?U ?HFrame ?HAux ?root ?fueled ?metric ?Rstep ?D ?I_D ?HDelay ?R ?I_R ?S ?I_S _ _ _ =>
    parse_rel 0 Rstep ltac:(fun rules n =>
    run_template_program (
      fueled' <- tmQuote fueled ;;
      metric' <- tmQuote metric ;;
      D' <- tmQuote D ;;
      I_D' <- tmQuote I_D ;;
      R' <- tmQuote (@R) ;;
      I_R' <- tmQuote (@I_R) ;;
      S' <- tmQuote (@S) ;;
      I_S' <- tmQuote (@I_S) ;;
      delayD <- tmQuote (@delayD U HFrame D I_D HDelay) ;;
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
        gen_all HAux rules fueled'' metric'' D'' I_D'' R'' I_R'' S'' I_S'' delayD') ltac:(fun qobs n =>
        unquote_and_assert_obs qobs k)
    end))
  end.

Ltac mk_rw' := mk_rw_obs ltac:(fun _ => idtac).

Ltac mk_smart_constr_children Root Rstep I_R I_S C s hasHrel Hrel :=
  lazymatch goal with
  | H : SmartConstrCase (frameD ?frame ?hole) -> _ |- _ =>
    specialize (H (MkSmartConstrCase _));
    let x := fresh "x" in
    let s' := fresh "s" in
    let Hrel' := fresh "Hrel" in
    unshelve edestruct H as [x s' Hrel'];
    [(* Siblings *)..|(* n *)|(* e_ok n *)
    |(* Param *)eapply (@preserve_R _ _ Root _ I_R _); eassumption
    |(* State *)eapply (@preserve_S_dn _ _ Root _ I_S _); cbn; eassumption
    |(* equation about n *)
    |];
    [(* Siblings *)..|(* n *)refine (e_map (fun C => _) C)|(* e_ok n *)|(* equation about n *)|];
    [(* n *)|(* e_ok (e_map ..) *)apply e_map_ok; assumption
    |(* equation about n *)unerase; reflexivity
    |];
    clear H s;
    apply (@preserve_S_up _ _ Root _ I_S _) in s'; [|assumption]; cbn in s';
    lazymatch hasHrel with
    | false => mk_smart_constr_children Root Rstep I_R I_S C s' true Hrel'
    | true =>
      let Hrel'' := fresh "Hrel" in
      match goal with |- result _ _ ?C ?e1 =>
      match type of s' with State _ C ?e2 =>
      match type of C with erased ?T =>
        assert (Hrel'' : «e_map (fun (C : T) => clos_refl_trans _ Rstep (framesD C e1) (framesD C e2)) C»);
        [unerase; eapply rt_trans; [exact Hrel|exact Hrel']|];
        clear Hrel Hrel'
      end end end;
      mk_smart_constr_children Root Rstep I_R I_S C s' true Hrel''
    end
  | _ =>
    lazymatch hasHrel with
    | false => econstructor; [exact s|unerase; apply rt_refl]
    | true => econstructor; [exact s|exact Hrel]
    end
  end.
Ltac mk_smart_constr :=
   clear;
   let fuel := fresh "fuel" in
   let C := fresh "C" in
   let emetric := fresh "emetric" in
   let Hemetric_ok := fresh "Hemetric_ok" in
   let Hemetric := fresh "Hemetric" in
   let r := fresh "r" in
   let s := fresh "s" in
   intros _ fuel C; intros;
   lazymatch goal with
   | |- @rw_for ?U ?HFrame ?Root ?fueled ?metric ?Rstep ?R ?I_R ?S ?I_S ?fuel _ _ _ =>
     unfold rw_for in *;
     intros emetric Hemetric_ok r s Hemetric;
     mk_smart_constr_children Root Rstep I_R I_S C s false None
   end.

Definition tm_get_constr (s : string) : TemplateMonad typed_term :=
  ref <- tmLocate s ;;
  match ref with
  | [ConstructRef ind n] => tmUnquote (tConstruct ind n [])
  | _ => tmFail ("tm_get_constr: not a constructor: " +++ s)
  end.

Ltac mk_run_rule :=
  lazymatch goal with
  | |- RunRule ?rule -> _ =>
    clear;
    let fuel := fresh "fuel" in
    let C := fresh "C" in
    intros _ fuel C; intros;
    let r := fresh "r" in
    let s := fresh "s" in
    let Hnext := fresh "Hnext" in
    let emetric := fresh "emetric" in
    let Hemetric_ok := fresh "Hemetric_ok" in
    let Hemetric := fresh "Hemetrick" in
    lazymatch goal with H1 : _, H2 : _, H3 : _ |- _ => revert H1 H2 H3 end;
    unfold rw_for; intros r s Hnext emetric Hemetric_ok _ _ Hemetric;
    let x' := fresh "x'" in
    let s' := fresh "s'" in
    let Hrel := fresh "Hrel" in
    unshelve edestruct Hnext as [x' s' Hrel];
    [(* n *)refine (e_map (fun C => _) C)|(* e_ok n *)
    |(* Param *)exact r|(* State *)exact s
    |(* equation about metric *)unerase; reflexivity|];
    [(* e_ok (e_map (fun C => new metric) C) *)apply e_map_ok; assumption|];
    econstructor; [exact s'|];
    unerase; eapply rt_trans; [eapply rt_step|exact Hrel];
    run_template_program (tm_get_constr rule) ltac:(fun ctor =>
    match ctor with
    | {| my_projT2 := ?ctor' |} =>
      eapply ctor';
      lazymatch goal with
      | _ => eassumption
      end
    end)
  end.

(* Used by mk_topdown *)
Ltac strip_one_match :=
  lazymatch goal with
  | H : InspectCaseRule _ -> match ?e with _ => _ end -> _ |- _ =>
    let Heqn := fresh "Heqn" in
    destruct e eqn:Heqn;
    repeat lazymatch goal with
    | H : InspectCaseRule _ -> Impossible -> _ |- _ => clear H
    | H : InspectCaseCongruence _ -> Impossible -> _ |- _ => clear H
    end
  | H : InspectCaseCongruence _ -> match ?e with _ => _ end -> _ |- _ =>
    let Heqn := fresh "Heqn" in
    destruct e eqn:Heqn;
    repeat lazymatch goal with
    | H : InspectCaseRule _ -> Impossible -> _ |- _ => clear H
    | H : InspectCaseCongruence _ -> Impossible -> _ |- _ => clear H
    end
  end.
Ltac mk_topdown_congruence :=
  lazymatch goal with
  | H : InspectCaseRule _ -> Active _ -> _ |- _ => fail
  | H : InspectCaseCongruence _ -> Congruence ?constr -> _, Hdelay : ConstrDelay ?constr -> _ |- _ =>
    eapply (Hdelay (MkConstrDelay constr)); intros;
    eapply (H (MkInspectCaseCongruence constr) (MkCongruence constr));
    solve [eassumption|reflexivity]
  end.
Ltac mk_topdown_active r s :=
  lazymatch goal with
  | H : InspectCaseRule _ -> Active ?rule -> _, Hextras : ExtraVars ?rule -> _ |- _ =>
    eapply (Hextras (MkExtraVars rule));
    [(* Find all the misc. arguments by unification *) eassumption ..
    |(* Success continuation: add rhs vars + assumptions above the line *)
     intros _; intros
    |(* Failure continuation: forget everything about the rule we just applied *)
     intros _; clear Hextras H];
    [(* Success: switch to new env + state and apply the proper rule *)
     lazymatch goal with
     | H1 : _ , H2 : _ |- _ =>
       let r_old := fresh "r_old" in
       let s_old := fresh "s_old" in
       rename r into r_old, s into s_old, H1 into r, H2 into s;
       eapply (H (MkInspectCaseRule rule) (MkActive rule)); [..|reflexivity|exact r|exact s];
       eassumption
     end
    |(* Failure: try to apply other rules *)
      mk_topdown_active r s]
  | _ => mk_topdown_congruence
  end.
Ltac mk_topdown :=
  repeat lazymatch goal with
  | H : Topdown -> _ |- _ => clear H
  | H : SmartConstr _ -> _ |- _ => clear H
  end;
  let d := fresh "d" in
  let R := fresh "R" in
  let C := fresh "C" in
  let e := fresh "e" in
  let r := fresh "r" in
  let s := fresh "s" in
  intros _ R C e d r s; intros;
  repeat strip_one_match;
  mk_topdown_active r s.

Ltac mk_bottomup_fallback :=
  lazymatch goal with
  | H : InspectCaseRule _ -> Active _ -> _ |- _ => fail
  | H : Fallback -> _ |- _ => exact (H MkFallback)
  end.
Ltac mk_bottomup_active :=
  lazymatch goal with
  | H : InspectCaseRule _ -> Active ?rule -> _, Hextras : ExtraVars ?rule -> _ |- _ =>
    eapply (Hextras (MkExtraVars rule));
    [eassumption..|intros _; intros|intros _; clear Hextras H];
    [eapply (H (MkInspectCaseRule rule) (MkActive rule)); eauto
    |mk_bottomup_active]
  | _ => mk_bottomup_fallback
  end.
Ltac mk_bottomup :=
  repeat lazymatch goal with
  | H : Topdown -> _ |- _ => clear H
  | H : Bottomup -> _ |- _ => clear H
  | H : SmartConstr _ -> _ |- _ => clear H
  end;
  let R := fresh "R" in
  let C := fresh "C" in
  let e := fresh "e" in
  let r := fresh "r" in
  let s := fresh "s" in
  intros _ R C e r s; intros;
  repeat strip_one_match;
  mk_bottomup_active.

Require Import Coq.PArith.BinPos Lia.

Ltac try_find_constr e k_constr k_atom :=
  lazymatch goal with
  | H : SmartConstr e -> _ |- _ => k_constr e H
  | _ =>
    lazymatch e with
    | ?e' _ => try_find_constr e' k_constr k_atom
    | _ => k_atom e
    end
  end.
Ltac next_action e k_rec k_constr k_atom :=
  lazymatch e with
  | Rec ?e' => k_rec e'
  | _ => try_find_constr e k_constr k_atom
  end.

Lemma nonempty_nonzero (fuel : Rewriting.Fuel true) : is_empty true fuel = false -> (fuel > 1)%positive.
Proof. unfold is_empty; destruct fuel; try ltac1:(lia); now inversion 1. Qed.

Inductive MetricDecreasing := MkMetricDecreasing.
Ltac apply_recur recur fuel fueled metric Hempty :=
  match fueled with
  | true =>
    specialize recur with (fuel := Pos.pred fuel);
    specialize (recur (erase (Pos.to_nat (Pos.pred fuel))) _);
    apply recur; try assumption;
    repeat lazymatch goal with
    | |- e_lt _ _ =>
      unfold e_lt; unerase; subst; cbn;
      apply nonempty_nonzero in Hempty; lia
    | |- e_ok (e_map _ _) => apply e_map_ok
    | |- e_ok _ => assumption
    | |- «_» => unerase; reflexivity
    end
  | false =>
    specialize recur with (fuel := fuel); unfold Rec; rewrite ?e_map_fuse;
    lazymatch goal with
    | |- result _ _ ?C' (@delayD ?univ ?HFrame ?D ?I_D ?HD ?A ?e ?d') =>
      lazymatch C' with
      | e_map ?f ?C'' =>
        specialize recur with
          (C := C')
          (y := e_map (fun C => metric _ (f C) (@delayD univ HFrame D I_D HD A e d')) C'')
          (d := d')
      | _ =>
        specialize recur with
          (C := C')
          (y := e_map (fun C => metric _ C (@delayD univ HFrame D I_D HD A e d')) C')
          (d := d')
      end;
      eapply recur;
      repeat lazymatch goal with
      | |- Param _ _ => assumption
      | |- State _ _ _ => assumption
      | |- e_ok (e_map _ _) => apply e_map_ok
      | |- e_ok _ => assumption
      | |- «_» => unerase; unfold run_metric; reflexivity
      | |- e_lt _ _ =>
        unfold e_lt; unerase;
        lazymatch goal with
        | |- (_ < ?x)%nat => subst x; unfold run_metric
        end;
        let dummy := fresh "dummy" in
        pose (dummy := MkMetricDecreasing); clearbody dummy; revert dummy
      end
    end
  end.

Ltac mk_edit_rhs recur fuel fueled metric Hempty :=
  let rec go _ :=
    lazymatch goal with
    | |- @rw_for _ _ _ _ _ _ _ _ _ _ _ _ _ ?e =>
      next_action e
        (* Recursive calls: *)
        ltac:(fun e' =>
          (* Rewrite any call pending on the current subterm in terms of delayed computation *)
          lazymatch goal with
          | H : e' = delayD ?d |- _ =>
            rewrite H;
            let emetric := fresh "emetric" in
            let Hemetric_ok := fresh "Hemetric_ok" in
            let r := fresh "r" in
            let s := fresh "s" in
            let Hemetric := fresh "Hemetric" in
            intros emetric Hemetric_ok r s Hemetric;
            apply_recur recur fuel fueled metric Hempty
          end)
        (* Constructor nodes: apply the smart constructor... *)
        ltac:(fun constr Hconstr =>
          apply (Hconstr (MkSmartConstr constr) fuel);
          repeat match goal with
          | |- e_ok (e_map _ _) => apply e_map_ok
          | |- e_ok _ => assumption
          end;
          (* ...and recursively expand each child *)
          intros _; intros; go tt)
        (* Atoms: just return the atom *)
        ltac:(fun e => unfold rw_for; intros; econstructor; [|unerase; apply rt_refl]; assumption)
    end
  in go tt.

Inductive Sentinel := MkSentinel. (* used by mk_rewriter *)
Ltac mk_rewriter :=
  lazymatch goal with
  | |- @rewriter ?univ ?HFrame _ ?Root ?fueled ?metric ?Rstep ?D ?I_D ?HD ?R ?I_R ?S ?I_S _ _ _ =>
    unfold rewriter, rewriter';
    lazymatch goal with
    | |- forall (_ : Rewriting.Fuel _), _ =>
      (* Pull the erased nat and its e_ok proof to the front *)
      let sentinel := fresh "sentinel" in
      let emetric := fresh "emetric" in
      let Hemetric_ok := fresh "Hemetric_ok" in
      pose (sentinel := MkSentinel : Sentinel);
      clearbody sentinel;
      intros; unfold rw_for; intros emetric Hemetric_ok;
      repeat progress lazymatch goal with
      | H : ?T, emetric : _, Hemetric_ok : _ |- _ =>
        lazymatch T with
        | Sentinel => idtac
        | _ => revert H
        end
      end;
      (* Now apply the fixpoint combinator *)
      pattern emetric; revert emetric Hemetric_ok;
      let recur := fresh "recur" in
      let fuel := fresh "fuel" in
      let A := fresh "A" in
      apply FixEN; intros emetric Hemetric_ok recur fuel A;
      (* Check if fuel-based and fuel empty, and return e unchanged if so *)
      let Hempty := fresh "Hempty" in
      match fueled with
      | true =>
        destruct (is_empty fueled fuel) eqn:Hempty;
        [econstructor; [|unerase; apply rt_refl]; assumption|]
      | false => idtac
      end;
      (* Case split on type tag *)
      destruct A;
      lazymatch goal with
      (* Nonatomic children: apply topdown rules and then bottomup rules *)
      | Htopdown : Topdown ?hole -> _ |- forall _ : erased (frames_t ?hole _), _ =>
        let C := fresh "C" in
        let C_ok := fresh "C_ok" in
        let e := fresh "e" in
        let d := fresh "d" in
        let r := fresh "r" in
        let s := fresh "s" in
        let Hemetric := fresh "Hemetric" in
        intros C C_ok e d r s Hemetric;
        apply (@res_chain univ HFrame Root Rstep S I_S _ C C_ok);
        [ apply (Htopdown (MkTopdown hole) _ C C_ok e d r s);
          lazymatch goal with
          (* Rule applications *)
          | Hrun : RunRule ?rule -> _ |- InspectCaseRule ?rule -> _ =>
            intros _ _; intros;
            lazymatch goal with He : delayD d = _ |- _ => rewrite He in * end;
            let r'' := fresh "r" in
            let s'' := fresh "s" in
            lazymatch goal with H1 : _, H2 : _ |- _ => rename H1 into r'', H2 into s'' end;
            eapply (Hrun (MkRunRule rule) fuel);
            lazymatch goal with
            | |- Param _ _ => eassumption
            | |- State _ _ _ => eassumption
            | |- «_» => eassumption
            | |- e_ok _ => eassumption
            | _ => idtac
            end;
            [try eassumption..|mk_edit_rhs recur fuel fueled metric Hempty]
          (* Congruence cases *)
          | Hconstr : SmartConstr ?constr -> _ |- InspectCaseCongruence ?constr -> _ =>
            intros _ _; intros;
            lazymatch goal with Hdelay : delayD d = _ |- _ => rewrite Hdelay in * end;
            let r' := fresh "r" in
            let s' := fresh "s" in
            let Hemetric' := fresh "Hemetric" in
            let r_t := type of r in assert (r' : r_t) by exact r;
            let s_t := type of s in assert (s' : s_t) by exact s;
            let Hemetric_t := type of Hemetric in assert (Hemetric' : Hemetric_t) by exact Hemetric;
            revert r' s' Hemetric';
            unfold rw_for in Hconstr;
            apply (Hconstr (MkSmartConstr _) fuel C C_ok); try exact Hemetric_ok;
            intros _; intros;
            lazymatch goal with
            (* If child is nonatomic (has call to delayD), recur *)
            | |- result _ _ _ (delayD _) =>
              apply_recur recur fuel fueled metric Hempty
            (* Otherwise, just return it *)
            | |- result _ _ _ _ => econstructor; [|unerase; apply rt_refl]; assumption
            end
          end
        | lazymatch goal with
          | Hbottomup : Bottomup hole -> _ |- _ =>
            clear emetric Hemetric_ok recur d e s Hemetric; intros e s;
            apply (Hbottomup (MkBottomup hole) _ C C_ok e r s);
            lazymatch goal with
            (* Rule applications *)
            | Hrun : RunRule ?rule -> _ |- InspectCaseRule ?rule -> _ =>
              intros _ _; intros;
              lazymatch goal with He : e = _ |- _ => rewrite He in * end;
              (* Run the rule... *)
              let s'' := fresh "s" in
              lazymatch goal with H : _ |- _ => rename H into s'' end;
              unshelve eapply (Hrun (MkRunRule rule) fuel);
              try lazymatch goal with
              | |- erased nat => refine (erase _)
              | |- State _ _ _ => exact s''
              | |- «_» => unerase; unfold run_metric; reflexivity
              end;
              try lazymatch goal with
              | |- e_ok (erase _) => apply erase_ok
              | _ => assumption
              end;
              (* ...and then just return the modified tree *)
              unfold rw_for; intros; econstructor; [|unerase; apply rt_refl]; assumption
            (* Fallback (just return the child) *)
            | |- Fallback -> _ =>
              intros _; econstructor; [|unerase; apply rt_refl]; assumption
            end
          end
        ]
      (* Atomic children: Just run the delayed computation *)
      | |- forall _ : erased (frames_t ?hole _), _ =>
        let C := fresh "C" in
        let C_ok := fresh "C_ok" in
        let e := fresh "e" in
        let d := fresh "d" in
        intros C C_ok e d; intros;
        econstructor; [|unerase; apply rt_refl]; assumption
      end
    end
  end.

(* Like mk_rw', but apply the default automation and only leave behind nontrivial goals *)
Ltac mk_rw :=
  mk_rw';
  lazymatch goal with
  | |- SmartConstr _ -> _ => mk_smart_constr
  | |- RunRule _ -> _ => mk_run_rule
  | |- Topdown _ -> _ => mk_topdown
  | |- Bottomup _ -> _ => mk_bottomup
  | _ => idtac
  end;
  [..|mk_rewriter].

Ltac mk_easy_delay :=
  try lazymatch goal with
  | |- ConstrDelay _ -> _ =>
    clear; simpl; intros; lazymatch goal with H : forall _, _ |- _ => eapply H; try reflexivity; eauto end
  end.

Ltac cond_failure :=
  lazymatch goal with
  | H : Failure ?rule -> ?R |- ?R =>
    apply (H (MkFailure rule))
  end.

Ltac cond_success name :=
  lazymatch goal with
  | Hs : Success ?rule -> _, Hf : Failure ?rule -> _ |- ?R =>
    specialize (Hs (MkSuccess rule)); clear Hf; rename Hs into name
  end.

