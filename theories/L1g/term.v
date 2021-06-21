Require Import FunInd.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import Ascii.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.micromega.Lia.
Require Export Common.Common Common.AstCommon.
Require Export L1g.compile.

Open Scope string_scope.
Open Scope bool.
Open Scope list.
Set Implicit Arguments.

(** Printing terms in exceptions for debugging purposes **)
Fixpoint print_term (t:Term) : string :=
  match t with
    | TRel n => "(REL " ++ (nat_to_string n) ++ ")"
    | TProof => " PRF "
    | TLambda nm _ => "(LAM " ++ (print_name nm) ++ ")"
    | TLetIn nm dfn bod =>
      ("LET " ++ (print_name nm) ++ " " ++ (print_term dfn) ++ " " ++
              (print_term bod))
    | TApp fn arg =>
      "(APP " ++ (print_term fn) ++ " " ++ (print_term arg) ++ ")"
    | TConst s => "[" ++ string_of_kername s ++ "]"
    | TConstruct i ix _ _ =>
      "(CSTR " ++ (print_inductive i) ++ " " ++ nat_to_string ix ++ ")"
    | TCase n mch _ =>
      "(CASE " ++ (print_inductive (fst n)) ++ " " ++
               (nat_to_string (snd n)) ++ " " ++ (print_term mch) ++
                 " _ " ++")"
    | TFix _ n => "(FIX " ++ (nat_to_string n) ++ ")"
    | TProj prj rcd =>
      "(PROJ " ++ print_projection prj ++ " " ++ print_term rcd ++ ")"
    | TWrong str => (" Wrong " ++ str )
  end.


Section TermTerms_dec. (** to make Ltac definitions local **)
Local Ltac rght := right; injection; intuition.
Local Ltac lft := left; subst; reflexivity.
Local Ltac cross := try (solve [right; intros h; discriminate]).
Lemma TermTerms_dec: 
  (forall (s t:Term), s = t \/ s <> t) /\
  (forall (bb cc:Brs), bb = cc \/ bb <> cc) /\
  (forall (dd ee:Defs), dd = ee \/ dd <> ee).
Proof.
  apply TrmTrmsBrsDefs_ind; intros.
  - Case "TRel". destruct t; cross. destruct (eq_nat_dec n n0); [lft | rght].
  - destruct t; cross; lft.
  - destruct t0; cross.
    destruct (name_dec n n0);
      destruct (H t0); [lft | rght ..].
  - destruct t1; cross.
    destruct (name_dec n n0);
      destruct (H t1_1); destruct (H0 t1_2); [lft | rght ..]. 
  - destruct t1; cross.
    destruct (H t1_1); destruct (H0 t1_2);
      [lft | rght ..]. 
  - destruct t; cross. destruct (kername_eq_dec k k0); [lft | rght].
  - destruct t; cross.
    destruct (inductive_dec i i0), (eq_nat_dec n n2),
    (eq_nat_dec n0 n3), (eq_nat_dec n1 n4); [lft | rght .. ].
  - destruct t0; cross.
    destruct p as [i n], p0 as [i0 n0].
    destruct (eq_dec n n0), (inductive_dec i i0); subst.
    destruct (H t0), (H0 b0); [lft | rght .. ].
    + right. intros j. myInjection j. intuition.
    + right. intros j. myInjection j. intuition.
    + right. intros j. myInjection j. intuition.
  - destruct t; cross.
    destruct (eq_nat_dec n n0); destruct (H d0); [lft | rght .. ].
  - destruct t0; cross.
    destruct (project_dec p p0), (H t0); [lft | rght .. ].
  - destruct t; cross. destruct (string_dec s s0).
    + subst. left. reflexivity.
    + right. intros h. myInjection h. elim n. reflexivity.
  - destruct cc; cross; lft.
  - destruct cc; cross.
    destruct (eq_nat_dec n n0), (H t0), (H0 cc); [lft | rght .. ].
  - destruct ee; cross. lft.
  - destruct ee; cross.
    destruct (name_dec n n1); destruct (eq_nat_dec n0 n2);
    destruct (H t0); destruct (H0 ee); [lft | rght .. ].
Qed.
End TermTerms_dec.

Definition Term_dec := proj1 TermTerms_dec.

Fixpoint TrmSize (t:Term) : nat :=
  match t with
    | TLambda _ bod => S (TrmSize bod)
    | TLetIn _ dfn bod => S (TrmSize dfn + TrmSize bod)
    | TApp fn a => S (TrmSize fn + TrmSize a)
    | TCase _ mch brs => S (TrmSize mch + TrmBsSize brs)
    | TFix ds _ => S (TrmDsSize ds)
    | TProj prj t => S (TrmSize t)
    | _ => 1
  end
with TrmBsSize (bs:Brs) : nat :=
  match bs with
    | bnil => 1
    | bcons _ s ss => S (TrmSize s + TrmBsSize ss)
  end
with TrmDsSize (ds:Defs) : nat :=
  match ds with
    | dnil => 1
    | dcons _ t1 _ es => S (TrmSize t1 + TrmDsSize es)
  end.

Lemma TrmSAize_mkApp:
  forall args t a, TrmSize t < TrmSize (mkApp (TApp t a) args).
Proof.
  induction args; intros.
  - cbn. lia.
  - cbn. specialize (IHargs (TApp t a0) a).
    cbn in IHargs. lia.
Qed.

Lemma mkApp_TConstruct_inject:
  forall args args' i n npars nargs  i' n' npars' nargs',
    mkApp (TConstruct i n npars nargs) args =
    mkApp (TConstruct i' n' npars' nargs') args' ->
     i = i' /\ n = n' /\ npars = npars' /\ nargs = nargs' /\ args = args'.
Proof.
  induction args; induction args'; intros.
  - cbn in H. subst. myInjection H. intuition.
  - cbn in H. destruct args'.
    + cbn in H. discriminate.
    + dstrctn (mk_canonical_append args' t). rewrite j in H.
      rewrite mkApp_out in H. discriminate.
  - cbn in H. destruct args.
    + cbn in H. discriminate.
    + dstrctn (mk_canonical_append args t). rewrite j in H.
      rewrite mkApp_out in H. discriminate.
  - cbn in H. admit.
Admitted.

Definition isWrong t : Prop := exists s, t = TWrong s.
Lemma isWrong_dec: forall t, {isWrong t}+{~ isWrong t}.
Proof.
  destruct t;
  try (right; intros h; destruct h as [x jx]; discriminate).
  - left. exists s. reflexivity.
Defined.

Definition isLambda (t:Term) : Prop :=
  exists nm bod, t = TLambda nm bod.
Lemma IsLambda: forall nm bod, isLambda (TLambda nm bod).
intros. exists nm, bod. reflexivity.
Qed.
Hint Resolve IsLambda : core.

Ltac isLam_inv :=
  let  xx := fresh "x"
  with yy := fresh "y"
  with zz := fresh "z"
  with jj := fresh "j" in
  match goal with
    | [ h : (isLambda ?a) |- _ ] =>
      destruct h as [xx [yy [zz jj]]]; discriminate
  end.
              
Lemma isLambda_dec: forall t, {isLambda t}+{~ isLambda t}.
Proof.
  induction t;
    try (right; intros h; unfold isLambda in h; elim h; intros x h1;
         elim h1; intros x0 h2; discriminate).
  left. auto.
Qed.

Definition isProof (t:Term) := t = TProof.
Lemma IsProof: isProof TProof.
intros. reflexivity.
Qed.
Hint Resolve IsProof : core.

Lemma isProof_dec: forall t, {isProof t}+{~ isProof t}.
Proof.
  destruct t;
  try (right; intros h; red in h; discriminate).
  - left. auto.
Defined.

Definition isApp (t:Term) : Prop :=
  exists fn arg, t = TApp fn arg.
Lemma IsApp: forall fn arg, isApp (TApp fn arg).
intros. exists fn, arg. reflexivity.
Qed.
Hint Resolve IsApp : core.

Ltac isApp_inv :=
  let  xx := fresh "x"
  with yy := fresh "y"
  with zz := fresh "z"
  with jj := fresh "j" in
  match goal with
    | [ h : (isApp ?a) |- _ ] =>
      destruct h as [xx [yy [zz jj]]]; discriminate
  end.

Lemma isApp_dec: forall t, {isApp t}+{~ isApp t}.
destruct t; try (right; not_isApp). 
left. auto.
Qed.

Definition isFix (t:Term) : Prop :=
  exists ds m, t = TFix ds m.
Lemma IsFix: forall ds m, isFix (TFix ds m).
intros. exists ds, m. reflexivity.
Qed.
Hint Resolve IsFix : core.

Ltac not_isFix :=
  let hh := fresh "h"
  with xx := fresh "x"
  with yy := fresh "y" 
  with jj := fresh "j" in
  intros hh; destruct hh as [xx [yy jj]]; discriminate.

Lemma isFix_dec: forall t, {isFix t}+{~ isFix t}.
induction t;
  try (solve [right; not_isFix]).
left. auto.
Qed.

Definition isConstruct (t:Term) : Prop :=
  exists i n np na, t = TConstruct i n np na.
Lemma IsConstruct:
  forall i n np na, isConstruct (TConstruct i n np na).
intros. exists i, n, np, na. reflexivity.
Qed.
Hint Resolve IsConstruct : core.

Lemma isConstruct_dec: forall t, isConstruct t \/ ~ isConstruct t.
Proof.
  destruct t;
  try (right; intros h; dstrctn h; discriminate).
  - left. auto.
Qed.

Definition isCase (t:Term) : Prop :=
  exists ml mch brs, t = TCase ml mch brs.
Lemma isCase_dec: forall t, isCase t \/ ~ isCase t.
Proof.
  destruct t;
  try (right; intros h; dstrctn h; discriminate).
  - left. exists p, t, b. reflexivity.
Qed.

Inductive isCanonical : Term -> Prop :=
| canC: forall (i:inductive) (n np na:nat),
    isCanonical (TConstruct i n np na)
| canCA: forall fn arg, isCanonical fn -> isCanonical (TApp fn arg).
Hint Constructors isCanonical : core.

Lemma isCanonical_dec: forall t, isCanonical t \/ ~ isCanonical t.
Proof.
  induction t; try (solve[right; intros h; inversion_Clear h]).
  - destruct IHt1.
    + left. constructor. assumption.
    + right. intros h. elim H. inversion_clear h. assumption.
  - left. auto.
Qed.

Function canonicalP (t:Term) : option (nat * nat * nat * Terms) :=
  match t with
    | TConstruct _ r npars nargs => Some (r, npars, nargs, nil)
    | TApp fn arg =>
      match canonicalP fn with
      | None => None
      | Some (x, args) => Some (x, app args (unit arg))
      end
    | _ => None
  end.
Functional Scheme canonicalP_ind := Induction for canonicalP Sort Prop.

Lemma canonicalP_isCanonical:
  forall t x, canonicalP t = Some x -> isCanonical t.
Proof.
  induction t; simpl; intros; try discriminate. 
  - destruct (canonicalP t1).
    + constructor. eapply IHt1. reflexivity.
    + discriminate.
  - constructor.
Qed.

Lemma isCanonical_canonicalP:
  forall t, isCanonical t -> exists x, canonicalP t = Some x.
Proof.
  induction 1; simpl.
  - exists (n, np, na, nil). reflexivity.
  - destruct IHisCanonical. destruct x. rewrite H0.
    inversion_Clear H.
    + inversion_Clear H0. cbn. exists (n, np, na, unit arg). reflexivity.
    + destruct p. destruct p. exists (n0, n1, n, app l (unit arg)).
      reflexivity.
Qed.

Function tskipn (n:nat) (l:Terms) : option Terms :=
  match n, l with
    | 0, l => Some l
    | S n, cons a l => tskipn n l
    | S _, nil => None
  end.

(*******************************
Lemma tappend_tnil: forall ts:Terms, tappend ts tnil = ts.
induction ts; simpl; try reflexivity.
rewrite IHts. reflexivity.
Qed.
Hint Rewrite tappend_tnil : tappend.

Lemma nil_tappend:
  forall ts us:Terms, tnil = tappend ts us -> ts = tnil /\ us = tnil.
Proof.
  induction ts; cbn; intros.
  - intuition.
  - discriminate.
Qed.

Lemma tappend_assoc:
  forall xts yts zts,
       (tappend xts (tappend yts zts)) = (tappend (tappend xts yts) zts).
  induction xts; intros yts zts; simpl.
  - reflexivity.
  - rewrite IHxts. reflexivity.
Qed.

Lemma tappend_cons_lem:
  forall ys t zs,
    tappend ys (tcons t zs) = tappend (tappend ys (tunit t)) zs.
  induction ys; intros tt zzs; simpl.
  - reflexivity.
  - rewrite IHys. reflexivity.
Qed.
  
Lemma tappend_tappend_lem:
  forall xts yts t zts,
       (tappend xts (tappend yts (tcons t zts))) =
       (tappend (tappend xts (tappend yts (tcons t tnil))) zts).
  intros xts yts t zts. rewrite tappend_cons_lem. rewrite tappend_assoc.
  reflexivity.
Qed.


Lemma tlength_tappend:
  forall ts us, tlength (tappend ts us) = (tlength ts) + (tlength us).
Proof.
  induction ts; simpl; intros; try reflexivity.
  - rewrite IHts. reflexivity.
Qed.

Lemma tappend_tcons_tunit:
  forall bs ds cs x,
    tappend bs (tcons x cs) = tappend ds cs -> tappend bs (tunit x) = ds.
Proof.
  induction bs; destruct ds; cbn; intros.
  - assert (j:= f_equal tlength H). cbn in j. lia.
  - injection H. intros. subst x. destruct ds.
    + reflexivity.
    + injection H; intros.
      assert (j:= f_equal tlength H). cbn in j.
      rewrite tlength_tappend in j. lia.
  - destruct cs.
    + discriminate.
    + injection H; intros. assert (j:= f_equal tlength H0).
      rewrite tlength_tappend in j. cbn in j. lia.
  - injection H; intros.  assert (j:= f_equal tlength H0).
    rewrite tlength_tappend in j. cbn in j.
    specialize (IHbs _ _ _ H0). rewrite IHbs. rewrite H1. reflexivity.
Qed.


Fixpoint tmap (fn:Term -> Term) (ts:Terms) : Terms :=
  match ts with
    | tnil => tnil
    | tcons x xs => tcons (fn x) (tmap fn xs)
  end.

Fixpoint tIn (a:Term) (l:Terms) : Prop :=
    match l with
      | tnil => False
      | tcons b m => b = a \/ tIn a m
    end.

Lemma tIn_tappend1:
  forall u ts ss, tIn u (tappend ts (tcons u ss)).
Proof.
  induction ts; intros ss.
  - simpl. left. reflexivity.
  - simpl. right. apply IHts.
Qed.

Lemma tIn_tappend2:
  forall t ts us, tIn t ts -> tIn t (tappend ts us).
induction ts; intros us h; inversion_Clear h; simpl.
- left. reflexivity.
- right. apply IHts. assumption.
Qed.


Fixpoint le (n m: nat): bool :=
  match n, m with
    | 0, _ => true
    | S n, S m => le n m
    | _, _ => false
  end.
 *********************************)

(******************************
Record split := mkSplit {fsts:Terms; nst:Term; lsts:Terms}.

Function tsplit (n:nat) (l:Term) (ls:Terms) {struct n} : option split :=
  match n, ls with
    | 0, tnil => Some (mkSplit tnil l tnil)
    | _, tnil => None
    | 0, ts => Some (mkSplit tnil l ts)
    | S m, tcons t ts =>
      match tsplit m t ts with
        | None => None
        | Some (mkSplit fs s ls) => Some (mkSplit (tcons l fs) s ls)
      end
  end.
(***
Definition testts:=
  (tcons (TRel 1) (tcons (TRel 2) (tcons (TRel 3) (tunit (TRel 4))))).
Eval cbv in tsplit 0 (TRel 0) testts.
Eval cbv in tsplit 1 (TRel 0) testts.
Eval cbv in tsplit 2 (TRel 0) testts.
Eval cbv in tsplit 3 (TRel 0) testts.
Eval cbv in tsplit 4 (TRel 0) testts.
Eval cbv in tsplit 5 (TRel 0) testts.
***)

Lemma tsplit_0_Some:
  forall ts t, tsplit 0 t ts = Some (mkSplit tnil t ts).
Proof. 
  destruct ts; intros; reflexivity.
Qed.

Lemma tsplit_tcons:
  forall ix t ts frsts u lasts,
    tsplit ix t ts = Some {| fsts:= frsts; nst:= u; lsts:= lasts |} ->
         tcons t ts = tappend frsts (tcons u lasts).
Proof.
  intros ix t ts.
  functional induction (tsplit ix t ts); intros; try discriminate.
  - myInjection H. reflexivity.
  - myInjection H. reflexivity.
  - myInjection H. cbn. apply f_equal2. reflexivity.
    apply IHo. assumption.
Qed.

Lemma tcons_tsplit:
  forall (frsts ts lasts:Terms) t u,
    tcons t ts = tappend frsts (tcons u lasts) ->
     tsplit (tlength frsts) t ts = Some (mkSplit frsts u lasts).
Proof.
  induction frsts; intros;cbn in *.
  - myInjection H. destruct lasts; reflexivity.
  - destruct (tappend_mk_canonical frsts u lasts) as [y [ys jy]].
    rewrite jy in H. myInjection H.
    erewrite IHfrsts. reflexivity. rewrite jy. reflexivity.
Qed.
  
Lemma tsplit_sanity:
  forall n t ts, match tsplit n t ts with
                 | None => n > tlength ts
                 | Some (mkSplit s1 s2 s3) =>
                   tcons t ts = tappend s1 (tcons s2 s3) /\
                   n = tlength s1
               end.
Proof.
  intros n t ts. functional induction (tsplit n t ts); intros; cbn.
  - intuition.
  - destruct n. elim y. lia.
  - destruct ls. elim y. intuition.
  - rewrite e1 in IHo. lia.
  - rewrite e1 in IHo. rewrite (proj1 IHo). rewrite (proj2 IHo).
    intuition.
Qed.

Function atsplit (n:nat) (ls:Terms) {struct ls} : option split :=
  match n, ls with
    | _, tnil => None
    | 0, tcons t ts => Some (mkSplit tnil t ts)
    | S m, tcons t ts =>
      match atsplit m ts with
        | Some (mkSplit fs u ls) => Some (mkSplit (tcons t fs) u ls)
        | None => None
      end
  end.
(*********
Eval cbv in atsplit 0 (tcons (TRel 0) testts).
Eval cbv in atsplit 1 (tcons (TRel 0) testts).
Eval cbv in atsplit 2 (tcons (TRel 0) testts).
Eval cbv in atsplit 3 (tcons (TRel 0) testts).
Eval cbv in atsplit 4 (tcons (TRel 0) testts).
Eval cbv in atsplit 5 (tcons (TRel 0) testts).
***********)

Lemma atsplit_tsplit:
  forall n u us, atsplit n (tcons u us) = tsplit n u us.
Proof.
  intros n u us.
  functional induction (tsplit n u us); cbn; intros;
  try reflexivity; try discriminate.
  - destruct n.
    + elim y.
    + destruct n; reflexivity.
  - destruct m.
    + rewrite e1 in IHo. cbn in IHo. discriminate.
    + rewrite e1 in IHo. cbn in IHo. destruct (atsplit m ts).
      destruct s. discriminate. reflexivity.
  - rewrite e1 in IHo. cbn in IHo.
    destruct m.
    + injection IHo; intros. subst fs. subst. reflexivity.
    + destruct (atsplit m ts).
      * destruct s0. injection IHo; intros. subst fs. subst.
        reflexivity.
      * discriminate.      
Qed.

Lemma atsplit_S:
  forall m ts fs u ls,
    atsplit m ts = Some {| fsts:= fs; nst:= u; lsts:= ls |} ->
    forall t, atsplit (S m) (tcons t ts) =
              Some {| fsts:= tcons t fs; nst:= u; lsts:= ls |}.
Proof.
  intros; functional induction (atsplit m ts); intros; try discriminate.
  - injection H; intros. subst fs. subst. cbn. reflexivity.
  - injection H; intros. subst fs. subst. cbn. rewrite e1. reflexivity.
Qed.

Function aatsplit (n:nat) (ls:Terms) {struct n} : option split :=
  match n, ls with
    | _, tnil => None
    | 0, tcons t ts => Some (mkSplit tnil t ts)
    | S m, tcons t ts =>
      match aatsplit m ts with
        | Some (mkSplit fs u ls) => Some (mkSplit (tcons t fs) u ls)
        | None => None
      end
  end.

Lemma aatsplit_atsplit:
  forall n ts, aatsplit n ts = atsplit n ts.
Proof.
  intros n ts. functional induction (atsplit n ts); cbn; try reflexivity.
  - destruct n; reflexivity.
  - rewrite IHo. destruct (atsplit m ts).
    + destruct s. myInjection e1. reflexivity.
    + discriminate.
  - rewrite e1 in IHo. rewrite IHo. reflexivity.
Qed.
 *************************)

(** treverse  **
Fixpoint treverse (ts: Terms) : Terms :=
  match ts with
    | tnil => tnil
    | tcons b bs => tappend (treverse bs) (tunit b)
  end.

Lemma treverse_tappend_distr:
  forall x y:Terms,
    treverse (tappend x y) = tappend (treverse y) (treverse x).
Proof.
  induction x as [| a l IHl]; cbn; intros.
  - destruct y as [| a l]; cbn. reflexivity.
    rewrite tappend_tnil. reflexivity.
  - rewrite (IHl y). rewrite tappend_assoc. reflexivity.
Qed.

Remark treverse_tunit:
  forall (l:Terms) (a:Term),
    treverse (tappend l (tunit a)) = tcons a (treverse l).
Proof.
  intros.
  apply (treverse_tappend_distr l (tunit a)); simpl; auto.
Qed.

Lemma treverse_involutive:
  forall ts:Terms, treverse (treverse ts) = ts.
Proof.
  induction ts as [| a l IHl]; cbn; intros. reflexivity.
  - rewrite treverse_tunit. rewrite IHl. reflexivity.
Qed.
   
Remark tunit_treverse:
    forall (l:Terms) (a:Term),
    tappend (treverse l) (tunit a) = treverse (tcons a l).
Proof.
  intros. cbn. reflexivity.
Qed.

Lemma treverse_terms_ind:
 forall (P : Terms -> Prop),
       P tnil ->
       (forall (a: Term) (l:Terms),
           P (treverse l) -> P (treverse (tcons a l))) ->
       forall l:Terms, P (treverse l).
Proof.
  intros. induction l.
  - cbn. assumption.
  - eapply H0. assumption.
Qed.

Lemma treverse_ind:
  forall (P: Terms -> Prop),
    P tnil ->
    (forall (x: Term) (l: Terms), P l -> P (tappend l (tunit x))) ->
    forall l: Terms, P l.
Proof.
  intros.
  assert (j: treverse (treverse l) = l). apply treverse_involutive.
  rewrite <-j.
  apply treverse_terms_ind.
  - assumption.
  - intros. cbn. apply H0. assumption.
Qed.

Fixpoint tfrsts (n:nat) (ts:Terms) : option Terms :=
  match n, ts with
    | 0, _ => Some tnil
    | S m, tnil => None
    | S m, tcons u us => match tfrsts m us with
                           | None => None
                           | Some xs => Some (tcons u xs)
                         end
  end.
Definition tlasts (n:nat) (ts:Terms) : option Terms :=
  match tfrsts (tlength ts - n) (treverse ts) with
    | None => None
    | Some us => Some (treverse us)
  end.
*************************)
  
(**********
Function tnth (n:nat) (l:Terms) {struct l} : option Term :=
  match l with
    | tnil => None
    | tcons x xs => match n with
                      | 0 => Some x
                      | S m => tnth m xs
                    end
  end.
 ***************)

(**************
Lemma tnth_tsplit_sanity:
  forall n t ts, match tsplit n t ts with
                 | None => tnth n (tcons t ts) = None
                 | Some sp => tnth n (tcons t ts) = Some (nst sp)
               end.
Proof.
  intros n t ts. functional induction (tsplit n t ts); cbn; try reflexivity.
  - destruct n. elim y. reflexivity.
  - rewrite e1 in IHo. destruct m.
    + cbn in IHo. discriminate.
    + cbn in IHo. assumption.
  - rewrite e1 in IHo. destruct m; cbn in IHo; assumption.
Qed.
    
Lemma tsplit_tnth_sanity:
  forall xs n u, tnth n xs = Some u ->
                 exists t ts frsts lasts,
                   xs = tcons t ts /\
                   tsplit n t ts = Some (mkSplit frsts u lasts).
Proof.
  intros xs n u.
  functional induction (tnth n xs); intros; try discriminate.
  - myInjection H. exists u, xs, tnil, xs. intuition. cbn.
    destruct xs; reflexivity.
  - destruct (IHo H) as [y0 [y1 [y2 [y3 [jy1 jy2]]]]]. subst xs.
    exists x, (tcons y0 y1), (tcons x y2), y3. intuition.
    cbn. rewrite jy2. reflexivity.
Qed.

Lemma tnth_None_tsplit_None:
  forall n t ts, tsplit n t ts = None -> tnth n (tcons t ts) = None.
Proof.
  intros. assert (k:= tnth_tsplit_sanity n t ts). rewrite H in k.
  assumption.
Qed.
 **************************)

(******************
  Lemma tnth_tlength_sanity:
  forall fsts t lsts,
    tnth (tlength fsts) (tappend fsts (tcons t lsts)) = Some t.
Proof.
  induction fsts; intros. reflexivity.
  - cbn. apply IHfsts.
Qed.

Lemma tnth_extend1:
  forall n l t,  tnth n l = Some t -> n < tlength l.
Proof.
  induction n; induction l; simpl; intros; try discriminate; try lia.
  - apply lt_n_S. eapply IHn. eassumption.
Qed.

Lemma tnth_extend2:
  forall n l,  n < tlength l -> exists t, tnth n l = Some t.
Proof.
  induction n; intros.
  - destruct l. simpl in H. lia. exists t. reflexivity.
  - destruct l. inversion H. simpl in H.
    specialize (IHn _ (lt_S_n _ _ H)). destruct IHn. exists x.
    simpl. assumption.
Qed.

Lemma tnth_append:
  forall n args t, tnth n args = Some t ->
            forall brgs, tnth n (tappend args brgs) = Some t.
Proof.
  induction n; induction args; simpl; intros; try discriminate; try assumption.
  - apply IHn. assumption.
Qed.
********************)

(*********************
Lemma mkApp_tnil_ident: forall t, mkApp t tnil = t.
  destruct t; cbn; try rewrite tappend_tnil; try reflexivity.
Qed.

Inductive MkApp :Term -> Terms -> Term -> Prop :=
| maApp: forall fn b bs cs,
           MkApp (TApp fn b bs) cs (TApp fn b (tappend bs cs))
| maNil: forall fn, ~ isApp fn -> MkApp fn tnil fn
| maCons: forall fn c cs, ~ isApp fn -> MkApp fn (tcons c cs) (TApp fn c cs).
Hint Constructors MkApp : core.

Lemma MkApp_tcons_isApp:
  forall fn bs res, MkApp fn bs res ->
  forall c cs, bs = tcons c cs -> isApp res.
induction 1; intros cx csx h.
- exists fn, b, (tappend bs cs). reflexivity.
- discriminate.
- injection h; intros; subst.
  exists fn, cx, csx. reflexivity.
Qed.

Lemma MkApp_nil_ident:
  forall fn, ~ isApp fn ->  MkApp fn tnil fn.
induction fn; simpl; intros h; try (constructor; assumption).
Qed.

Lemma MkApp_cons_App:
  forall fn, ~ isApp fn ->
    forall arg args, MkApp fn (tcons arg args) (TApp fn arg args).
induction fn; simpl; intros h arg args; try (constructor; assumption).
Qed.

Lemma mkApp_MkApp: forall fn bs, MkApp fn bs (mkApp fn bs).
induction fn; induction bs; intros; simpl;
try (solve [apply maNil; not_isApp]);
try (solve [apply maCons; not_isApp]). 
- apply maApp. 
- apply maApp. 
Qed.

Lemma MkApp_mkApp:
  forall fn bs res, MkApp fn bs res -> mkApp fn bs = res.
induction fn; intros bs res h; try (inversion_Clear h; simpl; try reflexivity).
- rewrite tappend_tnil. reflexivity.
- elim H. exists fn1, fn2, t. reflexivity.
Qed.

Lemma MkApp_single_valued:
  forall fn bs res1, MkApp fn bs res1 ->
     forall res2, MkApp fn bs res2 -> res1 = res2.
Proof.
intros. rewrite <- (MkApp_mkApp H). rewrite <- (MkApp_mkApp H0).
reflexivity.
Qed.

Lemma mkApp_cons_App:
  forall fn, ~ isApp fn ->
    forall arg args, mkApp fn (tcons arg args) = TApp fn arg args.
induction fn; simpl; intros h arg args; try (constructor; assumption).
- elim h. exists fn1, fn2, t. reflexivity.
Qed.

Lemma mkApp_goodFn:
  forall fn t ts, ~ isApp fn -> mkApp fn (tcons t ts) = TApp fn t ts.
destruct fn; intros; try reflexivity.
- elim H. auto.
Qed.

Lemma pre_mkApp_isApp:
  forall fn args res, MkApp fn args res ->
  forall b bs, args = tcons b bs -> isApp res.
induction 1; intros bx bsx h.
- exists fn, b, (tappend bs cs). reflexivity.
- discriminate.
- exists fn, c, cs. reflexivity.
Qed.

Lemma mkApp_isApp:
  forall fn arg args, isApp (mkApp fn (tcons arg args)).
intros fn arg args. eapply (@pre_mkApp_isApp fn (tcons arg args)).
- destruct (isApp_dec fn) as [h1 | h2].
  destruct h1 as [x0 [x1 [x2 h]]].
  + rewrite h. apply maApp. 
  + apply mkApp_MkApp. 
- reflexivity.
Qed.

Lemma mkApp_idempotent:
 forall fn args brgs,
   mkApp (mkApp fn args) brgs = mkApp fn (tappend args brgs).
Proof.
  induction fn; induction args; simpl; intros; try reflexivity.
  - rewrite tappend_tnil. reflexivity.
  - rewrite <- tappend_assoc. simpl. reflexivity.
Qed.

Lemma isApp_mkApp_isApp:
  forall t, isApp (mkApp t tnil) -> isApp t.
Proof.
  destruct t; intros h; destruct h as [x0 [x1 [x2 j]]]; simpl in j;
  try discriminate.
  - exists t1, t2, t3. reflexivity.
Qed.

Lemma not_isApp_mkApp_not_isApp:
  forall t, ~ isApp t -> ~ isApp (mkApp t tnil).
Proof.
  intros t h1 h2. elim h1. apply isApp_mkApp_isApp. assumption.
Qed.

Lemma isApp_mkApp_isApp2:
  forall t, isApp t -> isApp (mkApp t tnil).
Proof.
  inversion 1. destruct H0 as [x0 [x1 j]]. subst. simpl.
  exists x, x0, (tappend x1 tnil). reflexivity.
Qed.

Lemma not_isApp_mkApp_isApp2:
  forall t, ~ isApp (mkApp t tnil) -> ~ isApp t.
Proof.
  destruct t; intros h1 h2; elim h1; try assumption. 
  - apply isApp_mkApp_isApp2. assumption.
Qed.

Lemma not_isApp_mkApp_TApp:
  forall t arg args, ~ isApp t -> 
    mkApp (mkApp t tnil) (tcons arg args) = TApp (mkApp t tnil) arg args.
induction t; intros arg args h; simpl; try reflexivity.
- elim h. exists t1, t2, t3. reflexivity.
Qed.

(** main lemma for dealing with mkApp **)
(*********
Lemma mkApp_isApp_lem:
  forall fn ts arg args,
    ts = tcons arg args ->
    exists fn' arg' args', mkApp fn ts = TApp fn' arg' args'.
Proof.
  intros fn ts arg args h. functional induction (mkApp fn ts).
  - exists fn, b, (tappend bs (tcons arg args)). reflexivity.
  - discriminate.
  - myInjection h. destruct (isApp_dec t).
    + destruct i as [x0 [x1 [x2 jx]]]. subst. discriminate.
    + destruct t.
 ***********)

(********
Lemma mkApp_isApp_lem:
  forall arg args fn' arg' args',
    mkApp (TApp fn' arg' args') (tcons arg args) =
    mkApp fn' (tcons arg' (tappend args' (tcons arg args))).
Proof.
  intros. unfold mkApp at 1. reflexivity.

  induction fn; intros arg args; 
    try (solve [left; split; try not_isApp; intuition]).
  - right. exists fn1, fn2, t. intuition.
    unfold mkApp at 1. destruct (isApp_dec fn1).
    + destruct i as [k0 [k1 [k2 k3]]]. subst.
 ***************)         

(***********
Lemma mkApp_isApp_lem:
  forall fn arg args,
    (~ isApp fn /\ mkApp fn (tcons arg args) = TApp fn arg args) \/
    (exists fn' u us,
        fn = TApp fn' u us /\
        mkApp fn (tcons arg args) =
        mkApp fn' (tcons u (tappend us (tcons arg args)))).
Proof.
  induction fn; intros arg args; 
    try (solve [left; split; try not_isApp; intuition]).
  - right. exists fn1, fn2, t. intuition.
    unfold mkApp at 1. destruct (isApp_dec fn1).
    + destruct i as [k0 [k1 [k2 k3]]]. subst.
          
    destruct (IHfn1 arg args).
    + destruct H. rewrite mkApp_goodFn in H0; try assumption. elim H.


      Lemma mkApp_isApp_lem:
  forall fn arg args,
    (~ isApp fn /\ mkApp fn (tcons arg args) = TApp fn arg args) \/
    (exists fn' u us,
        fn = TApp fn' u us /\
        mkApp fn (tcons arg args) =
        mkApp fn' (tappend (tcons u us) (tcons arg args))).
Proof.
  induction fn; intros arg args; unfold mkApp; cbn;
    try (solve [left; split; try not_isApp; intuition]).
  - destruct (IHfn1 arg args).
    + destruct H. elim H.

      
    right. exists fn1, fn2, t. split. reflexivity.
    destruct fn1; try reflexivity.
    eapply f_equal3.
  - exists (TRel n), arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - exists (TSort s), arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - exists (TProof fn), arg, tnil. split. reflexivity.
    + left. intuition. revert H. not_isApp. 
  - exists (TProd n fn1 fn2), arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - exists (TLambda n fn1 fn2), arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - exists (TLetIn n fn1 fn2 fn3), arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - exists fn1, fn2, (tappend t (tunit arg)). split.
    + apply f_equal3; try reflexivity. rewrite <- tappend_cons_lem.
      reflexivity.
    + right. destruct (IHfn1 fn2 t) as [x0 [x1 [x2 [jx1 jx2]]]].
      destruct jx2.
      * destruct H as [k0 [k1 [k2 k3]]]. subst.
        exists x1, t. intuition.

        
  - change (exists (fn' arg' : Term) (args' : Terms),
              TApp fn1 fn2 (tappend t (tcons arg args)) =
              TApp fn' arg' (tappend args' args) /\
              (~ isApp (TApp fn1 fn2 t) /\
               fn' = TApp fn1 fn2 t /\ arg = arg' /\ args' = tnil \/
                                                     isApp (TApp fn1 fn2 t) /\ 
               TrmSize fn' < S (TrmSize fn1 + TrmSize fn2 + TrmsSize t) /\
               tIn arg args')).
    exists fn1, fn2, (tappend t (tunit arg)). split.
    + rewrite <- tappend_assoc. simpl. reflexivity.
    + right. split; try split.
      * exists fn1, fn2, t. reflexivity.
      * lia.
      * apply tIn_tappend1.
  - exists (TConst s), arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - exists (TInd i), arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - exists (TConstruct i n n0 n1), arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - exists (TCase p fn1 fn2 b), arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - exists (TFix d n), arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - exists (TWrong s), arg, tnil. cbn. split. reflexivity.
    left. repeat split. not_isApp.
Qed.
****************)
  
(********)
Lemma mkApp_isApp_lem:
  forall fn arg args, exists fn' arg' args',
    mkApp fn (tcons arg args) = TApp fn' arg' (tappend args' args) /\
    ((~ isApp fn /\ fn' = fn /\ arg = arg' /\ args' = tnil) \/
     (isApp fn /\ TrmSize fn' < TrmSize fn /\ tIn arg args')).
Proof.
  induction fn; intros arg args; unfold mkApp; simpl.
  - exists (TRel n), arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - exists (TSort s), arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - exists TProof, arg, tnil. split. reflexivity.
    + left. intuition. revert H. not_isApp. 
  - exists (TProd n fn1 fn2), arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - exists (TLambda n fn1 fn2), arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - exists (TLetIn n fn1 fn2 fn3), arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - change (exists (fn' arg' : Term) (args' : Terms),
              TApp fn1 fn2 (tappend t (tcons arg args)) =
              TApp fn' arg' (tappend args' args) /\
              (~ isApp (TApp fn1 fn2 t) /\
               fn' = TApp fn1 fn2 t /\ arg = arg' /\ args' = tnil \/
                                                     isApp (TApp fn1 fn2 t) /\ 
               TrmSize fn' < S (TrmSize fn1 + TrmSize fn2 + TrmsSize t) /\
               tIn arg args')).
    exists fn1, fn2, (tappend t (tunit arg)). split.
    + rewrite <- tappend_assoc. simpl. reflexivity.
    + right. split; try split.
      * exists fn1, fn2, t. reflexivity.
      * lia.
      * apply tIn_tappend1.
  - exists (TConst s), arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - exists (TInd i), arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - exists (TConstruct i n n0 n1), arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - exists (TCase p fn1 fn2 b), arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - exists (TFix d n), arg, tnil. split. reflexivity.
    left. intuition. revert H. not_isApp.
  - exists (TWrong s), arg, tnil. cbn. split. reflexivity.
    left. repeat split. not_isApp.
Qed.
(************)
 ********************************)

(** well-formed terms: TApp well-formed all the way down **)
Inductive WFapp: Term -> Prop :=
| wfaRel: forall m, WFapp (TRel m)
| wfaProof: WFapp TProof
| wfaLambda: forall nm bod, WFapp bod -> WFapp (TLambda nm bod)
| wfaLetIn: forall nm dfn bod,
    WFapp dfn -> WFapp bod -> WFapp (TLetIn nm dfn bod)
| wfaApp: forall fn t, WFapp fn -> WFapp t -> WFapp (TApp fn t)
| wfaConst: forall nm, WFapp (TConst nm)
| wfaConstruct: forall i m np na, WFapp (TConstruct i m np na)
| wfaCase: forall m mch brs,
    WFapp mch -> WFappBs brs -> WFapp (TCase m mch brs)
| wfaFix: forall defs m, WFappDs defs -> WFapp (TFix defs m)
| wfaProj: forall prj t, WFapp t -> WFapp (TProj prj t)
with WFappBs: Brs -> Prop :=
     | wfabnil: WFappBs bnil
     | wfabcons: forall n b bs, WFapp b -> WFappBs bs ->  WFappBs (bcons n b bs)
with WFappDs: Defs -> Prop :=
     | wfadnil: WFappDs dnil
     | wfadcons: forall nm bod arg ds,
         WFapp bod -> WFappDs ds -> WFappDs (dcons nm bod arg ds).
Hint Constructors WFapp WFappBs WFappDs : core.
Scheme WFapp_ind' := Minimality for WFapp Sort Prop
  with WFappBs_ind' := Minimality for WFappBs Sort Prop
  with WFappDs_ind' := Minimality for WFappDs Sort Prop.
Combined Scheme WFappTrmsBrsDefs_ind
         from WFapp_ind', WFappBs_ind', WFappDs_ind'.

Inductive WFapps: Terms -> Prop :=
| wfaNil: WFapps nil
| wfaCons: forall t ts, WFapp t -> WFapps ts -> WFapps (cons t ts).

Lemma append_pres_WFapps:
  forall ts, WFapps ts -> forall us, WFapps us -> WFapps (app ts us).
Proof.
  induction 1; intros us hus; simpl.
  - assumption.
  - constructor. assumption. apply IHWFapps. assumption.
Qed.

Lemma canonicalP_pres_WFapp:
  forall t x, canonicalP t = Some x ->
              forall r args, x = (r, args) ->  WFapp t -> WFapps args.
Proof.
  intros t.
  functional induction (canonicalP t); intros; try discriminate.
  - myInjection H. myInjection H2.
    inversion_Clear H1. apply append_pres_WFapps.
    + eapply IHo; try eassumption. reflexivity.
    + constructor. assumption. constructor.
  - inversion_Clear H1. myInjection H. constructor.
Qed.

(**********
Lemma WFapps_tappendl:
  forall ts us, WFapps (tappend ts us) -> WFapps ts.
Proof.
  induction ts; simpl; intros us h; intuition. 
  + inversion h; constructor. assumption. eapply IHts. eassumption.
Qed.

Lemma WFapps_tappendr:
  forall ts us, WFapps (tappend ts us) -> WFapps us.
Proof.
  intros ts us. functional induction (tappend ts us); intuition.
  - apply IHt. inversion H. assumption.
Qed.
 ************)

(***
Lemma WFapp_mkApp_TApp:
  forall u, WFapp u -> forall t a1 args, u = (TApp t a1 args) ->
    mkApp t (tcons a1 args) = TApp t a1 args.
Proof.
  induction 1; intros; try discriminate.
  - injection H3. intros. subst. rewrite (mkApp_cons_App H). reflexivity.
Qed.

Lemma WFapp_mkApp_WFapp:
  forall u, WFapp u -> forall t ts, u = mkApp t ts -> WFapp t /\ WFapps ts.
Proof.
  induction 1; intros tx tsx h; destruct tx; destruct tsx; simpl in *; 
  try discriminate; intuition; injection h; intros; subst;
  try (constructor; assumption); try assumption.
  - constructor; try assumption. eapply WFapps_tappendl. eassumption.
  - constructor; try assumption. eapply WFapps_tappendl. eassumption.
  - eapply WFapps_tappendr. eassumption.
Qed.

Lemma tnth_pres_WFapp:
  forall (brs:Terms), WFapps brs -> forall n t, tnth n brs = Some t -> WFapp t.
Proof.
  intros brs h n t.
  functional induction (tnth n brs); intros; try discriminate.
  - injection H; intros; subst. inversion h. assumption.
  - apply IHo; inversion h; assumption.
Qed.
 ***************)

Lemma WFapps_all:
  forall args, WFapps args ->
               forall n x, nth_error args n = Some x -> WFapp x.
Proof.  
  induction 1; intros; destruct n; unfold nth_error in H; try discriminate.
  - unfold nth_error in H1. myInjection H1. assumption.
  - apply (IHWFapps n x). change (nth_error ts n = Some x) in H1. assumption.
Qed.

Lemma WFapp_mkApp:
  forall args t, WFapp (mkApp t args) -> WFapp t /\ WFapps args.
Proof.
  induction args; intros.
  - cbn in H. intuition. (* constructor. *)
  - change (WFapp (mkApp (TApp t a) args)) in H.
    specialize (IHargs _ H). destruct IHargs. inversion_Clear H0.
    split.
    + assumption.
    + constructor; assumption.
Qed.
    
Lemma mkApp_pres_WFapp:
  forall args, WFapps args -> forall t, WFapp t -> WFapp (mkApp t args).
Proof.
  induction 1; intros.
  - cbn. assumption.
  - cbn. apply IHWFapps. constructor; assumption.
Qed.

Lemma bnth_pres_WFapp:
  forall (brs:Brs), WFappBs brs ->
                    forall n t m, bnth n brs = Some (t,m) -> WFapp t.
Proof.
  intros brs h n t.
  functional induction (bnth n brs); intros; try discriminate.
  - myInjection H. inversion h. assumption.
  - eapply IHo; inversion h; eassumption.
Qed.

Lemma dnthBody_pres_WFapp:
  forall (ds:Defs), WFappDs ds ->
    forall n x ix, (dnthBody n ds) = Some (x, ix) -> WFapp x.
Proof.
  intros ds h n x ix.
  functional induction (dnthBody n ds); intros; auto.
  - discriminate.
  - myInjection H. inversion h. assumption.
  - apply IHo; inversion h; assumption.
Qed.

Lemma tskipn_pres_WFapp args:
    WFapps args -> forall np ts, tskipn np args = Some ts -> WFapps ts.
Proof.
  intros hargs np ts h.
  functional induction (tskipn np args).
  - injection h. intros. subst. assumption.
  - inversion_Clear hargs. apply IHo; try assumption.
  - discriminate.
Qed.

(**********
Lemma nth_error_pres_WFapp:
  forall ts n x, nth_error ts n = Some x -> WFapp x -> WFapps ts.
Proof.
 **************) 

(** well-formed terms: TApp well-formed all the way down **)
(*** not used essentially at the moment **)
Inductive WFTrm: Term -> nat -> Prop :=
| wfRel: forall n m, m < n -> WFTrm (TRel m) n
| wfProof: forall n, WFTrm TProof n
| wfLambda: forall n nm bod, WFTrm bod (S n) -> WFTrm (TLambda nm bod) n
| wfLetIn: forall n nm dfn bod,
    WFTrm dfn n -> WFTrm bod (S n) -> WFTrm (TLetIn nm dfn bod) n
| wfApp: forall n fn t,
    WFTrm fn n -> WFTrm t n -> WFTrm (TApp fn t) n
| wfConst: forall n nm, WFTrm (TConst nm) n
| wfConstruct: forall n i m np na, WFTrm (TConstruct i m np na) n
| wfCase: forall n m mch brs,
    WFTrm mch n -> WFTrmBs brs n -> WFTrm (TCase m mch brs) n
| wfFix: forall n defs m,
    WFTrmDs defs (n + dlength defs) -> WFTrm (TFix defs m) n
| wfProj: forall n prj t, WFTrm t n -> WFTrm (TProj prj t) n
with WFTrmBs: Brs -> nat -> Prop :=
     | wfbnil: forall n, WFTrmBs bnil n
     | wfbcons: forall n m b bs,
         WFTrm b n -> WFTrmBs bs n -> WFTrmBs (bcons m b bs) n
with WFTrmDs: Defs -> nat -> Prop :=
     | wfdnil: forall n, WFTrmDs dnil n
     | wfdcons: forall n nm bod arg ds,
         WFTrm bod n -> WFTrmDs ds n -> WFTrmDs (dcons nm bod arg ds) n.
Hint Constructors WFTrm WFTrmBs WFTrmDs : core.
Scheme WFTrm_ind' := Minimality for WFTrm Sort Prop
  with WFTrmBs_ind' := Minimality for WFTrmBs Sort Prop
  with WFTrmDs_ind' := Minimality for WFTrmDs Sort Prop.
Combined Scheme WFTrmTrmsBrsDefs_ind
         from WFTrm_ind', WFTrmBs_ind', WFTrmDs_ind'.

Lemma WFTrm_WFapp:
  (forall t n, WFTrm t n -> WFapp t) /\
  (forall bs n, WFTrmBs bs n -> WFappBs bs) /\
  (forall ds n, WFTrmDs ds n -> WFappDs ds).
Proof.
  apply WFTrmTrmsBrsDefs_ind; intros; try (constructor; try assumption).
Qed.


(*** Some basic operations and properties of [Term] ***)

(** occurrances of a constant in a term (ignoring type components) **)
Section PoccTrm_sec.
Variable nm:kername.

Inductive PoccTrm : Term -> Prop :=
| PoLambdaBod: forall s bod, PoccTrm bod -> PoccTrm (TLambda s bod)
| PoLetInDfn: forall s dfn bod, PoccTrm dfn -> PoccTrm (TLetIn s dfn bod)
| PoLetInBod: forall s dfn bod,
    PoccTrm bod -> PoccTrm (TLetIn s dfn bod)
| PoAppL: forall fn a, PoccTrm fn -> PoccTrm (TApp fn a)
| PoAppA: forall fn a, PoccTrm a -> PoccTrm (TApp fn a)
| PoConst: PoccTrm (TConst nm)
| PoCaseA: forall n p mch brs, PoccTrm (TCase ((mkInd nm n), p) mch brs)
| PoCaseL: forall n mch brs, PoccTrm mch -> PoccTrm (TCase n mch brs)
| PoCaseR: forall n mch brs, PoccBrs brs -> PoccTrm (TCase n mch brs)
| PoFix: forall ds m, PoccDefs ds -> PoccTrm (TFix ds m)
| PoCnstr: forall m1 m2 np na, PoccTrm (TConstruct (mkInd nm m1) m2 np na)
| PoProj: forall prj t, PoccTrm t -> PoccTrm (TProj prj t)
with PoccBrs : Brs -> Prop :=
     | PoBhd: forall n t ts, PoccTrm t -> PoccBrs (bcons n t ts)
     | PoBtl: forall n t ts, PoccBrs ts -> PoccBrs (bcons n t ts)
with PoccDefs : Defs -> Prop :=
     | PoDhd_bod: forall dn db dra ds,
         PoccTrm db -> PoccDefs (dcons dn db dra ds)
     | PoDtl: forall dn db dra ds,
         PoccDefs ds -> PoccDefs (dcons dn db dra ds).
Hint Constructors PoccTrm PoccBrs PoccDefs : core.
Scheme poTrm_ind' := Minimality for PoccTrm Sort Prop
  with poBrs_ind' := Minimality for PoccBrs Sort Prop
  with poDefs_ind' := Minimality for PoccDefs Sort Prop.
Combined Scheme poTrmTrmsBrsDefs_ind
         from poTrm_ind', poBrs_ind', poDefs_ind'.

Lemma Pocc_TConst: forall s2, PoccTrm (TConst s2) -> nm = s2.
  intros s2 h. inversion h. reflexivity.
Qed.

Lemma notPocc_TConst: forall s2, ~ PoccTrm (TConst s2) -> nm <> s2.
intros s2 h j. elim h. rewrite <- j. auto. 
Qed.

(**************
Lemma PoccTrms_tappendl:
  forall ts us, PoccTrms ts -> PoccTrms (tappend ts us).
induction 1; simpl.
- constructor. assumption.
- apply PoTtl. assumption.
Qed.

Lemma PoccTrms_tappendr:
  forall us, PoccTrms us -> forall ts, PoccTrms (tappend ts us).
induction 1; induction ts0; simpl.
- constructor. assumption.
- apply PoTtl. assumption.
- simpl in IHPoccTrms. apply PoTtl. assumption.
- apply PoTtl. assumption.
Qed.

Lemma PoccTrms_tappend_tcons:
  forall u, PoccTrm u -> forall ts us, PoccTrms (tappend ts (tcons u us)).
intros. apply PoccTrms_tappendr. apply PoThd. assumption.
Qed.

Lemma tnth_PoccTrms:
  forall ix args t, tnth ix args = Some t ->
                    PoccTrm t -> PoccTrms args.
Proof.
  intros ix args t h1  h2.
  functional induction (tnth ix args); try discriminate.
  - myInjection h1. constructor. assumption.
  - apply PoTtl. intuition.
Qed.

Lemma PoccTrms_append_invrt:
  forall bs cs, PoccTrms (tappend bs cs) -> PoccTrms bs \/ PoccTrms cs.
induction bs; intros cs h; simpl in h.
- intuition.
- inversion_Clear h.
  * left. apply PoThd. assumption.
  * destruct (IHbs _ H0).
    left. apply PoTtl. assumption.
    right. assumption.
Qed.
 ******************)

Lemma inverse_Pocc_TConstL: forall s2, ~ PoccTrm (TConst s2) -> nm <> s2.
intros s2 h j. elim h. rewrite <- j. auto.
Qed.

Lemma Pocc_TApp:
  forall t arg, PoccTrm (TApp t arg) -> PoccTrm t \/ PoccTrm arg.
inversion 1; intuition.
Qed.

Lemma notPocc_TLambda:
  forall n bod, ~ PoccTrm (TLambda n bod) -> ~ PoccTrm bod.
intuition. 
Qed.

Lemma notPocc_TLetIn:
  forall n dfn bod, ~ PoccTrm (TLetIn n dfn bod) ->
                    ~ PoccTrm dfn \/ ~ PoccTrm bod.
intuition. 
Qed.

Lemma notPocc_TCase:
  forall n mch brs, ~ PoccTrm (TCase n mch brs) ->
                   ~ PoccTrm mch /\ ~ PoccBrs brs.
intuition. 
Qed.

Lemma notPocc_TFix:
  forall ds m, ~ PoccTrm (TFix ds m) -> ~ PoccDefs ds.
intuition. 
Qed.

(**********
Lemma notPoccTrms:
  forall t ts, ~ PoccTrms (tcons t ts) -> ~ PoccTrm t /\ ~ PoccTrms ts.
intuition. 
Qed.

Lemma PoccTrms_tcons:
  forall t ts, PoccTrms (tcons t ts) -> PoccTrm t \/ PoccTrms ts.
inversion 1; intuition. 
Qed.

Lemma PoccTrms_append:
  forall ts1 ts2, PoccTrms (tappend ts1 ts2) -> PoccTrms ts1 \/ PoccTrms ts2.
  induction ts1; intros ts2 h. simpl in h.
  - right. assumption.
  - inversion_Clear h.
    + left. apply PoThd. assumption.
    + destruct (IHts1 _ H0).
      * left. apply PoTtl. assumption.
      * right. assumption.
Qed.


Lemma tIn_Pocc_Poccs:
  forall t ts us, tIn t ts -> PoccTrm t -> PoccTrms (tappend ts us).
induction ts; intros us h1 h2.
- inversion h1.
- inversion h1.
  + subst. simpl. apply PoThd. assumption.
  + simpl.  apply PoTtl. apply IHts; assumption.
Qed.
 *************)

Lemma notPoccDefs:
  forall nm bod rarg ds, ~ PoccDefs (dcons nm bod rarg ds) ->
                         ~ PoccTrm bod /\ ~ PoccDefs ds.
intuition. 
Qed.



(** Instantiate index n of a term with a _locally_closed_ term, so
*** we do not lift.  But we do increment n when going under a binder 
**)
Section Instantiate_sec.
Variable (tin:Term).

Inductive Instantiate: nat -> Term -> Term -> Prop :=
| IRelEq: forall n, Instantiate n (TRel n) tin
| IRelGt: forall n m, n > m -> Instantiate n (TRel m) (TRel m)
| IRelLt: forall n m, n < m -> Instantiate n (TRel m) (TRel (pred m))
| IPrf: forall n, Instantiate n TProof TProof
| ILambda: forall n nm bod ibod,
    Instantiate (S n) bod ibod -> 
    Instantiate n (TLambda nm bod) (TLambda nm ibod)
| ILetIn: forall n nm dfn bod idfn ibod,
    Instantiate n dfn idfn -> Instantiate (S n) bod ibod ->
    Instantiate n (TLetIn nm dfn bod) (TLetIn nm idfn ibod)
| IApp: forall n t a it ia,
    Instantiate n t it -> Instantiate n a ia ->
    Instantiate n (TApp t a) (TApp it ia)
| IConst: forall n s, Instantiate n (TConst s) (TConst s)
| IConstruct: forall n ind m1 np na,
    Instantiate n (TConstruct ind m1 np na) (TConstruct ind m1 np na)
| ICase: forall n np s ts is its ,
    Instantiate n s is -> InstantiateBrs n ts its ->
    Instantiate n (TCase np s ts) (TCase np is its)
| IFix: forall n d m id, 
    InstantiateDefs (n + dlength d) d id ->
    Instantiate n (TFix d m) (TFix id m)
| IProj: forall n prj t it,
    Instantiate n t it -> Instantiate n (TProj prj t) (TProj prj it) 
| IWrong: forall n s, Instantiate n (TWrong s) (TWrong s)
with InstantiateBrs: nat -> Brs -> Brs -> Prop :=
     | Ibnil: forall n, InstantiateBrs n bnil bnil
     | Ibcons: forall n m b bs ib ibs,
         Instantiate n b ib ->
         InstantiateBrs n bs ibs ->
         InstantiateBrs n (bcons m b bs) (bcons m ib ibs)
with InstantiateDefs: nat -> Defs -> Defs -> Prop :=
     | Idnil: forall n, InstantiateDefs n dnil dnil
     | Idcons: forall n nm bod rarg ds ibod ids,
         Instantiate n bod ibod -> InstantiateDefs n ds ids ->
         InstantiateDefs n (dcons nm bod rarg ds)
                         (dcons nm ibod rarg ids).
Hint Constructors Instantiate InstantiateBrs InstantiateDefs : core.
Scheme Instantiate_ind' := Induction for Instantiate Sort Prop
  with InstantiateBrs_ind' := Induction for InstantiateBrs Sort Prop
  with InstantiateDefs_ind' := Induction for InstantiateDefs Sort Prop.
Combined Scheme InstInstsBrsDefs_ind
         from Instantiate_ind', InstantiateBrs_ind', InstantiateDefs_ind'.

Lemma InstantiateBrs_pres_blength:
  forall n bs ibs, InstantiateBrs n bs ibs -> blength bs = blength ibs.
Proof.
  induction 1.
  + reflexivity.
  + simpl. intuition.
Qed.

Lemma InstantiateDefs_pres_dlength:
  forall n ds ids, InstantiateDefs n ds ids -> dlength ds = dlength ids.
Proof.
  induction 1.
  + reflexivity.
  + simpl. intuition.
Qed.

Lemma Instantiate_pres_isLambda:
  forall t, isLambda t ->
            forall n it, Instantiate n t it -> isLambda it.
Proof.
  intros t ht n it hit. dstrctn ht. subst.
  inversion_Clear hit. auto.
Qed.          

Lemma Instantiates_no_gen:
  ~ PoccTrm tin ->
  (forall n t s, Instantiate n t s -> PoccTrm s -> PoccTrm t) /\
  (forall n ts ss, InstantiateBrs n ts ss -> PoccBrs ss -> PoccBrs ts) /\
  (forall n ds es, InstantiateDefs n ds es -> PoccDefs es -> PoccDefs ds).
Proof.
  intro h. apply InstInstsBrsDefs_ind; intros; auto.
  - contradiction.
  - inversion H.
  - inversion_Clear H0. constructor. intuition.
  - inversion_Clear H1.
    + constructor. intuition. 
    + eapply PoLetInBod. intuition.
  - inversion_Clear H1.
    + constructor. intuition.
    + apply PoAppA. intuition.
  - inversion_clear H1.
    + constructor. 
    + eapply PoCaseL. intuition.
    + eapply PoCaseR. intuition.
  - inversion_Clear H0. constructor. intuition.
  - inversion H0. constructor. intuition.
  - inversion_Clear H1.
    + constructor. intuition.
    + apply PoBtl. intuition. 
  - inversion_Clear H1.
    + constructor. intuition. 
    + apply PoDtl. intuition. 
Qed.

Function instantiate (n:nat) (tbod:Term) {struct tbod} : Term :=
  match tbod with
    | TRel m => match Nat.compare n m with
                  | Datatypes.Eq => tin
                  | Gt => TRel m
                  | Lt => TRel (pred m)
                end
    | TProof => TProof
    | TApp t a => TApp (instantiate n t) (instantiate n a)
    | TLambda nm bod => TLambda nm (instantiate (S n) bod)
    | TCase np s ts => TCase np (instantiate n s) (instantiateBrs n ts)
    | TLetIn nm tdef bod =>
      TLetIn nm (instantiate n tdef) (instantiate (S n) bod)
    | TFix ds m => TFix (instantiateDefs (n + dlength ds) ds) m
    | TProj prj t => TProj prj (instantiate n t)
    | x => x
  end
with instantiateBrs (n:nat) (bs:Brs) {struct bs} : Brs :=
       match bs with
         | bnil => bnil
         | bcons m t ts => bcons m (instantiate n t) (instantiateBrs n ts)
       end
with instantiateDefs (n:nat) (ds:Defs) {struct ds} : Defs :=
       match ds with
         | dnil => dnil
         | dcons nm bod rarg ds =>
           dcons nm (instantiate n bod) rarg (instantiateDefs n ds)
       end.

(* Functional Scheme instantiate_ind' := Induction for instantiate Sort Prop *)
(* with instantiates_ind' := Induction for instantiates Sort Prop *)
(* with instantiateDefs_ind' := Induction for instantiateDefs Sort Prop. *)
(* Combined Scheme instantiateAll_ind *)
(*          from instantiate_ind', instantiates_ind', instantiateDefs_ind'. *)


Lemma instantiateDefs_pres_dlength:
  forall n ds, dlength ds = dlength (instantiateDefs n ds).
Proof.
  induction ds.
  + reflexivity.
  + simpl. intuition.
Qed.

(******* Instantiate and instantiate are same relations **********)
Lemma Instantiate_instantiate:
  (forall n t it, Instantiate n t it -> instantiate n t = it) /\
  (forall n ts its, InstantiateBrs n ts its -> instantiateBrs n ts = its) /\
  (forall n ds ids, InstantiateDefs n ds ids -> instantiateDefs n ds = ids).
Proof.
  apply InstInstsBrsDefs_ind; intros; simpl; intuition;
    try (subst; reflexivity).
  - rewrite nat_compare_EQ. reflexivity.
  - rewrite (proj1 (nat_compare_gt n m) g). reflexivity.
  - rewrite (proj1 (nat_compare_lt n m) l). reflexivity.
Qed.

Lemma instantiate_Instantiate:
  (forall t n, Instantiate n t (instantiate n t)) /\
  (forall bs n, InstantiateBrs n bs (instantiateBrs n bs)) /\
  (forall (ds:Defs) n, InstantiateDefs n ds (instantiateDefs n ds)).
Proof.
  apply TrmTrmsBrsDefs_ind; intros; simpl; try (solve [constructor]);
  try (solve[constructor; intuition]).  
  - destruct (lt_eq_lt_dec n0 n) as [[h | h] | h].
    + rewrite (proj1 (nat_compare_lt _ _) h). apply IRelLt. assumption.
    + rewrite (proj2 (NPeano.Nat.compare_eq_iff _ _) h). subst. apply IRelEq.
    + rewrite (proj1 (nat_compare_gt _ _)). apply IRelGt.
      assumption. assumption.
Qed.


Lemma instant_pres_PoccTrm:
  (forall tbod, PoccTrm tbod -> forall n, PoccTrm (instantiate n tbod)) /\
  (forall bs, PoccBrs bs -> forall n, PoccBrs (instantiateBrs n bs)) /\
  (forall Ds, PoccDefs Ds -> forall n, PoccDefs (instantiateDefs n Ds)).
Proof.
  apply poTrmTrmsBrsDefs_ind; intros; simpl; try solve [constructor; trivial].
Qed.

End Instantiate_sec.
End PoccTrm_sec.


Lemma instantiate_pres_WFapp:
  (forall bod, WFapp bod ->
              forall t, WFapp t -> forall n, WFapp (instantiate t n bod)) /\
  (forall bs, WFappBs bs ->
              forall t, WFapp t -> forall n, WFappBs (instantiateBrs t n bs)) /\
  (forall ds, WFappDs ds ->
              forall t, WFapp t -> forall n, WFappDs (instantiateDefs t n ds)).
Proof.
  apply WFappTrmsBrsDefs_ind; intros;
  try (solve [unfold instantiate; constructor]).
  - destruct (lt_eq_lt_dec n m) as [[h|h]|h]; unfold instantiate.
    + rewrite (proj1 (nat_compare_lt _ _) h). constructor.
    + rewrite (proj2 (NPeano.Nat.compare_eq_iff _ _) h). assumption.
    + rewrite (proj1 (nat_compare_gt _ _) h). constructor.
  - change (WFapp (TLambda nm (instantiate t (S n) bod))). constructor.
    + apply H0. assumption.
  - change (WFapp (TLetIn nm (instantiate t n dfn) (instantiate t (S n) bod))).
    constructor.
    + apply H0. assumption.
    + apply H2. assumption.
  - change (WFapp (TApp (instantiate t0 n fn) (instantiate t0 n t))).
    constructor.
    + apply H0. assumption.
    + apply H2. assumption.
  - change (WFapp (TCase m (instantiate t n mch) (instantiateBrs t n brs))).
    constructor.
    + apply H0; assumption.
    + apply H2; assumption.
  - change (WFapp (TFix (instantiateDefs t (n + dlength defs) defs) m)).
    constructor.
    + apply H0. assumption.
  - cbn. constructor. intuition.
  - change (WFappBs (bcons n (instantiate t n0 b)
                            (instantiateBrs t n0 bs))).
     constructor.
     + apply H0. assumption.
     + apply H2. assumption.
   - change (WFappDs (dcons nm (instantiate t n bod) arg
                            (instantiateDefs t n ds))).
     constructor.
     + apply H0. assumption.
     + apply H2. assumption.
Qed.


(** operations for weak reduction and weak evaluation **)
Definition whBetaStep (bod arg:Term) : Term := instantiate arg 0 bod.

Lemma whBetaStep_pres_WFapp:
  forall bod, WFapp bod -> forall arg, WFapp arg -> WFapp (whBetaStep bod arg).
Proof.
  intros bod hbod arg harg. unfold whBetaStep.
  apply instantiate_pres_WFapp; assumption.
Qed.


(****
Lemma not_isApp_whBetaStep:
  forall bod arg args, ~ isApp (whBetaStep bod arg args) ->
    args = tnil /\ ~ isApp (instantiate arg 0 bod).
induction bod; unfold whBetaStep; simpl; intros; split;
try not_isApp; destruct args; try reflexivity;
try (elim H; apply mkApp_isApp).
- unfold mkApp in H. destruct (instantiate arg 0 (TRel n)); try assumption.
******)


(***
Goal
  forall bod arg b bs, isApp (whBetaStep bod arg (tcons b bs)).
Proof.
  intros.
  change (isApp (whBetaStep bod arg (tappend tnil args))).
  rewrite <- whBetaStep_absorbs_mkApp.
***)


(*****
Lemma whBetaStep_noGen:
  forall nm t bod arg args, 
    PoccTrm nm t -> t = (whBetaStep bod arg args) ->
    PoccTrm nm bod \/ PoccTrm nm arg \/ PoccTrms nm args.
unfold whBetaStep. intros nm t bod arg args.
assert (j:= proj1 (instantiate_Instantiate arg)).

induction t.

unfold whBetaStep; simpl; induction 1; intros.
****)

Definition whCaseStep (cstrNbr:nat) (args:Terms) (brs:Brs): option Term := 
  match bnth cstrNbr brs with
    | Some (t, _) => Some (mkApp t args)
    | None => None
  end.

(***
Lemma mkApp_pres_WFTrm:
  forall n args, WFTrms args n ->
                   forall fn, WFTrm fn n ->
                              WFTrm (mkApp fn args) n.
Proof.
  induction 1; intros; cbn.
  - destruct fn; assumption.
  - assert (j: WFTrm (TApp fn t) n).
    { constructor; assumption. }
    specialize (IHWFTrms _ j). destruct fn; eassumption.
Qed.

Lemma mkApp_pres_WFapp:
  forall ts, WFapps ts -> forall t, WFapp t -> WFapp (mkApp t ts).
Proof.
  induction 1; intros s hs; inversion_Clear hs; cbn;
    try rewrite tappend_tnil; intuition;
      try (constructor; try not_isApp; try intros h; try discriminate;
           try constructor; try assumption);
      try (destruct h; discriminate); try contradiction.
Qed.
 ***)

Lemma bnth_pres_WFTrm:
  forall n (brs:Brs), WFTrmBs brs n ->
    forall m x ix, bnth m brs = Some (x, ix) -> WFTrm x n.
Proof.
  intros n brs h m x ix.
  functional induction (bnth m brs); intros; auto.
  - discriminate.
  - myInjection H. inversion_Clear h. assumption.
  - apply IHo; inversion h; assumption.
Qed.


Lemma whCaseStep_pres_WFapp:
  forall (brs:Brs), WFappBs brs -> forall ts, WFapps ts -> 
  forall (n:nat) (s:Term), whCaseStep n ts brs = Some s -> WFapp s.
Proof.
  intros brs hbrs ts hts n s h. unfold whCaseStep in h.
  case_eq (bnth n brs); intros; rewrite H in h.
  - destruct p. myInjection h. apply mkApp_pres_WFapp.
    + assumption.
    + eapply (bnth_pres_WFapp hbrs n). eassumption.
  - discriminate.
Qed.


(** Unfolding a Fixpoint **)
(** "dts" is a list of the mutual fixpoint definitions
*** "m" tells which of the definitions is being called
**)
Definition pre_whFixStep body dts arg : Term :=
  let f := fold_left
             (fun bod ndx => instantiate (TFix dts ndx) 0 bod)
             (list_to_zero (dlength dts)) body in
  (TApp f arg).
Functional Scheme pre_whFixStep_ind := Induction for pre_whFixStep Sort Prop.

Lemma pre_whFixStep_dunit:
  forall nm bod d arg,
    pre_whFixStep bod (dunit nm d 0) arg =
    TApp (instantiate (TFix (dunit nm d 0) 0) 0 bod) arg.
Proof.
  intros. unfold pre_whFixStep, dlength, list_to_zero.
  reflexivity.
Qed.
  
Lemma fold_left_pres_WFTrm:
  forall (f:Term -> nat -> Term) (ns:list nat) (a:nat),
    (forall u m, m >= a ->
                 WFTrm u (S m) -> forall n, In n ns -> WFTrm (f u n) m) ->
    forall t, WFTrm t (a + List.length ns) -> WFTrm (fold_left f ns t) a.
Proof.
  intros f. induction ns; cbn; intros.
  - replace (a + 0) with a in H0. assumption. lia.
  - apply IHns.
    + intros. apply H; try assumption. apply (or_intror H3).
    + replace (a0 + S (Datatypes.length ns))
        with (S (a0 + (Datatypes.length ns))) in H0.
      assert (j: a0 + Datatypes.length ns >= a0). lia.
      specialize (H t _ j H0).
      apply H. apply (or_introl eq_refl). lia.
Qed.

Lemma fold_left_pres_WFapp:
  forall (f:Term -> nat -> Term) (ns:list nat) (t:Term),
    (forall u, WFapp u -> forall n, WFapp (f u n)) ->
    WFapp t -> WFapp (fold_left f ns t).
Proof.
  intros f. induction ns; simpl; intros.
  - assumption.
  - apply IHns.
    + intros. apply H. assumption.
    + apply H. assumption.
Qed.

Lemma pre_whFixStep_pres_WFapp:
  forall  (bod:Term) (dts:Defs) (arg:Term),
    WFapp bod -> WFappDs dts -> WFapp arg ->
        WFapp (pre_whFixStep bod dts arg).
Proof.
  intros bod dts arg hbod hdts hargs.
  unfold pre_whFixStep. constructor; try assumption.
  apply fold_left_pres_WFapp; try assumption.
  intros. eapply (proj1 instantiate_pres_WFapp).
  + assumption.
  + constructor. assumption.
Qed.
