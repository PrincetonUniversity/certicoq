
(****)
Add LoadPath "../common" as Common.
Add LoadPath "../L1_QuotedCoq" as L1.
Add LoadPath "../L1g" as L1g.
(****)


Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import Ascii.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.omega.Omega.
Require Export Common.Common.
Require Export L1.term.
Require Export L1g.compile.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

(** Printing terms in exceptions for debugging purposes **)
Fixpoint print_term (t:Term) : string :=
  match t with
    | TRel n => " (" ++ (nat_to_string n) ++ ") "
    | TSort _ => " SRT "
    | TCast _ _ _ => " CAST "
    | TProd _ _ _ => " PROD "
    | TLambda _ _ _ => " LAM "
    | TLetIn _ _ _ _ => " LET "
    | TApp fn arg args =>
      " (APP" ++ (print_term fn) ++ (print_term arg) ++ " _ " ++ ") "
    | TConst s => "[" ++ s ++ "]"
    | TInd _ => " TIND "
    | TConstruct _ n => " (CSTR " ++ (nat_to_string n) ++ ") "
    | TCase n _ mch _ =>
      " (CASE " ++ (nat_to_string (fst n)) ++ " _ " ++ (print_term mch) ++
                 " _ " ++") "
    | TFix _ n => " (FIX " ++ (nat_to_string n) ++ ") "
  end.

Section TermTerms_dec. (** to make Ltac definitions local **)
Local Ltac rght := right; injection; intuition.
Local Ltac lft := left; subst; reflexivity.
Local Ltac cross := try (solve [right; intros h; discriminate]).
Lemma TermTerms_dec: 
  (forall (s t:Term), s = t \/ s <> t) /\
  (forall (ss tt:Terms), ss = tt \/ ss <> tt) /\
  (forall (dd ee:Defs), dd = ee \/ dd <> ee).
Proof.
  apply TrmTrmsDefs_ind.
  - Case "TRel". destruct t; cross. destruct (eq_nat_dec n n0); [lft | rght].
  - Case "TSort". destruct t; cross. destruct (Srt_dec s s0); [lft | rght].
  - destruct t1; cross.
    destruct (cast_kind_dec c c0); destruct (H t1_1); destruct (H0 t1_2);
    [lft | rght ..]. 
  - destruct t1; cross.
    destruct (name_dec n n0);
      destruct (H t1_1); destruct (H0 t1_2); [lft | rght ..]. 
  - destruct t1; cross.
    destruct (name_dec n n0);
      destruct (H t1_1); destruct (H0 t1_2); [lft | rght ..]. 
  - destruct t2; cross.
    destruct (name_dec n n0);
      destruct (H t2_1); destruct (H0 t2_2); destruct (H1 t2_3); 
      [lft | rght ..]. 
  - destruct t2; cross.
    destruct (H t2_1); destruct (H0 t2_2); destruct (H1 t2); [lft | rght ..].
  - destruct t; cross. destruct (string_dec s s0); [lft | rght].
  - destruct t; cross. destruct (inductive_dec i i0); [lft | rght].
  - destruct t; cross.
    destruct (inductive_dec i i0); destruct (eq_nat_dec n n0); [lft | rght .. ].
  - destruct t2; cross. destruct p as [n l], p0 as [n0 l0].
    + destruct (eq_nat_dec n n0); destruct (nat_list_dec l l0);
      destruct (H t2_1); destruct (H0 t2_2);
      destruct (H1 t2); [lft | rght .. ].
  - destruct t; cross.
    destruct (eq_nat_dec n n0); destruct (H d0); [lft | rght .. ].
  - destruct tt; cross. lft.
  - destruct tt; cross. destruct (H t1); destruct (H0 tt); [lft | rght .. ].
  - destruct ee; cross. lft.
  - destruct ee; cross.
    destruct (name_dec n n1); destruct (eq_nat_dec n0 n2);
    destruct (H t1); destruct (H0 t2); destruct (H1 ee); [lft | rght .. ].
Qed.
End TermTerms_dec.

Definition Term_dec := proj1 TermTerms_dec.
Definition Terms_dec := proj1 (proj2 TermTerms_dec).


Fixpoint TrmSize (t:Term) : nat :=
  match t with
    | TProd _ ty bod => S (TrmSize bod + TrmSize ty)
    | TLambda _ ty bod => S (TrmSize bod + TrmSize ty)
    | TLetIn _ dfn ty bod => S (TrmSize dfn + TrmSize ty + TrmSize bod)
    | TApp fn a args => S (TrmSize fn + TrmSize a + TrmsSize args)
    | TCase _ ty mch brs => S (TrmSize ty + TrmSize mch + TrmsSize brs)
    | TFix ds _ => S (TrmDsSize ds)
    | TCast t _ ty => S (TrmSize t + TrmSize ty)
    | _ => 1
  end
with TrmsSize (ts:Terms) : nat :=
  match ts with
    | tnil => 1
    | tcons s ss => S (TrmSize s + TrmsSize ss)
  end
with TrmDsSize (ds:Defs) : nat :=
  match ds with
    | dnil => 1
    | dcons _ t1 t2 _ es => S (TrmSize t1 + TrmSize t2 + TrmDsSize es)
  end.

Definition isLambda (t:Term) : Prop :=
  exists nm ty bod, t = TLambda nm ty bod.
Lemma IsLambda: forall nm ty bod, isLambda (TLambda nm ty bod).
intros. exists nm, ty, bod. reflexivity.
Qed.
Hint Resolve IsLambda.

Ltac not_isLambda :=
  let hh := fresh "h"
  with xx := fresh "x"
  with jj := fresh "j"
  with yy := fresh "y"
  with zz := fresh "z" in
  intros hh; destruct hh as [xx [yy [zz jj]]]; discriminate.

Lemma isLambda_dec: forall t, {isLambda t}+{~ isLambda t}.
induction t;
  try (solve [right; intros h; unfold isLambda in h;
              elim h; intros x h1; elim h1; intros x0 h2;
              elim h2; intros x1 h3; discriminate]).
left. auto.
Qed.

Definition isCast (t:Term) : Prop :=
  exists tm ck ty, t = TCast tm ck ty.
Lemma IsCast: forall t ck ty, isCast (TCast t ck ty).
intros. exists t, ck, ty. reflexivity.
Qed.
Hint Resolve IsCast.

Lemma isCast_dec: forall t, {isCast t}+{~ isCast t}.
induction t;
  try (solve [right; intros h; unfold isCast in h;
              destruct h as [tm [ck [ty j]]]; discriminate]).
left. auto.
Qed.

Definition isApp (t:Term) : Prop :=
  exists fn arg args, t = TApp fn arg args.
Lemma IsApp: forall fn arg args, isApp (TApp fn arg args).
intros. exists fn, arg, args. reflexivity.
Qed.
Hint Resolve IsApp.

Ltac not_isApp :=
  let hh := fresh "h"
  with xx := fresh "x"
  with jj := fresh "j"
  with yy := fresh "y"
  with zz := fresh "z" in
  intros hh; destruct hh as [xx [yy [zz jj]]]; discriminate.
Ltac isApp_inv h :=
  let hh := fresh "h"
  with xx := fresh "x"
  with yy := fresh "y"
  with zz := fresh "z"
  with jj := fresh "j"
  in destruct h as [xx [yy [zz jj]]]; discriminate.
Ltac isApp :=
  let hh := fresh "h"
  with xx := fresh "x"
  with jj := fresh "j"
  with yy := fresh "y"
  with kk := fresh "k"
  with zz := fresh "z"
  with ll := fresh "l" in
  intros hh; destruct hh as [xx jj]; destruct jj as [yy kk];
  destruct kk as [zz ll].

Lemma isApp_dec: forall t, {isApp t}+{~ isApp t}.
destruct t; try (right; not_isApp). 
left. auto.
Qed.

Definition isCastApp (t:Term) : Prop :=
  exists fn arg args ck ty, t = TCast (TApp fn arg args) ck ty.
Lemma IsAppCast:
  forall fn arg args ck ty, isCastApp (TCast (TApp fn arg args) ck ty).
intros. unfold isCastApp.
exists fn, arg, args, ck, ty. reflexivity.
Qed.
Hint Resolve IsAppCast.

Lemma isCastApp_dec: forall t, {isCastApp t}+{~ isCastApp t}.
destruct t;
  try (solve [right; intros h;
            destruct h as [x1 [x2 [x3 [x4 [x5 h]]]]]; discriminate]).
destruct t1;
  try (solve [right; intros h;
            destruct h as [x1 [x2 [x3 [x4 [x5 h]]]]]; discriminate]).
left. exists t1_1, t1_2, t, c, t2. reflexivity.
Qed.

Definition isFix (t:Term) : Prop :=
  exists ds n, t = TFix ds n.
Lemma IsFix: forall ds n, isFix (TFix ds n).
intros. exists ds, n. reflexivity.
Qed.
Hint Resolve IsFix.

Ltac not_isFix :=
  let hh := fresh "h"
  with xx := fresh "x"
  with jj := fresh "j"
  with yy := fresh "y" in
  intros hh; destruct hh as [xx [yy jj]]; discriminate.

Lemma isFix_dec: forall t, {isFix t}+{~ isFix t}.
induction t;
  try (solve [right; intros h; unfold isFix in h;
              elim h; intros x h1; elim h1; intros x0 h2; discriminate]).
left. auto.
Qed.

Definition isConstruct (t:Term) : Prop :=
  exists i n, t = TConstruct i n.
Lemma IsConstruct: forall i n, isConstruct (TConstruct i n).
intros. exists i, n. reflexivity.
Qed.
Hint Resolve IsConstruct.

Lemma isConstruct_dec: forall t, isConstruct t \/ ~ isConstruct t.
induction t;
try (solve [right; unfold isConstruct; intros h; elim h;
            intros x1 h1; elim h1; intros x2 h2; discriminate]).
- left. auto.
Qed.

Inductive isCanonical : Term -> Prop :=
| canC: forall (i:inductive) (n:nat), isCanonical (TConstruct i n)
| canA: forall (arg:Term) (args:Terms) (i:inductive) (n:nat), 
          isCanonical (TApp (TConstruct i n) arg args).
Hint Constructors isCanonical.

Lemma IsCanonical:
  (forall i n, isCanonical (TConstruct i n)) /\
  (forall i n t ts, isCanonical (TApp (TConstruct i n) t ts)).
split; intros; auto.
Qed.
Hint Resolve IsCanonical.

Lemma isCanonical_dec: forall t, isCanonical t \/ ~ isCanonical t.
induction t;
  try (solve [right; intros h; inversion h; inversion H;
              destruct H1; discriminate]).
- destruct (isConstruct_dec t1).
  + left. unfold isConstruct in H. destruct H as [x0 [x1 j]]. subst.
    constructor.
  + right. intros h. inversion_Clear h. elim H. auto.
- left. constructor.
Qed.

Function canonicalP (t:Term) : exception (nat * Terms) :=
  match t with
    | TConstruct _ r => ret (r, tnil)
    | TApp (TConstruct _ r) arg args => ret (r, tcons arg args)
    | x => raise ("canonicalP: " ++ (print_term x))
  end.

Lemma canonicalP_isCanonical:
  forall t x, canonicalP t = Ret x -> isCanonical t.
Proof.
  induction t; simpl; intros; try discriminate.
  - destruct t1; try discriminate. constructor.
  - constructor.
Qed.

Lemma isCanonical_canonicalP:
  forall t, isCanonical t -> exists x, canonicalP t = Ret x.
Proof.
  induction 1; simpl.
  - exists (n, tnil). reflexivity.
  - exists (n, tcons arg args). reflexivity.
Qed.

Function appliedAxiomP (t:Term) : bool :=
  match t with
    | TConst _ => true
    | TApp (TConst _) arg args => true
    | _ => false
  end.
    
Open Scope string_scope.
Lemma appliedAxiomP_canonicalP:
  forall mch, appliedAxiomP mch = true -> exists z, canonicalP mch = Exc z.
Proof.
  intros mch. functional induction (appliedAxiomP mch); intros; try discriminate.
  - simpl. exists ("canonicalP: [" ++  _x ++ "]"). reflexivity.
  - simpl. unfold raise.
    exists  (String "c"
          (String "a"
             (String "n"
                (String "o"
                   (String "n"
                      (String "i"
                         (String "c"
                            (String "a"
                               (String "l"
                                  (String "P"
                                     (String ":"
                                        (String " "
                                           (String " "
                                              (String "("
                                                 (String "A"
                                                 (String "P"
                                                 (String "P"
                                                 (String "["
                                                 ((_x ++ "]") ++
                                                              print_term arg ++ " _ ) "))))))))))))))))))).
    reflexivity.
Qed.


(** some utility operations on [Terms] ("lists" of Term) **)
Fixpoint tlength (ts:Terms) : nat :=
  match ts with 
    | tnil => 0
    | tcons _ ts => S (tlength ts)
  end.

Function tappend (ts1 ts2:Terms) : Terms :=
  match ts1 with
    | tnil => ts2
    | tcons t ts => tcons t (tappend ts ts2)
  end.

Lemma tappend_tnil: forall ts:Terms, tappend ts tnil = ts.
induction ts; simpl; try reflexivity.
rewrite IHts. reflexivity.
Qed.
Hint Rewrite tappend_tnil : tappend.

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

Lemma tappend_mk_canonical:
  forall ts s ss, exists u us, (tappend ts (tcons s ss)) = tcons u us.
Proof.
  destruct ts; intros s ss; simpl.
  - exists s, ss. reflexivity.
  - exists t, (tappend ts (tcons s ss)). reflexivity.
Qed.

Lemma tlength_tappend:
  forall ts us, tlength (tappend ts us) = (tlength ts) + (tlength us).
Proof.
  induction ts; simpl; intros; try reflexivity.
  - rewrite IHts. reflexivity.
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

Function tskipn (n:nat) (l:Terms) : option Terms :=
  match n, l with
    | 0, l => Some l
    | S n, tcons a l => tskipn n l
    | S _, tnil => None
  end.

Function tnth (n:nat) (l:Terms) {struct l} : option Term :=
  match l with
    | tnil => None
    | tcons x xs => match n with
                      | 0 => Some x
                      | S m => tnth m xs
                    end
  end.

Lemma tnth_extend1:
  forall n l t,  tnth n l = Some t -> n < tlength l.
Proof.
  induction n; induction l; simpl; intros; try discriminate; try omega.
  - apply lt_n_S. eapply IHn. eassumption.
Qed.

Lemma tnth_extend2:
  forall n l,  n < tlength l -> exists t, tnth n l = Some t.
Proof.
  induction n; intros.
  - destruct l. simpl in H. omega. exists t. reflexivity.
  - destruct l. inversion H. simpl in H.
    specialize (IHn _ (lt_S_n _ _ H)). destruct IHn. exists x. simpl. assumption.
Qed.

Lemma tnth_append:
  forall n args t, tnth n args = Some t ->
            forall brgs, tnth n (tappend args brgs) = Some t.
Proof.
  induction n; induction args; simpl; intros; try discriminate; try assumption.
  - apply IHn. assumption.
Qed.


(** operations on Defs **)
Fixpoint dlength (ts:Defs) : nat :=
  match ts with 
    | dnil => 0
    | dcons _ _ _ _ ts => S (dlength ts)
  end.

Function dnthBody (n:nat) (l:Defs) {struct l} : option (Term * nat) :=
  match l with
    | dnil => None
    | dcons _ _ x ix t => match n with
                           | 0 => Some (x, ix)
                           | S m => dnthBody m t
                         end
  end.


(** syntactic control of "TApp": no nested apps, app must have an argument **)
Function mkApp (t:Term) (args:Terms) {struct t} : Term :=
  match t with
    | TApp fn b bs => TApp fn b (tappend bs args)
    | fn => match args with
              | tnil => fn
              | tcons c cs => TApp fn c cs
            end
  end.

Lemma mkApp_tnil_ident: forall t, mkApp t tnil = t.
  destruct t; simpl; try rewrite tappend_tnil; try reflexivity.
Qed.

Inductive MkApp :Term -> Terms -> Term -> Prop :=
| maApp: forall fn b bs cs,
           MkApp (TApp fn b bs) cs (TApp fn b (tappend bs cs))
| maNil: forall fn, ~ isApp fn -> MkApp fn tnil fn
| maCons: forall fn c cs, ~ isApp fn -> MkApp fn (tcons c cs) (TApp fn c cs).
Hint Constructors MkApp.

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

(*******
Lemma mkApp_character:
  forall fn args, ~ isApp (mkApp fn args) \/
   (exists fn' arg' args', mkApp fn args = TApp fn' arg' args' /\ ~ isApp fn').
Proof.
  intros fn args.
  functional induction (mkApp fn args).
  - destruct IHt.
    + left. assumption.
    + right. assumption.
  - destruct t; try (left; not_isApp). elim y.
  - destruct t. 
    + right. exists (TRel n), c, cs. intuition. isApp_inv H.
    + right. exists (TSort s), c, cs. intuition. isApp_inv H.
    + right. exists (TCast t1 c0 t2), c, cs. intuition. isApp_inv H.
    + right. exists (TProd n t1 t2), c, cs. intuition. isApp_inv H.
    + right. exists (TLambda n t1 t2), c, cs. intuition. isApp_inv H.
    + right. exists (TLetIn n t1 t2 t3), c, cs. intuition. isApp_inv H.
    + left. elim y.
    + right. exists (TConst s), c, cs. intuition. isApp_inv H.
    + right. exists (TInd i), c, cs. intuition. isApp_inv H.
    + right. exists (TConstruct i n), c, cs. intuition. isApp_inv H.
    + right. exists (TCase n t1 t2 t3), c, cs. intuition. isApp_inv H.
    + right. exists (TFix d n), c, cs. intuition. isApp_inv H.
Qed.
***)

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
  - exists (TCast fn1 c fn2), arg, tnil. split. reflexivity.
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
  * omega.
  * apply tIn_tappend1.
- exists (TConst s), arg, tnil. split. reflexivity.
  left. intuition. revert H. not_isApp.
- exists (TInd i), arg, tnil. split. reflexivity.
  left. intuition. revert H. not_isApp.
- exists (TConstruct i n), arg, tnil. split. reflexivity.
  left. intuition. revert H. not_isApp.
- exists (TCase p fn1 fn2 t), arg, tnil. split. reflexivity.
  left. intuition. revert H. not_isApp.
- exists (TFix d n), arg, tnil. split. reflexivity.
  left. intuition. revert H. not_isApp.
Qed.

(** well-formed terms: TApp well-formed all the way down **)
Inductive WFapp: Term -> Prop :=
| wfaRel: forall m, WFapp (TRel m)
| wfaSort: forall srt, WFapp (TSort srt)
| wfaCast: forall tm ck ty, WFapp tm -> WFapp ty -> WFapp (TCast tm ck ty)
| wfaProd: forall nm ty bod,
            WFapp bod -> WFapp ty -> WFapp (TProd nm ty bod)
| wfaLambda: forall nm ty bod,
            WFapp bod -> WFapp ty -> WFapp (TLambda nm ty bod)
| wfaLetIn: forall nm dfn ty bod,
             WFapp dfn -> WFapp bod -> WFapp ty -> 
             WFapp (TLetIn nm dfn ty bod)
| wfaApp: forall fn t ts,
           ~ (isApp fn) -> WFapp fn -> WFapp t -> WFapps ts ->
           WFapp (TApp fn t ts)
| wfaConst: forall nm, WFapp (TConst nm)
| wfaInd: forall i, WFapp (TInd i)
| wfaConstruct: forall i m1, WFapp (TConstruct i m1)
| wfaCase: forall m ty mch brs,
            WFapp mch -> WFapps brs -> WFapp ty ->
            WFapp (TCase m ty mch brs)
| wfaFix: forall defs m, WFappDs defs -> WFapp (TFix defs m)
with WFapps: Terms -> Prop :=
| wfanil: WFapps tnil
| wfacons: forall t ts, WFapp t -> WFapps ts -> WFapps (tcons t ts)
with WFappDs: Defs -> Prop :=
| wfadnil: WFappDs dnil
| wfadcons: forall nm ty bod arg ds,
             WFapp ty -> WFapp bod -> WFappDs ds ->
             WFappDs (dcons nm ty bod arg ds).
Hint Constructors WFapp WFapps WFappDs.
Scheme WFapp_ind' := Minimality for WFapp Sort Prop
  with WFapps_ind' := Minimality for WFapps Sort Prop
  with WFappDs_ind' := Minimality for WFappDs Sort Prop.
Combined Scheme WFappTrmsDefs_ind from WFapp_ind', WFapps_ind', WFappDs_ind'.

Lemma tappend_pres_WFapps:
  forall ts, WFapps ts -> forall us, WFapps us -> WFapps (tappend ts us).
Proof.
  induction 1; intros us hus; simpl.
  - assumption.
  - constructor. assumption. apply IHWFapps. assumption.
Qed.

Lemma canonicalP_pres_WFapp:
  forall t, WFapp t ->
        forall r args, canonicalP t = Ret (r, args) -> WFapps args.
Proof.
  induction t; simpl; intros; try discriminate.
  - destruct t1; try discriminate. myInjection H0. inversion_Clear H.
    constructor; assumption.
  - myInjection H0. constructor.
Qed.

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


Lemma mkApp_pres_WFapp:
  forall ts, WFapps ts -> forall t, WFapp t -> WFapp (mkApp t ts).
Proof.
  induction 1; intros s hs; inversion_Clear hs; simpl; intuition;
  try (constructor; [not_isApp | constructor; assumption| assumption .. ]).
  - rewrite tappend_tnil. constructor; assumption.
  - constructor; try assumption.
    + apply tappend_pres_WFapps. assumption. constructor; assumption.
Qed.

Lemma tnth_pres_WFapp:
  forall (brs:Terms), WFapps brs -> forall n t, tnth n brs = Some t -> WFapp t.
Proof.
  intros brs h n t.
  functional induction (tnth n brs); intros; try discriminate.
  - injection H; intros; subst. inversion h. assumption.
  - apply IHo; inversion h; assumption.
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

Lemma tskipn_pres_WFapp:
  forall args, WFapps args -> forall np ts, tskipn np args = Some ts ->
   WFapps ts.
  intros args hargs np ts h.
  functional induction (tskipn np args).
  - injection h. intros. subst. assumption.
  - inversion_Clear hargs. apply IHo; try assumption.
  - discriminate.
Qed.

(** compiling well formed terms to Term produces well formed Terms **)
Lemma terms_Terms_map_lem:
  forall (brs:list (nat * term)),
    terms_Terms term_Term (map snd brs) =
    terms_Terms (fun x : nat * term => term_Term (snd x)) brs.
Proof.
  induction brs; cbn. reflexivity.
  rewrite IHbrs. reflexivity.
Qed.

Lemma wf_notisApp_notisApp:
  forall fn, wf_term fn -> ~ L1.term.isApp fn ->
               forall x, term_Term fn = Ret x -> ~ isApp x.
Proof.
  destruct fn; cbn; intros h0 h1 y hy; intros;
  try discriminate; try (myInjection hy; not_isApp);
  inversion_Clear h0;
  try destruct (term_Term fn3); try destruct (term_Term fn2);
  try destruct (term_Term fn1); try destruct (term_Term fn); try discriminate;
  try myInjection hy; try not_isApp.
  - elim h1. exists fn, (u :: us). reflexivity.
  - destruct (terms_Terms (fun x : nat * term => term_Term (snd x)) l);
    discriminate.
  - destruct (terms_Terms (fun x : nat * term => term_Term (snd x)) l);
    try discriminate.
    myInjection hy. not_isApp.
  - destruct (defs_Defs term_Term m); try discriminate.
    myInjection hy. not_isApp.
Qed.
       

Lemma term_Term_pres_WFapp:
  forall n,
    (forall (t:term),
       WF_term n t = true ->
       exists T, term_Term t = Ret T /\ WFapp T) /\
  (forall (ts:list term),
     WF_terms n ts = true ->
     exists Ts, terms_Terms term_Term ts = Ret Ts /\ WFapps Ts) /\
  (forall (ds:list (def term)),
     WF_defs n ds = true ->
     exists Ds, defs_Defs term_Term ds = Ret Ds /\ WFappDs Ds).
Proof.
  apply (WF_term_terms_defs_ind
    (fun (m:nat) (t:term) (q:bool) =>
       WF_term m t = true -> exists T, term_Term t = Ret T /\ WFapp T)
    (fun (m:nat) (ts:list term) (q:bool) =>
       WF_terms m ts = true ->
       exists Ts, terms_Terms term_Term ts = Ret Ts /\ WFapps Ts)
    (fun (m:nat) (ds:list (def term)) (q:bool) =>
       WF_defs m ds = true ->
       exists Ds, defs_Defs term_Term ds = Ret Ds /\ WFappDs Ds));
  intros; cbn in H; try discriminate.
  - exists (TRel n1). split. reflexivity. constructor.
  - exists (TSort (match srt with 
                    | sProp => SProp
                    | sSet => SSet
                    | sType _ => SType  (* throwing away sort info *)
                   end)). split. reflexivity. constructor.
  - cbn in H1. destruct (proj1 (andb_true_iff _ _) H1) as [j1 j2].
    destruct (H j1) as [x0 [k0 k2]]. destruct (H0 j2) as [x1 [k1 k3]].
    exists (TCast x1 ck x0). cbn. split.
    + rewrite k1. rewrite k0. reflexivity.
    + constructor; assumption.
  - cbn in H1. destruct (proj1 (andb_true_iff _ _) H1) as [j1 j2].
    destruct (H j1) as [x0 [k0 k2]]. destruct (H0 j2) as [x1 [k1 k3]].
    exists (TProd nm x0 x1). cbn. split.
    + rewrite k0. rewrite k1. reflexivity.
    + constructor; assumption.
  - cbn in H1. destruct (proj1 (andb_true_iff _ _) H1) as [j1 j2].
    destruct (H j1) as [x0 [k0 k2]]. destruct (H0 j2) as [x1 [k1 k3]].
    exists (TLambda nm x0 x1). cbn. split.
    + rewrite k0. rewrite k1. reflexivity.
    + constructor; assumption.     
  - cbn in H2.
    destruct (proj1 (andb_true_iff _ _) H2) as [j1 j2].
    destruct (proj1 (andb_true_iff _ _) j1) as [j3 j4].
    destruct (H j3) as [x0 [k0 p0]].
    destruct (H0 j4) as [x1 [k1 p1]].
    destruct (H1 j2) as [x2 [k2 p2]].
    exists (TLetIn nm x0 x1 x2). cbn. split.
    + rewrite k0. rewrite k1. rewrite k2. reflexivity.
    + constructor; assumption.
  - cbn in H2.
    destruct (proj1 (andb_true_iff _ _) H2) as [j1 j2].
    destruct (proj1 (andb_true_iff _ _) j1) as [j3 j4].
    destruct (proj1 (andb_true_iff _ _) j3) as [j5 j6].
    destruct (H j6) as [x0 [k0 p0]].
    destruct (H0 j4) as [x1 [k1 p1]].
    destruct (H1 j2) as [x2 [k2 p2]].
    exists (TApp x0 x1 x2). cbn. split.
    + rewrite k0. rewrite k1. rewrite k2. reflexivity.
    + constructor; try assumption. 
     inversion p0; subst; unfold isNotApp in j5; try not_isApp.
     refine (wf_notisApp_notisApp _ _ _); try eassumption.
      * refine (proj1 (WF_wf_term n0) _ _). assumption.
      * intros k. destruct k as [y0 [y1 j]]. subst. discriminate.
  - exists (TConst pth). split. reflexivity. constructor.
  - exists (TInd ind). split. reflexivity. constructor.
  - exists (TConstruct ind m). split. reflexivity. constructor.
  - cbn in H2.
    destruct (proj1 (andb_true_iff _ _) H2) as [j1 j2].
    destruct (proj1 (andb_true_iff _ _) j1) as [j3 j4].
    destruct (H j3) as [x0 [k0 k0a]].
    destruct (H0 j4) as [x1 [k1 k1a]].
    destruct (H1 j2) as [x2 [k2 k2a]].
    exists (TCase (npars, map fst brs) x0 x1 x2). split.
    + cbn. rewrite k1.
      rewrite terms_Terms_map_lem in k2. rewrite k2.
      rewrite k0. reflexivity.
    + constructor; assumption.
  - cbn in H0. destruct (H H0) as [x0 [k0 k0a]].
    exists (TFix x0 m). cbn. rewrite k0. split. reflexivity.
    constructor. assumption.
  - subst. destruct _x; try contradiction; cbn in H; try discriminate.
    destruct l. discriminate. contradiction.
  - subst. exists tnil. split. reflexivity. constructor.
  - subst. cbn in H1. destruct (proj1 (andb_true_iff _ _) H1) as [j1 j2].
    destruct (H j1) as [x0 [k0 k0a]]. destruct (H0 j2) as [x1 [k1 k1a]].
    exists (tcons x0 x1). split. cbn. rewrite k0. rewrite k1. reflexivity.
    constructor; assumption.
  - subst. exists dnil. split. reflexivity. constructor.
  - subst. cbn in H2.
    destruct (proj1 (andb_true_iff _ _) H2) as [j1 j2].
    destruct (proj1 (andb_true_iff _ _) j1) as [j3 j4].
    destruct (H j3) as [x0 [k0 k0a]].
    destruct (H0 j4) as [x1 [k1 k1a]].
    destruct (H1 j2) as [x2 [k2 k2a]].
    exists (dcons (dname term c) x0 x1 (rarg term c) x2). cbn. split.
    rewrite k0. rewrite k1. rewrite k2. reflexivity.
    constructor; assumption.
Qed.



(** well-formed terms: TApp well-formed all the way down **)
(*** not used essentially at the moment **)
Inductive WFTrm: Term -> nat -> Prop :=
| wfRel: forall n m, m < n -> WFTrm (TRel m) n
| wfSort: forall n srt, WFTrm (TSort srt) n
| wfCast: forall n t ck ty, WFTrm t n -> WFTrm ty n -> WFTrm (TCast t ck ty) n
| wfProd: forall n nm ty bod,
            WFTrm bod (S n) -> WFTrm ty n -> WFTrm (TProd nm ty bod) n
| wfLambda: forall n nm ty bod,
            WFTrm bod (S n) -> WFTrm ty n -> WFTrm (TLambda nm ty bod) n
| wfLetIn: forall n nm dfn ty bod,
             WFTrm dfn n -> WFTrm bod (S n) -> WFTrm ty n -> 
             WFTrm (TLetIn nm dfn ty bod) n
| wfApp: forall n fn t ts,
           ~ (isApp fn) -> WFTrm fn n -> WFTrm t n -> WFTrms ts n ->
           WFTrm (TApp fn t ts) n
| wfConst: forall n nm, WFTrm (TConst nm) n
| wfInd: forall n i, WFTrm (TInd i) n
| wfConstruct: forall n i m1, WFTrm (TConstruct i m1) n
| wfCase: forall n m ty mch brs,
            WFTrm mch n -> WFTrms brs n -> WFTrm ty n ->
            WFTrm (TCase m ty mch brs) n
| wfFix: forall n defs m,
           WFTrmDs defs (n + dlength defs) -> WFTrm (TFix defs m) n
with WFTrms: Terms -> nat -> Prop :=
| wfnil: forall n, WFTrms tnil n
| wfcons: forall n t ts, WFTrm t n -> WFTrms ts n -> WFTrms (tcons t ts) n
with WFTrmDs: Defs -> nat -> Prop :=
| wfdnil: forall n, WFTrmDs dnil n
| wfdcons: forall n nm ty bod arg ds,
             WFTrm ty n -> WFTrm bod n -> WFTrmDs ds n ->
             WFTrmDs (dcons nm ty bod arg ds) n.
Hint Constructors WFTrm WFTrms WFTrmDs.
Scheme WFTrm_ind' := Minimality for WFTrm Sort Prop
  with WFTrms_ind' := Minimality for WFTrms Sort Prop
  with WFTrmDs_ind' := Minimality for WFTrmDs Sort Prop.
Combined Scheme WFTrmTrmsDefs_ind from WFTrm_ind', WFTrms_ind', WFTrmDs_ind'.

Lemma WFTrm_WFapp:
  (forall t n, WFTrm t n -> WFapp t) /\
  (forall ts n, WFTrms ts n -> WFapps ts) /\
  (forall ds n, WFTrmDs ds n -> WFappDs ds).
Proof.
  apply WFTrmTrmsDefs_ind; intros; try (constructor; try assumption).
Qed.


(*** Some basic operations and properties of [Term] ***)

(** occurrances of a constant in a term (ignoring type components) **)
Section PoccTrm_sec.
Variable nm:string.

Inductive PoccTrm : Term -> Prop :=
| PoProdBod: forall s ty bod, PoccTrm bod -> PoccTrm (TProd s ty bod)
| PoProdTy: forall s ty bod, PoccTrm ty -> PoccTrm (TProd s ty bod)
| PoLambdaBod: forall s ty bod, PoccTrm bod -> PoccTrm (TLambda s ty bod)
| PoLambdaTy: forall s ty bod, PoccTrm ty -> PoccTrm (TLambda s ty bod)
| PoCastTm: forall t ck ty, PoccTrm t -> PoccTrm (TCast t ck ty)
| PoCastTy: forall t ck ty, PoccTrm ty -> PoccTrm (TCast t ck ty)
| PoLetInDfn: forall s ty dfn bod,
                PoccTrm dfn -> PoccTrm (TLetIn s dfn ty bod)
| PoLetInBod: forall s ty dfn bod,
                PoccTrm bod -> PoccTrm (TLetIn s dfn ty bod)
| PoLetInTy: forall s ty dfn bod,
                PoccTrm ty -> PoccTrm (TLetIn s dfn ty bod)
| PoAppL: forall fn a args, PoccTrm fn -> PoccTrm (TApp fn a args)
| PoAppA: forall fn a args, PoccTrm a -> PoccTrm (TApp fn a args)
| PoAppR: forall fn a args, PoccTrms args -> PoccTrm (TApp fn a args)
| PoConst: PoccTrm (TConst nm)
| PoCaseL: forall n ty mch brs, PoccTrm mch -> PoccTrm (TCase n ty mch brs)
| PoCaseR: forall n ty mch brs, PoccTrms brs -> PoccTrm (TCase n ty mch brs)
| PoCaseTy: forall n ty mch brs, PoccTrm ty -> PoccTrm (TCase n ty mch brs)
| PoFix: forall ds m, PoccDefs ds -> PoccTrm (TFix ds m)
| PoCnstr: forall m1 m2, PoccTrm (TConstruct (mkInd nm m1) m2)
with PoccTrms : Terms -> Prop :=
| PoThd: forall t ts, PoccTrm t -> PoccTrms (tcons t ts)
| PoTtl: forall t ts, PoccTrms ts -> PoccTrms (tcons t ts)
with PoccDefs : Defs -> Prop :=
| PoDhd_ty: forall dn dty db dra ds,
           PoccTrm dty -> PoccDefs (dcons dn dty db dra ds)
| PoDhd_bod: forall dn dty db dra ds,
           PoccTrm db -> PoccDefs (dcons dn dty db dra ds)
| PoDtl: forall dn dty db dra ds,
           PoccDefs ds -> PoccDefs (dcons dn dty db dra ds).
Hint Constructors PoccTrm PoccTrms PoccDefs.
Scheme poTrm_ind' := Minimality for PoccTrm Sort Prop
  with poTrms_ind' := Minimality for PoccTrms Sort Prop
  with poDefs_ind' := Minimality for PoccDefs Sort Prop.
Combined Scheme poTrmTrmsDefs_ind from poTrm_ind', poTrms_ind', poDefs_ind'.

Lemma Pocc_TConst: forall s2, PoccTrm (TConst s2) -> nm = s2.
intros s2 h. inversion h. reflexivity.
Qed.

Lemma notPocc_TConst: forall s2, ~ PoccTrm (TConst s2) -> nm <> s2.
intros s2 h j. elim h. rewrite <- j. auto. 
Qed.

Lemma Pocc_TCnstr:
  forall s2 m1 m2, PoccTrm (TConstruct (mkInd s2 m1) m2) -> nm = s2.
intros s2 m1 m2 h. inversion h. reflexivity.
Qed.

Lemma notPocc_TCnstr:
  forall s2 m1 m2, ~ PoccTrm (TConstruct (mkInd s2 m1) m2) -> nm <> s2.
intros s2 m1 m2 h j. elim h. rewrite <- j. auto. 
Qed.

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

Lemma inverse_Pocc_TConstL: forall s2, ~ PoccTrm (TConst s2) -> nm <> s2.
intros s2 h j. elim h. rewrite <- j. auto.
Qed.

Lemma notPocc_TApp:
  forall t arg args, ~ PoccTrm (TApp t arg args) ->
     ~ PoccTrm t /\ ~ PoccTrm arg /\ ~ PoccTrms args.
intuition.
Qed.

Lemma notPocc_mkApp:
  forall t args, ~ PoccTrm (mkApp t args) ->
     ~ PoccTrm t /\ ~ PoccTrms args.
Proof.
  induction t; induction args; simpl; intros h; split; intuition; 
  try (solve [inversion H]);
  try (solve [inversion_Clear H; apply h;
               [apply PoAppA; assumption |
                apply PoAppR; assumption]]).
  - inversion_Clear H; apply h.
    + apply PoAppL. assumption.
    + apply PoAppA. assumption.
    + apply PoAppR. apply PoccTrms_tappendl. assumption.
  - inversion_Clear H; apply h.
    + apply PoAppL. assumption.
    + apply PoAppA. assumption.
    + apply PoAppR. apply PoccTrms_tappendl. assumption.
  - inversion_Clear H; apply h.
    + apply PoAppR. apply PoccTrms_tappendr. apply PoThd. assumption.
    + apply PoAppR. apply PoccTrms_tappendr. apply PoTtl. assumption.
Qed.

Lemma Pocc_TApp:
  forall t arg args, PoccTrm (TApp t arg args) ->
     PoccTrm t \/ PoccTrm arg \/ PoccTrms args.
inversion 1; intuition.
Qed.

Lemma notPocc_TProd:
  forall n ty bod, ~ PoccTrm (TProd n ty bod) ->
                   ~ PoccTrm bod /\ ~ PoccTrm ty.
intuition. 
Qed.

Lemma notPocc_TLambda:
  forall n ty bod, ~ PoccTrm (TLambda n ty bod) ->
                   ~ PoccTrm bod /\ ~ PoccTrm ty.
intuition. 
Qed.

Lemma notPocc_TLetIn:
  forall n dfn ty bod, ~ PoccTrm (TLetIn n dfn ty bod) ->
                   ~ PoccTrm dfn /\ ~ PoccTrm bod /\ ~ PoccTrm ty.
intuition. 
Qed.

Lemma notPocc_TCase:
  forall n ty mch brs, ~ PoccTrm (TCase n ty mch brs) ->
                   ~ PoccTrm ty /\ ~ PoccTrm mch /\ ~ PoccTrms brs.
intuition. 
Qed.

Lemma notPocc_TFix:
  forall ds m, ~ PoccTrm (TFix ds m) -> ~ PoccDefs ds.
intuition. 
Qed.

Lemma notPoccTrms:
  forall t ts, ~ PoccTrms (tcons t ts) -> ~ PoccTrm t /\ ~ PoccTrms ts.
intuition. 
Qed.

Lemma PoccTrms_tcons:
  forall t ts, PoccTrms (tcons t ts) -> PoccTrm t \/ PoccTrms ts.
inversion 1; intuition. 
Qed.

Lemma notPoccDefs:
  forall nm ty bod rarg ds, ~ PoccDefs (dcons nm ty bod rarg ds) ->
                            ~ PoccTrm ty /\ ~ PoccTrm bod /\ ~ PoccDefs ds.
intuition. 
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


Lemma Pocc_mkApp_inv:
  forall fn args, PoccTrm (mkApp fn args) -> PoccTrm fn \/ PoccTrms args.
Proof.
  intros fn args.
  functional induction (mkApp fn args); simpl; intros h; intuition.
  - inversion_Clear h; intuition. 
    + destruct (PoccTrms_append_invrt _ _ H0). 
      * left. apply PoAppR. assumption.
      * right. assumption.
  - destruct (Pocc_TApp h); intuition.
Qed.

Lemma tIn_Pocc_Poccs:
  forall t ts us, tIn t ts -> PoccTrm t -> PoccTrms (tappend ts us).
induction ts; intros us h1 h2.
- inversion h1.
- inversion h1.
  + subst. simpl. apply PoThd. assumption.
  + simpl.  apply PoTtl. apply IHts; assumption.
Qed.

Lemma Pocc_fn_mkApp_lem:
  forall fn, PoccTrm fn -> forall args, PoccTrm (mkApp fn args).
Proof.
  induction 1.
  - destruct args; simpl.
    + apply PoProdBod. assumption.
    + apply PoAppL. apply PoProdBod. assumption.
  - destruct args; simpl.
    + apply PoProdTy. assumption.
    + apply PoAppL. apply PoProdTy. assumption.
  - destruct args; simpl.
    + apply PoLambdaBod. assumption.
    + apply PoAppL. apply PoLambdaBod. assumption.
  - destruct args; simpl.
    + apply PoLambdaTy. assumption.
    + apply PoAppL. apply PoLambdaTy. assumption.
  - destruct args; simpl.
    + apply PoCastTm. assumption.
    + apply PoAppL. apply PoCastTm. assumption.
  - destruct args; simpl.
    + apply PoCastTy. assumption.
    + apply PoAppL. apply PoCastTy. assumption.
  - destruct args; simpl.
    + apply PoLetInDfn. assumption.
    + apply PoAppL. apply PoLetInDfn. assumption.
  - destruct args; simpl.
    + apply PoLetInBod. assumption.
    + apply PoAppL. apply PoLetInBod. assumption.
  - destruct args; simpl.
    + apply PoLetInTy. assumption.
    + apply PoAppL. apply PoLetInTy. assumption.
  - simpl. intros brgs. apply PoAppL. assumption.
  - simpl. intros brgs. apply PoAppA. assumption.
  - simpl. intros brgs. apply PoAppR. apply PoccTrms_tappendl. assumption.
  - destruct args; simpl.
    + apply PoConst.
    + apply PoAppL. apply PoConst.
  - destruct args; simpl.
    + apply PoCaseL. assumption.
    + apply PoAppL. apply PoCaseL. assumption.
  - destruct args; simpl.
    + apply PoCaseR. assumption.
    + apply PoAppL. apply PoCaseR. assumption.
  - destruct args; simpl.
    + apply PoCaseTy. assumption.
    + apply PoAppL. apply PoCaseTy. assumption.
  - destruct args; simpl.
    + apply PoFix. assumption.
    + apply PoAppL. apply PoFix. assumption.
  - destruct args; simpl.
    + apply PoCnstr; assumption.
    + apply PoAppL. apply PoCnstr.
Qed.

Lemma Pocc_TApp_mkApp:
  forall fn arg args, PoccTrm (TApp fn arg args) ->
    PoccTrm (mkApp fn (tcons arg args)).
Proof.
  inversion_clear 1.
  - apply Pocc_fn_mkApp_lem. assumption.
  - destruct (mkApp_isApp_lem fn arg args)
      as [x0 [x1 [x2 [h1 h2]]]].
    rewrite h1. destruct h2.
    + destruct H as [j1 [j2 [j3 j4]]]. subst. simpl.
      apply PoAppA. assumption.
    + destruct H as [j1 [j2 j3]]. apply PoAppR.
      eapply tIn_Pocc_Poccs; eassumption.
  - destruct (mkApp_isApp_lem fn arg args)
      as [x0 [x1 [x2 [h1 h2]]]].
    rewrite h1. destruct h2.
    + destruct H as [j1 [j2 [j3 j4]]]. subst. simpl.
      apply PoAppR. assumption.
    + destruct H. apply PoAppR. apply PoccTrms_tappendr. assumption.
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
| ISort: forall n srt, Instantiate n (TSort srt) (TSort srt)
| ICast: forall n t ck ty it ity,
           Instantiate n t it -> Instantiate n ty ity ->
           Instantiate n (TCast t ck ty) (TCast it ck ity)
| IProd: forall n nm ty bod ibod ity,
             Instantiate (S n) bod ibod -> Instantiate n ty ity ->
             Instantiate n (TProd nm ty bod) (TProd nm ity ibod)
| ILambda: forall n nm ty bod ibod ity,
             Instantiate (S n) bod ibod -> Instantiate n ty ity ->
             Instantiate n (TLambda nm ty bod) (TLambda nm ity ibod)
| ILetIn: forall n nm dfn ty bod idfn ibod ity,
               Instantiate n dfn idfn -> Instantiate (S n) bod ibod ->
               Instantiate n ty ity -> 
               Instantiate n (TLetIn nm dfn ty bod) (TLetIn nm idfn ity ibod)
| IApp: forall n t a ts it ia its,
          Instantiate n t it -> Instantiate n a ia -> Instantiates n ts its ->
          Instantiate n (TApp t a ts) (mkApp it (tcons ia its))
| IConst: forall n s, Instantiate n (TConst s) (TConst s)
| IInd: forall n ind, Instantiate n (TInd ind) (TInd ind)
| IConstruct: forall n ind m1,
                Instantiate n (TConstruct ind m1) (TConstruct ind m1)
| ICase: forall n np ty s ts is its ity,
           Instantiate n s is -> Instantiate n ty ity ->
           Instantiates n ts its ->
           Instantiate n (TCase np ty s ts) (TCase np ity is its)
| IFix: forall n d m id, 
          InstantiateDefs (n + dlength d) d id ->
          Instantiate n (TFix d m) (TFix id m)
with Instantiates: nat -> Terms -> Terms -> Prop :=
| Inil: forall n, Instantiates n tnil tnil
| Icons: forall n t ts it its,
           Instantiate n t it -> Instantiates n ts its ->
           Instantiates n (tcons t ts) (tcons it its)
with InstantiateDefs: nat -> Defs -> Defs -> Prop :=
| Idnil: forall n, InstantiateDefs n dnil dnil
| Idcons: forall n nm ty bod rarg ds ity ibod ids,
            Instantiate n ty ity -> Instantiate n bod ibod ->
            InstantiateDefs n ds ids ->
            InstantiateDefs n (dcons nm ty bod rarg ds)
                            (dcons nm ity ibod rarg ids).
Hint Constructors Instantiate Instantiates InstantiateDefs.
Scheme Instantiate_ind' := Induction for Instantiate Sort Prop
  with Instantiates_ind' := Induction for Instantiates Sort Prop
  with InstantiateDefs_ind' := Induction for InstantiateDefs Sort Prop.
Combined Scheme InstInstsDefs_ind from 
         Instantiate_ind', Instantiates_ind', InstantiateDefs_ind'.

Lemma InstantiateDefs_pres_dlength:
  forall n ds ids, InstantiateDefs n ds ids -> dlength ds = dlength ids.
Proof.
  induction 1.
  + reflexivity.
  + simpl. intuition.
Qed.

Lemma Instantiates_no_gen:
  (~ PoccTrm tin) ->
  (forall n t s, Instantiate n t s -> PoccTrm s -> PoccTrm t) /\
  (forall n ts ss, Instantiates n ts ss -> PoccTrms ss -> PoccTrms ts) /\
  (forall n ds es, InstantiateDefs n ds es -> PoccDefs es -> PoccDefs ds).
intro h. apply InstInstsDefs_ind; intros; auto.
- contradiction.
- inversion H.
- inversion_Clear H1.
  + constructor. intuition.
  + apply PoCastTy. intuition.
- inversion_Clear H1.
  + constructor. intuition.
  + apply PoProdTy. intuition.
- inversion_Clear H1.
  + constructor. apply H. assumption.
  + apply PoLambdaTy. apply H0. assumption.
- inversion_Clear H2.
  + constructor. apply H. assumption.
  + apply PoLetInBod. apply H0. assumption.
  + apply PoLetInTy. apply H1. assumption.
- destruct (Pocc_mkApp_inv _ _ H2) as [hit | hiats]; intuition.
  inversion hiats; intuition.
- inversion_Clear H2.
  + constructor. apply H. assumption.
  + apply PoCaseR. apply H1. assumption.
  + apply PoCaseTy. apply H0. assumption.
- inversion_Clear H0.
  + constructor. apply H. assumption.
- inversion_Clear H1.
  + constructor. apply H. assumption.
  + apply PoTtl. apply H0. assumption.
- inversion_Clear H2.
  + constructor. intuition. 
  + apply PoDhd_bod. intuition. 
  + apply PoDtl. intuition. 
Qed.

Function instantiate (n:nat) (tbod:Term) {struct tbod} : Term :=
  match tbod with
    | TRel m => match nat_compare n m with
                  | Eq => tin
                  | Gt => TRel m
                  | Lt => TRel (pred m)
                end
    | TApp t a ts =>
      mkApp (instantiate n t) (tcons (instantiate n a) (instantiates n ts))
    | TLambda nm ty bod =>
      TLambda nm (instantiate n ty) (instantiate (S n) bod)
    | TProd nm ty bod => TProd nm (instantiate n ty) (instantiate (S n) bod)
    | TCase np ty s ts =>
      TCase np (instantiate n ty) (instantiate n s) (instantiates n ts)
    | TLetIn nm tdef ty bod =>
      TLetIn nm (instantiate n tdef) (instantiate n ty) (instantiate (S n) bod)
    | TFix ds m => TFix (instantiateDefs (n + dlength ds) ds) m
    | TCast t ck ty => TCast (instantiate n t) ck (instantiate n ty)
    | x => x
  end
with instantiates (n:nat) (args:Terms) {struct args} : Terms :=
       match args with
         | tnil => tnil
         | tcons t ts => tcons (instantiate n t) (instantiates n ts)
       end
with instantiateDefs (n:nat) (ds:Defs) {struct ds} : Defs :=
       match ds with
         | dnil => dnil
         | dcons nm ty bod rarg ds =>
           dcons nm (instantiate n ty)
                 (instantiate n bod) rarg (instantiateDefs n ds)
       end.
Functional Scheme instantiate_ind' := Induction for instantiate Sort Prop
with instantiates_ind' := Induction for instantiates Sort Prop
with instantiateDefs_ind' := Induction for instantiateDefs Sort Prop.

Lemma instantiateDefs_pres_dlength:
  forall n ds, dlength ds = dlength (instantiateDefs n ds).
Proof.
  induction ds.
  + reflexivity.
  + simpl. intuition.
Qed.

Lemma Instantiate_instantiate:
  (forall n t it, Instantiate n t it -> instantiate n t = it) /\
  (forall n ts its, Instantiates n ts its -> instantiates n ts = its) /\
  (forall n ds ids, InstantiateDefs n ds ids -> instantiateDefs n ds = ids).
apply InstInstsDefs_ind; intros; simpl; intuition; try (subst; reflexivity).
- rewrite nat_compare_EQ. reflexivity.
- rewrite (proj1 (nat_compare_gt n m) g). reflexivity.
- rewrite (proj1 (nat_compare_lt n m) l). reflexivity.
Qed.

Lemma instantiate_Instantiate:
  (forall t n, Instantiate n t (instantiate n t)) /\
  (forall ts n, Instantiates n ts (instantiates n ts)) /\
  (forall (ds:Defs) n, InstantiateDefs n ds (instantiateDefs n ds)).
Proof.
  apply TrmTrmsDefs_ind; intros; simpl; try (solve [constructor]);
  try (solve[constructor; intuition]).  
- destruct (lt_eq_lt_dec n0 n) as [[h | h] | h].
  + rewrite (proj1 (nat_compare_lt _ _) h). apply IRelLt. assumption.
  + rewrite (proj2 (nat_compare_eq_iff _ _) h). subst. apply IRelEq.
  + rewrite (proj1 (nat_compare_gt _ _)). apply IRelGt.
    assumption. assumption.
Qed.

Lemma instant_pres_PoccTrm:
  (forall tbod, PoccTrm tbod -> forall n, PoccTrm (instantiate n tbod)) /\
  (forall ts, PoccTrms ts -> forall n, PoccTrms (instantiates n ts)) /\
  (forall (Ds:Defs), PoccDefs Ds -> forall n, PoccDefs (instantiateDefs n Ds)).
apply poTrmTrmsDefs_ind; intros; simpl; try solve [constructor; trivial].
- eapply Pocc_TApp_mkApp. apply PoAppL. auto.
- eapply Pocc_TApp_mkApp. apply PoAppA. auto. 
- eapply Pocc_TApp_mkApp. apply PoAppR. auto. 
Qed.

Lemma instantiate_is_Const:
  forall n tbod,
    instantiate n tbod = TConst nm -> 
    (tbod = TRel n /\ tin = TConst nm) \/ (tbod = TConst nm).
induction tbod; intros h; simpl; intuition; try discriminate.
- unfold instantiate in h.
  case_eq (nat_compare n n0); intros; rewrite H in h.
  + left. split. rewrite (nat_compare_eq _ _ H). reflexivity.
    * destruct tin; simpl in h; try discriminate. assumption.
  + discriminate.
  + discriminate.
- simpl in h.
  assert (j:= mkApp_isApp (instantiate n tbod1)
                          (instantiate n tbod2) (instantiates n t)).
  destruct j as [x0 [x1 [x2 k]]]. rewrite k in h. discriminate.
Qed.

End Instantiate_sec.
End PoccTrm_sec.


Lemma instantiate_pres_WFapp:
  (forall bod, WFapp bod ->
              forall t, WFapp t -> forall n, WFapp (instantiate t n bod)) /\
  (forall ts, WFapps ts ->
              forall t, WFapp t -> forall n, WFapps (instantiates t n ts)) /\
  (forall ds, WFappDs ds ->
              forall t, WFapp t -> forall n, WFappDs (instantiateDefs t n ds)).
Proof.
  apply WFappTrmsDefs_ind; intros;
  try (solve [unfold instantiate; constructor]).
  - destruct (lt_eq_lt_dec n m) as [[h|h]|h]; unfold instantiate.
    + rewrite (proj1 (nat_compare_lt _ _) h). constructor.
    + rewrite (proj2 (nat_compare_eq_iff _ _) h). assumption.
    + rewrite (proj1 (nat_compare_gt _ _) h). constructor.
  - change (WFapp (TCast (instantiate t n tm) ck (instantiate t n ty))).
    constructor.
    + apply H0. assumption.
    + apply H2. assumption.
  - change (WFapp (TProd nm (instantiate t n ty) (instantiate t (S n) bod))).
    constructor.
    + apply H0. assumption.
    + apply H2. assumption.
  - change (WFapp (TLambda nm (instantiate t n ty) (instantiate t (S n) bod))).
    constructor.
    + apply H0. assumption.
    + apply H2. assumption.
  - change (WFapp (TLetIn nm (instantiate t n dfn)
                          (instantiate t n ty) (instantiate t (S n) bod))).
    constructor.
    + apply H0. assumption.
    + apply H2. assumption.
    + apply H4. assumption.
  - change (WFapp (mkApp (instantiate t0 n fn) 
                         (tcons (instantiate t0 n t) (instantiates t0 n ts)))).
    apply mkApp_pres_WFapp.
    + constructor. apply H3; assumption. apply H5. assumption.
    + apply H1. assumption.
  - change (WFapp (TCase m (instantiate t n ty) (instantiate t n mch)
                         (instantiates t n brs))).
    constructor.
    + apply H0; assumption.
    + apply H2; assumption.
    + apply H4; assumption.
   - change (WFapp (TFix (instantiateDefs t (n + dlength defs) defs) m)).
     constructor.
     + apply H0. assumption.
   - change (WFapps (tcons (instantiate t0 n t) (instantiates t0 n ts))).
     constructor.
     + apply H0. assumption.
     + apply H2. assumption.
   - change (WFappDs (dcons nm (instantiate t n ty)
                            (instantiate t n bod) arg
                            (instantiateDefs t n ds))).
     constructor.
     + apply H0. assumption.
     + apply H2. assumption.
     + apply H4. assumption.
Qed.


(** operations for weak reduction and weak evaluation **)
Definition whBetaStep (bod arg:Term) (args:Terms) : Term :=
  mkApp (instantiate arg 0 bod) args.

Lemma whBetaStep_pres_WFapp:
  forall bod, WFapp bod -> forall arg, WFapp arg -> forall args, WFapps args ->
    WFapp (whBetaStep bod arg args).
Proof.
  intros bod hbod arg harg args hargs. unfold whBetaStep.
  apply mkApp_pres_WFapp. assumption.
  apply instantiate_pres_WFapp; assumption.
Qed.

Lemma whBetaStep_absorbs_mkApp:
  forall bod arg args brgs, 
    (mkApp (whBetaStep bod arg args) brgs) =
    whBetaStep bod arg (tappend args brgs).
Proof.
  intros. unfold whBetaStep. apply mkApp_idempotent.
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

Function whCaseStep (cstrNbr:nat) (ts brs:Terms) : option Term :=
  match tnth cstrNbr brs with
    | Some t => Some (mkApp t ts)
    | None => None
  end.

Lemma whCaseStep_pres_WFapp:
  forall (brs:Terms), WFapps brs -> forall ts, WFapps ts -> 
  forall (n:nat) (s:Term), whCaseStep n ts brs = Some s -> WFapp s.
Proof.
  intros brs hbrs ts hts n s h. unfold whCaseStep in h.
  assert (j:= tnth_pres_WFapp hbrs n). destruct (tnth n brs).
  - injection h; intros. rewrite <- H. apply mkApp_pres_WFapp. 
    + assumption.
    + apply j. reflexivity.
  - discriminate.
Qed.


(** Unfolding a Fixpoint **)
(** "dts" is a list of the mutual fixpoint definitions
*** "m" tells which of the definitions is being called
**)
Definition pre_whFixStep body dts args : Term :=
  let f := fold_left
             (fun bod ndx => instantiate (TFix dts ndx) 0 bod)
             (list_to_zero (dlength dts)) body in
  (mkApp f args).
Functional Scheme pre_whFixStep_ind := Induction for pre_whFixStep Sort Prop.

Definition whFixStep (dts:Defs) (xix:Term * nat) (args:Terms) :  option Term :=
  let (x,ix) := xix in
  match tnth ix args with
              (** Check that the recursive argument is canonical **)
    | Some (TConstruct _ _) => Some (pre_whFixStep x dts args)
    | Some (TApp (TConstruct _ _) _ _) => Some (pre_whFixStep x dts args)
    | _ => None
  end.
Functional Scheme whFixStep_ind := Induction for whFixStep Sort Prop.

Lemma pre_whFixStep_absorbs_mkApp:
  forall bod dts args brgs,
    mkApp (pre_whFixStep bod dts args) brgs =
    pre_whFixStep bod dts (tappend args brgs).
Proof.
  intros. unfold pre_whFixStep. rewrite mkApp_idempotent. reflexivity.
Qed.

 
(***
Lemma whFixStep_extends:
  forall dts m args t,
    whFixStep dts m args = Some t ->
    forall brgs, exists s, whFixStep dts m (tappend args brgs) = Some s.
Proof.
  intros dts m args t hargs brgs.
  unfold whFixStep.
  unfold whFixStep in hargs.
  destruct (dnthBody m dts); try discriminate.
  destruct p. destruct (tnth n args); try discriminate.
  destruct t1; try discriminate.
  destruct t1_1; try discriminate.
  unfold pre_whFixStep.
  unfold pre_whFixStep in hargs.
  destruct (tnth n (tappend args brgs)).
  destruct t2.

  unfold pre_whFixStep in hargs.

  
Lemma whFixStep_absorbs_mkApp:
  forall dts m args brgs t,
    whFixStep dts m args = Some t ->
  (mkApp t brgs) = (whFixStep dts m (tappend args brgs)).
Proof.
  unfold whFixStep. intros.
  rewrite (pre_whFixStep_absorbs_mkApp). reflexivity.
Qed.
***)

(***
Lemma whFixStep_dnthBody:
  forall (dts:Defs) (m:nat) (args:Terms) (t:Term),
    whFixStep dts m args = Some t ->
    exists (tn:Term * nat), dnthBody m dts = Some tn.
Proof.
  intros dts m args t. unfold whFixStep, pre_whFixStep.
  destruct (dnthBody m dts); try discriminate.
  destruct p, (tnth n args); intros; try discriminate.
  destruct t1; try discriminate.
  exists (t0, n). reflexivity.
  Qed.
 ***)

(***
Lemma whFixStep_mkApp:
  forall (dts:Defs) (x:Term) (ix:nat) (args:Terms) (t:Term),
    whFixStep dts (x, ix) args = Some t ->
    exists f, t = mkApp f args.
Proof.
  intros dts x ix args t h.
    destruct (whFixStep_dnthBody _ _ _ h) as [[s d] j].
  unfold whFixStep, pre_whFixStep in h.
  destruct (dnthBody m dts); try discriminate.
  destruct p, (tnth n args); try discriminate.
  destruct t1; try discriminate.
  destruct t1_1; try discriminate.
  exists (fold_left
              (fun (bod : Term) (ndx : nat) =>
               instantiate (TFix dts ndx) 0 bod) (list_to_zero (dlength dts))
              t0).
  myInjection h. reflexivity.
Qed.
 **)

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
  forall  (bod:Term) (dts:Defs) (args:Terms),
    WFapp bod -> WFappDs dts -> WFapps args ->
        WFapp (pre_whFixStep bod dts args).
Proof.
  intros bod dts args hbod hdts hargs.
  unfold pre_whFixStep.
  apply mkApp_pres_WFapp. assumption.
  apply fold_left_pres_WFapp; try assumption.
  intros. apply instantiate_pres_WFapp.
  assumption. constructor. assumption.
Qed.
  
Lemma whFixStep_pres_WFapp:
  forall (dts:Defs)  (x:Term) (ix:nat) (args:Terms) (t:Term),
    WFappDs dts -> WFapp x -> WFapps args ->
    whFixStep dts (x, ix) args = Some t ->
    WFapp t.
Proof.
  intros dts x ix args t hdts hx hargs hwhFs.
  unfold whFixStep, pre_whFixStep in hwhFs.
  destruct (tnth ix); try discriminate.
  destruct t0; try discriminate.
  - destruct t0_1; try discriminate. myInjection hwhFs.
    apply mkApp_pres_WFapp; try assumption.
    apply fold_left_pres_WFapp.
    + intros u hu m. apply instantiate_pres_WFapp.
      assumption. constructor. assumption.
    + assumption.
  - myInjection hwhFs.
    apply mkApp_pres_WFapp; try assumption.
    apply fold_left_pres_WFapp.
    + intros u hu m. apply instantiate_pres_WFapp.
      assumption. constructor. assumption.
    + assumption.
Qed.