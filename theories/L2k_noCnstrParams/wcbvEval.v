Require Import FunInd.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Program.Basics.
Require Import Coq.omega.Omega.
Require Import Coq.Logic.Decidable.
Require Import Common.Common.
Require Import L2k.compile.
Require Import L2k.term.
Require Import L2k.program.
        
Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

Notation ret := (ExtLib.Structures.Monad.ret).
Notation bind := (ExtLib.Structures.Monad.bind).
Notation raise := (ExtLib.Structures.MonadExc.raise).

(** Relational version of weak cbv evaluation  **)
Inductive WcbvEval (p:environ Term) : Term -> Term -> Prop :=
| wLam: forall nm bod, WcbvEval p (TLambda nm bod) (TLambda nm bod)
| wProof: WcbvEval p TProof TProof
| wAppProof : forall fn arg arg',
    WcbvEval p fn TProof ->
    WcbvEval p arg arg' ->
    WcbvEval p (TApp fn arg) TProof
| wConstruct: forall i r args args',
    WcbvEvals p args args' ->
    WcbvEval p (TConstruct i r args) (TConstruct i r args')
| wFix: forall dts m, WcbvEval p (TFix dts m) (TFix dts m)
| wConst: forall nm (t s:Term),
    lookupDfn nm p = Ret t ->
    WcbvEval p t s ->
    WcbvEval p (TConst nm) s
| wAppLam: forall (fn bod a1 a1' s:Term) (nm:name),
    WcbvEval p fn (TLambda nm bod) ->
    WcbvEval p a1 a1' ->
    WcbvEval p (whBetaStep bod a1') s ->
    WcbvEval p (TApp fn a1) s
| wLetIn: forall (nm:name) (dfn bod dfn' s:Term),
    WcbvEval p dfn dfn' ->
    WcbvEval p (instantiate dfn' 0 bod) s ->
    WcbvEval p (TLetIn nm dfn bod) s
| wAppFix: forall dts m (fn a1 x s:Term),
    WcbvEval p fn (TFix dts m) ->
    whFixStep dts m = Some x ->
    WcbvEval p (TApp x a1) s ->
    WcbvEval p (TApp fn a1) s
| wAppCong: forall fn fn' arg arg', 
    WcbvEval p fn fn' ->
    (* Lambda, Fix and Proof are redexes; Constructors are fully applied *)
    (~ isLambda fn' /\ ~ isFix fn' /\ ~ isConstruct fn' /\ fn' <> TProof) ->
    WcbvEval p arg arg' ->
    WcbvEval p (TApp fn arg) (TApp fn' arg') 
| wCase: forall mch i n args brs cs s,
    WcbvEval p mch (TConstruct i n args) ->
    whCaseStep n args brs = Some cs ->
    WcbvEval p cs s ->
    WcbvEval p (TCase i mch brs) s
| wProj: forall bod r args arg x ind res,
    WcbvEval p bod (TConstruct ind r args) ->
    tnth arg args = Some x ->
    WcbvEval p x res ->
    WcbvEval p (TProj (ind, arg) bod) res
with WcbvEvals (p:environ Term) : Terms -> Terms -> Prop :=
     | wNil: WcbvEvals p tnil tnil
     | wCons: forall t t' ts ts',
         WcbvEval p t t' -> WcbvEvals p ts ts' -> 
         WcbvEvals p (tcons t ts) (tcons t' ts').
Hint Constructors WcbvEval WcbvEvals : core.
Scheme WcbvEval1_ind := Induction for WcbvEval Sort Prop
     with WcbvEvals1_ind := Induction for WcbvEvals Sort Prop.
Combined Scheme WcbvEvalEvals_ind from WcbvEval1_ind, WcbvEvals1_ind.

(** when reduction stops **)
Definition no_Wcbv_step (p:environ Term) (t:Term) : Prop :=
  no_step (WcbvEval p) t.
Definition no_Wcbvs_step (p:environ Term) (ts:Terms) : Prop :=
  no_step (WcbvEvals p) ts.

(** evaluate omega = (\x.xx)(\x.xx): nontermination **)
Definition xx := (TLambda nAnon (TApp (TRel 0) (TRel 0))).
Definition xxxx := (TApp xx xx).
Goal WcbvEval nil xxxx xxxx.
unfold xxxx, xx.
change (WcbvEval nil xxxx xxxx).
Abort.
             
Lemma pre_WcbvEval_single_valued:
  forall p,
  (forall t s, WcbvEval p t s -> forall u, WcbvEval p t u -> s = u) /\
  (forall t s, WcbvEvals p t s -> forall u, WcbvEvals p t u -> s = u).
Proof.
  intros p.
  apply WcbvEvalEvals_ind; intros; try (inversion_Clear H; reflexivity).
  - inversion_Clear H1; trivial.
    + specialize (H _ H4). discriminate.
    + specialize (H _ H4). discriminate.
    + destruct H5 as [a [b [c d]]]. elim d. symmetry. apply H. assumption.
  - inversion_Clear H0. apply f_equal3; try reflexivity.
    eapply H. assumption.
  - inversion_Clear H0. rewrite H2 in e. myInjection e.
    eapply H. assumption.
  - inversion_Clear H2.
    + specialize (H _ H5). discriminate.
    + specialize (H _ H5). myInjection H.
      specialize (H0 _ H6). subst.
      eapply H1. assumption.
    + specialize (H _ H5). discriminate.
    + destruct H6 as [a [b c]]. specialize (H _ H5). subst fn'.
      elim a. auto.
  - inversion_Clear H1. specialize (H _ H6). subst.
    eapply H0. assumption.
  - inversion_Clear H1.
    + specialize (H _ H4). discriminate.
    + specialize (H _ H4). discriminate.
    + specialize (H _ H4). myInjection H. rewrite H5 in e. myInjection e.
      specialize (H0 _ H7). subst. intuition.
    + destruct H5 as [a [b c]]. specialize (H _ H4). subst fn'.
      destruct b. auto.
  - destruct a as [a [b [c d]]]. inversion_Clear H1.
    + specialize (H _ H4). contradiction. 
    + specialize (H _ H4). subst. elim a. auto.
    + specialize (H _ H4). subst. elim b. auto.
    + pose proof (H _ H4). pose proof (H0 _ H7). subst. reflexivity.
  - inversion_Clear H1.
    + specialize (H _ H5). myInjection H. rewrite e in H7. myInjection H7.
      apply H0. assumption.
  - inversion_Clear H1. specialize (H _ H5). myInjection H.
    rewrite e in H7. myInjection H7. intuition.
  - inversion_Clear H1. specialize (H _ H4). specialize (H0 _ H6). subst.
    reflexivity.
Qed.

Lemma WcbvEval_single_valued:
  forall p t s, WcbvEval p t s -> forall u, WcbvEval p t u -> s = u.
Proof.
  intros. eapply (proj1 (pre_WcbvEval_single_valued p)); eassumption.
Qed.

Lemma Construct_not_applied:
  forall p t x, WcbvEval p t x -> forall f a, t = TApp f a ->
                forall i r args, f <> TConstruct i r args.
Proof.
  induction 1; intros; try discriminate.
  - myInjection H1. intros h. subst. inversion H.
  - myInjection H2. intros h. subst. inversion H.
  - myInjection H2. intros h. subst. inversion H.
  - myInjection H2. intros h. subst. destruct H0 as [e [b [c d]]].
    inversion_Clear H. elim c. auto.
Qed.
   
Lemma WcbvEvals_tcons_tcons:
  forall p arg args brgs, WcbvEvals p (tcons arg args) brgs ->
                          exists crg crgs, brgs = (tcons crg crgs).
Proof.
  inversion 1. exists t', ts'. reflexivity.
Qed.

Lemma WcbvEvals_tcons_tcons':
  forall p arg brg args brgs,
    WcbvEvals p (tcons arg args) (tcons brg brgs) ->
    WcbvEval p arg brg /\ WcbvEvals p args brgs.
Proof.
  inversion 1. intuition.
Qed.

Lemma WcbvEvals_pres_tlength:
  forall p args brgs, WcbvEvals p args brgs -> tlength args = tlength brgs.
Proof.
  induction 1. reflexivity. cbn. rewrite IHWcbvEvals. reflexivity.
Qed.

(************** wcbvEval preserves WFapp **
Lemma WcbvEval_pres_WFapp:
  forall p, WFaEnv p -> 
  (forall t s, WcbvEval p t s -> WFapp t -> WFapp s) /\
  (forall ts ss, WcbvEvals p ts ss -> WFapps ts -> WFapps ss).
Proof.
  intros p hp.
  apply WcbvEvalEvals_ind; intros; try assumption;
  try (solve[inversion_Clear H0; intuition]);
  try (solve[inversion_Clear H1; intuition]).
  - apply H. unfold lookupDfn in e. case_eq (lookup nm p); intros xc.
    + intros k. assert (j:= lookup_pres_WFapp hp _ k)
      . rewrite k in e. destruct xc. 
      * myInjection e. inversion j. assumption.
      * discriminate.
    + rewrite xc in e. discriminate.
  - inversion_clear H2. apply H1.
    specialize (H H4). inversion_Clear H.
    apply (whBetaStep_pres_WFapp); intuition. 
  - inversion_Clear H1. apply H0. apply instantiate_pres_WFapp; intuition.
  - inversion_clear H1. specialize (H H3). inversion_Clear H.
    apply H0. apply pre_whFixStep_pres_WFapp; try eassumption; intuition.
    + eapply dnthBody_pres_WFapp; try eassumption.
  - inversion_Clear H1.
    destruct (WcbvEvals_tcons_tcons w0) as [x0 [x1 jx]]. subst.    
    destruct (mkApp_isApp_lem fn' x0 x1) as
        [y0 [y1 [y2 [ka [[kc1 [kc2 [kc3 kc4]]] | [kd1 [kd2 kd3]]]]]]];
      rewrite ka.
    + subst. cbn.
      assert (j: WFapps (tcons arg args)). constructor; assumption.
      specialize (H0 j). inversion_Clear H0.
      constructor; intuition.
    + destruct kd1 as [z0 [z1 [z2 kz]]]. rewrite kz in ka. cbn in ka.
      myInjection ka. specialize (H H6). inversion_Clear H.
      assert (k:= tappend_tcons_tunit _ _ _ _ H1).
      rewrite <- k. constructor; try assumption.
      rewrite <- tappend_assoc. cbn. apply tappend_pres_WFapps; try assumption.
      apply H0. constructor; try assumption.
  - inversion_Clear H1. apply H0. 
    refine (whCaseStep_pres_WFapp _ _ _ _); try eassumption.
    refine (canonicalP_pres_WFapp _ e). intuition.
Qed.
 *************)

Lemma WcbvEval_weaken:
  forall p,
    (forall t s, WcbvEval p t s ->
                 forall nm ec, crctEnv ((nm,ec)::p) ->
                               WcbvEval ((nm,ec)::p) t s) /\
    (forall ts ss, WcbvEvals p ts ss ->
                   forall nm ec, crctEnv ((nm,ec)::p) ->
                                 WcbvEvals ((nm,ec)::p) ts ss).
Proof.
  intros p. apply WcbvEvalEvals_ind; intros; auto.
  - econstructor; intuition.
  - destruct (kername_eq_dec nm nm0).
    + subst. inversion_Clear H0; unfold lookupDfn in e.
      * rewrite (proj1 (fresh_lookup_None (trm:=Term) _ _)) in e.
        discriminate. assumption.
      * rewrite (proj1 (fresh_lookup_None (trm:=Term) _ _)) in e.
        discriminate. assumption.
    + eapply wConst.
      * rewrite <- (lookupDfn_weaken' n). eassumption. 
      * apply H. assumption. 
  - eapply wAppLam.
    + apply H. assumption.
    + apply H0. assumption.
    + apply H1. assumption.
  - eapply wLetIn; intuition.
  - eapply wAppFix; try eassumption; intuition. 
  - eapply wCase; intuition; eassumption.
  - eapply wProj; try eassumption; intuition.
Qed.

Lemma LookupDfn_pres_Crct:
  forall p, crctEnv p -> forall nm u, LookupDfn nm p u ->
                                      forall m, crctTerm p m u.
Proof.
  induction p; intros; unfold LookupDfn in *.
  - inversion H0.
  - inversion_Clear H0. inversion_Clear H.
    + apply (proj1 Crct_weaken); try assumption. apply Crct_Up. assumption.
    + inversion_Clear H. apply (proj1 Crct_weaken); try assumption.
      * eapply IHp.
        -- eapply (proj1 Crct_CrctEnv p). eassumption.
        -- eassumption.
      * apply (proj1 Crct_weaken_Typ); try assumption.
        eapply IHp; try eassumption.
Qed.
  

Lemma WcbvEval_pres_Crct:
  forall p,
    (forall t s, WcbvEval p t s ->
                 forall m, crctTerm p m t -> crctTerm p m s) /\
    (forall ts ss, WcbvEvals p ts ss ->
                   forall m, crctTerms p m ts -> crctTerms p m ss).
Proof.
  intros p.
  apply WcbvEvalEvals_ind; cbn; intros;
    try (inversion_Clear H; intuition);
    try (inversion_Clear H0; intuition);
    try (inversion_Clear H1; intuition).
  - inversion_Clear H5. inversion_Clear H0.
    econstructor; try eassumption; intuition.
    econstructor; try eassumption.
    + econstructor; try eassumption.
    + rewrite <- (WcbvEvals_pres_tlength w). assumption.
  - unfold LookupDfn, lookupDfn in *.
    rewrite (Lookup_lookup H5) in e. myInjection e. 
    eapply H. eapply LookupDfn_pres_Crct; try eassumption.
  - inversion_Clear H2. specialize (H _ H7). specialize (H0 _ H8).
    eapply H1. eapply whBetaStep_pres_Crct; try eassumption.
    inversion_clear H. assumption.
  - eapply H0. apply instantiate_pres_Crct; try eassumption; try omega.
    apply H. assumption.
  - specialize (H _ H6). inversion_Clear H.
    inversion_Clear w0; (eapply H0; constructor; try assumption;
      apply (whFixStep_pres_Crct _ H5 _ e)).
  - specialize (H _ H8). apply H0.
    refine (whCaseStep_pres_Crct _ H9 _ _); try eassumption.
    inversion_Clear H. assumption.
  - apply H0. eapply tnth_pres_Crct; try eassumption.
    specialize (H _ H5). inversion_Clear H. assumption.
Qed.

Section wcbvEval_sec.
Variable p:environ Term.

(** now an executable weak-call-by-value evaluation **)
(** use a timer to make this terminate **)
Function wcbvEval
         (tmr:nat) (t:Term) {struct tmr}: exception Term :=
  match tmr with 
  | 0 => raise ("out of time: " ++ print_term t)
  | S n =>
    match t with      (** look for a redex **)
    | TConst nm =>
      match (lookup nm p) with
      | Some (ecTrm t) => wcbvEval n t
      (** note hack coding of axioms in environment **)
      | Some (ecTyp _ _) => raise ("wcbvEval;TConst;ecTyp: " ++ string_of_kername nm)
      | _ => raise "wcbvEval: TConst environment miss"
      end
    | TApp fn a1 =>
      match wcbvEval n fn with
      | Exc str =>  raise ("(wcbvEval;TApp:fn" ++ str ++ ")")
      | Ret TProof =>          (* Proof redex *)
        match wcbvEval n a1 with
        | Exc s =>  raise ("wcbvEval,ProofRedex,arg: " ++ s)
        | Ret _ => Ret TProof 
        end
      | Ret (TFix dts m) =>           (* Fix redex *)
        match whFixStep dts m with
        | None => raise ("wcbvEval;TApp:whFixStep doesn't eval")
        | Some f => wcbvEval n (TApp f a1)
        end
      | Ret (TLambda _ bod) =>        (* beta redex *)
        match wcbvEval n a1 with
        | Exc s =>  raise ("wcbvEval,beta,arg: " ++ s)
        | Ret b1 => wcbvEval n (whBetaStep bod b1)
        end
      | Ret (TConstruct i cn args) =>  (* constructors are fully applied *)
        raise ("wcbvEval,Cong,Constructor: "
                 ++ " " ++ (print_inductive i) ++ " " ++ (nat_to_string cn))
      | Ret (_ as u) =>
        match wcbvEval n a1 with
        | Exc s =>  raise ("wcbvEval,Cong,arg: " ++ s)
        | Ret b1 => ret (TApp u b1)  (* congruence *)
        end
      end
    | TCase i mch brs =>
      match wcbvEval n mch with
      | Exc str => raise ("wcbvEval,TCase,mch: " ++  str)
      | Ret (TConstruct j r args) =>
        match whCaseStep r args brs with
        | None => raise "wcbvEval:Case,whCaseStep"
        | Some cs => match inductive_dec i j with
                     | left _ => wcbvEval n cs
                     | right _ => raise "wcbvEval:Case,whCaseStep, inductives"
                     end
       end
      | Ret x => raise "wcbvEval:Case,discriminee"
      end
  | TLetIn nm df bod =>
    match wcbvEval n df with
    | Ret df' => wcbvEval n (instantiate df' 0 bod)
    | Exc s => raise ("wcbvEval,TLetIn,def: " ++ s)
    end
  | TConstruct i cn args =>
    match wcbvEvals n args with
    | Ret args' => ret (TConstruct i cn args')
    | Exc s => raise ("wcbvEval:TConstruct:args: " ++ s)
    end
  | TProj (i, arg) bod =>
    match wcbvEval n bod with
    | Exc s => raise ("(wcbvEval:TProj,bod: " ++ s ++ ")")
    | Ret (TConstruct j m args) =>
        match tnth arg args with
        | None => raise ("wcbvEval:TProj,tnth_error")
        | Some x => match inductive_dec i j with
                     | left _ => wcbvEval n x
                     | right _ => raise "wcbvEval:Proj,inductives"
                     end
        end
    | Ret x => raise "wcbvEval:Proj"
    end
  (** already in whnf ***)
  | TProof => ret TProof
  | TLambda nn t => ret (TLambda nn t)
  | TFix mfp br => ret (TFix mfp br)
  (** should never appear **)
  | TRel _ => raise "wcbvEval:unbound Rel"
  | TWrong s => raise (print_term t)
    end
  end%string
with wcbvEvals (tmr:nat) (ts:Terms) {struct tmr}
     : exception Terms :=
       match tmr with 
       | 0 => raise "out of time"
       | S n => match ts with             (** look for a redex **)
                | tnil => ret tnil
                | tcons s ss =>
                  match wcbvEval n s, wcbvEvals n ss with
                  | Ret es, Ret ess => ret (tcons es ess)
                  | Exc s, _ => raise ("wcbvEvals:hd: " ++ s)
                  | Ret _, Exc s => raise ("wcbvEvals:tl: " ++ s)
                  end
                end
       end%string.
Functional Scheme wcbvEval_ind' := Induction for wcbvEval Sort Prop
with wcbvEvals_ind' := Induction for wcbvEvals Sort Prop.
Combined Scheme wcbvEvalEvals_ind from wcbvEval_ind', wcbvEvals_ind'.

(** wcbvEval and WcbvEval are the same relation **)
Lemma wcbvEval_WcbvEval:
  forall tmr,
  (forall t s, wcbvEval tmr t = Ret s -> WcbvEval p t s) /\
  (forall ts ss, wcbvEvals tmr ts = Ret ss -> WcbvEvals p ts ss).
Proof.
  intros tmr.
  apply (wcbvEvalEvals_ind
           (fun tmr t su => forall u (p1:su = Ret u), WcbvEval p t u)
           (fun tmr t su => forall u (p1:su = Ret u), WcbvEvals p t u));
    intros; try discriminate; try (myInjection p1);
    try(solve[constructor]); intuition.
  - eapply wConst; intuition. unfold lookupDfn. rewrite e1. reflexivity.
  - specialize (H _ e1). specialize (H0 _ e2). now eapply wAppProof.
  - specialize (H _ e1). specialize (H0 _ p1).
    eapply wAppFix; eassumption.
  - specialize (H _ e1). specialize (H0 _ e2). specialize (H1 _ p1). 
    eapply wAppLam; eassumption.
  - specialize (H _ e1). specialize (H0 _ e2).
    apply wAppCong; try assumption. repeat split; intros h.
    + dstrctn h. subst. contradiction. 
    + dstrctn h. subst. contradiction. 
    + dstrctn h. subst. contradiction. 
    + subst. contradiction.
  - eapply wCase; subst; try eassumption.
    + now apply H. 
    + intuition.
  - eapply wLetIn; intuition.
  - eapply wProj; try eassumption. subst i.
    + specialize (H _ e1). eassumption.
    + subst. apply H0. assumption.
Qed.

Lemma wcbvEvals_tcons_tcons:
  forall m args brg brgs,
    wcbvEvals m args = Ret (tcons brg brgs) ->
    forall crg crgs, args = (tcons crg crgs) ->
                     wcbvEval (pred m) crg = Ret brg.
Proof.
  intros m args.
  functional induction (wcbvEvals m args); intros; try discriminate.
  myInjection H0. myInjection H. assumption.
Qed.

(** need strengthening to large-enough fuel to make the induction
 *** go through **)
Lemma pre_WcbvEval_wcbvEval:
  (forall t s, WcbvEval p t s ->
               exists n, forall m, m >= n -> wcbvEval (S m) t = Ret s) /\
  (forall ts ss, WcbvEvals p ts ss ->
                 exists n, forall m, m >= n -> wcbvEvals (S m) ts = Ret ss).
Proof.
  assert (j:forall m, m > 0 -> m = S (m - 1)).
  { induction m; intuition. }
  apply WcbvEvalEvals_ind; intros; try (exists 0; intros mx h; reflexivity).
  - destruct H, H0. exists (S (max x x0)). intros mx h.
    assert (l1:= max_fst x x0). assert (l2:= max_snd x x0).
    simpl. rewrite (j mx); try omega. rewrite (H (mx - 1)); try omega.
    rewrite H0; try omega. reflexivity.
  - destruct H. exists (S x). intros m hm. simpl. rewrite (j m); try omega.
    + rewrite (H (m - 1)); try omega. reflexivity.
  - destruct H. exists (S x). intros mm h. cbn.
    unfold lookupDfn in e. destruct (lookup nm p); try discriminate.
    + destruct e0; try discriminate.
      rewrite (j mm); try omega. myInjection e. eapply H. omega.
  - destruct H, H0, H1. exists (S (max x (max x0 x1))). intros m h.
    assert (j1:= max_fst x (max x0 x1)). 
    assert (lx: m > x). omega.
    assert (j2:= max_snd x (max x0 x1)).
    assert (j3:= max_fst x0 x1).
    assert (lx0: m > x0). omega.
    assert (j4:= max_snd x0 x1).
    assert (j5:= max_fst x0 x1).
    assert (lx1: m > x1). omega.
    assert (k:wcbvEval m fn = Ret (TLambda nm bod)).
    + rewrite (j m). apply H.
      assert (l:= max_fst x (max x0 x1)); omega. omega.
    + assert (k0:wcbvEval m a1 = Ret a1').
      * rewrite (j m). apply H0. 
        assert (l:= max_snd x (max x0 x1)). assert (l':= max_fst x0 x1).
        omega. omega.
      * simpl. rewrite (j m); try omega.
        rewrite H; try omega. rewrite H0; try omega. rewrite H1; try omega.
        reflexivity.
  - destruct H, H0. exists (S (max x x0)). intros mx h.
    assert (l1:= max_fst x x0). assert (l2:= max_snd x x0).
    simpl. rewrite (j mx); try omega. rewrite (H (mx - 1)); try omega.
    rewrite H0; try omega. reflexivity.
  - destruct H, H0. exists (S (max x0 x1)). intros mx h.
    assert (l1:= max_fst x0 x1). assert (l2:= max_snd x0 x1).
    cbn. rewrite (j mx); try omega. rewrite (H (mx - 1)); try omega.
    destruct (whFixStep dts m).
    + myInjection e. rewrite H0; try omega. reflexivity.
    + discriminate.
  - destruct H, H0. exists (S (max x x0)). intros mx h.
    assert (l1:= max_fst x x0). assert (l2:= max_snd x x0).
    destruct a as [z0 [z1 [z2 z3]]].
    simpl. rewrite (j mx); try omega. rewrite (H (mx - 1)); try omega.
    destruct fn'; try rewrite H0; try reflexivity; try omega.
    + elim z3. auto.
    + elim z0. auto.
    + elim z2. auto.
    + elim z1. auto.
  - destruct H, H0. exists (S (max x x0)). intros mx h.
    assert (l1:= max_fst x x0). assert (l2:= max_snd x x0).
    cbn. rewrite (j mx); try omega. rewrite (H (mx - 1)); try omega.
    rewrite e. destruct (inductive_dec i i).
    + apply (H0 (mx - 1)); try omega.
    + now elim n0.
  - destruct H, H0. exists (S (max x0 x1)). intros mx h.
    assert (l1:= max_fst x0 x1). assert (l2:= max_snd x0 x1).
    simpl. rewrite (j mx); try omega. rewrite (H (mx - 1)); try omega.
    rewrite e. destruct (inductive_dec ind ind).
    + apply (H0 (mx - 1)); try omega.
    + now elim n.
  - destruct H, H0. exists (S (max x x0)). intros mx h.
    assert (l1:= max_fst x x0). assert (l2:= max_snd x x0).
    simpl. rewrite (j mx); try omega. rewrite (H (mx - 1)); try omega.
    rewrite H0; try omega. reflexivity.
Qed.

Lemma WcbvEval_wcbvEval:
  forall t s, WcbvEval p t s ->
             exists n, forall m, m >= n -> wcbvEval m t = Ret s.
Proof.
  intros t s h.
  destruct (proj1 pre_WcbvEval_wcbvEval _ _ h).
  exists (S x). intros m hm. specialize (H (m - 1)).
  assert (k: m = S (m - 1)). { omega. }
  rewrite k. apply H. omega.
Qed.
  
Lemma wcbvEval_up:
 forall t s tmr,
   wcbvEval tmr t = Ret s ->
   exists n, forall m, m >= n -> wcbvEval m t = Ret s.
Proof.
  intros. 
  destruct (WcbvEval_wcbvEval (proj1 (wcbvEval_WcbvEval tmr) t s H)).
  exists x. apply H0.
Qed.

End wcbvEval_sec.
