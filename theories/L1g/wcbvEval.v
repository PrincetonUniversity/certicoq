Require Import FunInd.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Program.Basics.
Require Import Coq.omega.Omega.
Require Import Common.AstCommon.
Require Import L1g.term.
Require Import L1g.program.
Require Import L1g.wndEval.

Delimit Scope string_scope with string.
Open Scope string_scope.
Open Scope bool.
Open Scope list.
Set Implicit Arguments.


(** Big step relation of weak cbv evaluation  **)
Inductive WcbvEval (p:environ Term) : Term -> Term -> Prop :=
| wLam: forall nm bod, WcbvEval p (TLambda nm bod) (TLambda nm bod)
| wProof: WcbvEval p TProof TProof
| wAppProof fn arg arg':
    WcbvEval p fn TProof ->
    WcbvEval p arg arg' ->
    WcbvEval p (TApp fn arg) TProof
| wConstruct: forall i r np na,
    WcbvEval p (TConstruct i r np na) (TConstruct i r np na)
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
| wAppFix: forall dts m n (fn arg s x:Term),
    WcbvEval p fn (TFix dts m) ->
    dnthBody m dts = Some (x,n) ->
    WcbvEval p (pre_whFixStep x dts arg) s ->
    WcbvEval p (TApp fn arg) s 
| wAppCong: forall fn fn' arg arg', 
    WcbvEval p fn fn' ->
    (~ isLambda fn' /\ ~ isFix fn' /\ fn' <> TProof) ->
    WcbvEval p arg arg' ->
    WcbvEval p (TApp fn arg) (TApp fn' arg')
| wCase: forall mch Mch n args ml ts brs cs s npars nargs,
    WcbvEval p mch Mch ->
    canonicalP Mch = Some (n, npars, nargs, args) ->
    tskipn (snd ml) args = Some ts ->
    whCaseStep n ts brs = Some cs ->
    WcbvEval p cs s ->
    WcbvEval p (TCase ml mch brs) s
| wProj: forall bod Bod r npars nargs args arg x ind res,
    WcbvEval p bod Bod ->
    canonicalP Bod = Some (r, npars, nargs, args) ->
    List.nth_error args (npars + arg) = Some x ->
    WcbvEval p x res ->
    WcbvEval p (TProj (ind, npars, arg) bod) res.
Hint Constructors WcbvEval : core.

(** when reduction stops **)
Definition no_Wcbv_step (p:environ Term) (t:Term) : Prop :=
  no_step (WcbvEval p) t.

(** evaluate omega = (\x.xx)(\x.xx): nontermination **)
Definition xx := TLambda nAnon (TApp (TRel 0) (TRel 0)).
Definition xxxx := TApp xx xx.
Goal WcbvEval nil xxxx xxxx.
Proof.
  unfold xxxx, xx. eapply wAppLam.
  - constructor.
  - eapply wLam.
  - cbn. change (WcbvEval nil xxxx xxxx).
Abort.
             
Lemma WcbvEval_pres_WFapp:
  forall p t s, WcbvEval p t s -> WFaEnv p -> WFapp t -> WFapp s.
Proof.
  induction 1; intros; try (first [assumption | constructor]). 
  - apply IHWcbvEval. assumption. eapply lookupDfn_pres_WFapp; eassumption.
  - apply IHWcbvEval3. assumption. inversion_Clear H3.
    intuition. inversion_Clear H8. apply whBetaStep_pres_WFapp; assumption.
  - intuition. apply H4. inversion_Clear H2.
    apply instantiate_pres_WFapp; intuition.
  - inversion_Clear H3. intuition. apply H4. inversion_Clear H5.
    apply pre_whFixStep_pres_WFapp; try assumption.
    eapply (dnthBody_pres_WFapp); eassumption.
  - inversion_Clear H3. intuition.
  - inversion_Clear H3. intuition.
  - inversion_Clear H5. intuition. apply H6.
    pose proof (canonicalP_pres_WFapp H0 eq_refl H7) as j0.
    pose proof (tskipn_pres_WFapp j0 _ H1) as j1.
    apply (whCaseStep_pres_WFapp H10 j1 _ H2).
  - inversion_Clear H4. intuition. apply H5.
    eapply WFapps_all; try eassumption.
    eapply canonicalP_pres_WFapp; try reflexivity; eassumption.
Qed.
    
Lemma WcbvEval_single_valued:
  forall p t s, WcbvEval p t s -> forall u, WcbvEval p t u -> s = u.
Proof.
  induction 1; intros; try (inversion_Clear H; reflexivity).
  - inversion_Clear H1; trivial.
    + specialize (IHWcbvEval1 _ H4). discriminate.
    + specialize (IHWcbvEval1 _ H4). discriminate.
    + destruct H5 as [a [b c]]. elim c.
      symmetry. apply IHWcbvEval1. assumption.
  - inversion_Clear H1. rewrite H in H3. myInjection H3. intuition.
  - inversion_Clear H2.
    + specialize (IHWcbvEval1 _ H5). discriminate.
    + specialize (IHWcbvEval1 _ H5). myInjection IHWcbvEval1.
      specialize (IHWcbvEval2 _ H6). subst. intuition.
    + specialize (IHWcbvEval1 _ H5). discriminate.
    + destruct H6 as [a [b c]]. specialize (IHWcbvEval1 _ H5).
      elim a. subst. auto.
  - inversion_Clear H1. specialize (IHWcbvEval1 _ H6). subst. intuition.
  - inversion_Clear H2.
    + specialize (IHWcbvEval1 _ H5). discriminate.
    + specialize (IHWcbvEval1 _ H5). discriminate.
    + specialize (IHWcbvEval1 _ H5). myInjection IHWcbvEval1.
      rewrite H0 in H6. myInjection H6. intuition.
    + destruct H6 as [a [b c]]. specialize (IHWcbvEval1 _ H5). subst fn'.
      destruct b. auto.
  - destruct H0 as [a [b c]]. inversion_Clear H2.
      * specialize (IHWcbvEval1 _ H4). subst. elim c. reflexivity.
      * specialize (IHWcbvEval1 _ H4). subst. elim a. auto. 
      * specialize (IHWcbvEval1 _ H4). subst. elim b. auto. 
      * destruct H5 as [e [f g]].
        specialize (IHWcbvEval1 _ H4). specialize (IHWcbvEval2 _ H7).
        subst. reflexivity.
  - inversion_Clear H4. specialize (IHWcbvEval1 _ H8). subst.
    rewrite H0 in H9. myInjection H9. rewrite H1 in H10. myInjection H10.
    rewrite H2 in H12. myInjection H12. intuition.
  - inversion_Clear H3. specialize (IHWcbvEval1 _ H8). subst Bod0.
    rewrite H0 in H10. myInjection H10.
    rewrite H1 in H11. myInjection H11.
    apply IHWcbvEval2. assumption.
Qed.
 
Lemma sv_cor:
  forall p fn fn' t s,
    WcbvEval p fn t -> WcbvEval p fn' t -> WcbvEval p fn s -> WcbvEval p fn' s.
Proof.
  intros. rewrite <- (WcbvEval_single_valued H H1). assumption.
Qed.
  
Lemma WcbvEval_no_further:
  forall p t s, WcbvEval p t s -> WcbvEval p s s.
Proof.
  induction 1; intros; auto.
Qed.

Lemma WcbvEval_trn:
  forall p s t,
    WcbvEval p s t ->
    forall u,
      WcbvEval p t u -> WcbvEval p s u.
Proof.
  intros.
  pose proof (WcbvEval_no_further H) as j0.
  rewrite (WcbvEval_single_valued H0 j0).
  assumption.
Qed.

Lemma WcbvEval_weaken:
  forall p t s, WcbvEval p t s ->
                 forall nm ec, fresh nm p -> WcbvEval ((nm,ec)::p) t s.
Proof.
  induction 1; intros; auto.
  - specialize (IHWcbvEval1 _ ec H1). specialize (IHWcbvEval2 _ ec H1).
    econstructor; eassumption.
  - destruct (kername_eq_dec nm nm0).
    + subst. unfold lookupDfn in H.
      rewrite (proj1 (fresh_lookup_None (trm:=Term) _ _) H1) in H.
      discriminate.
    + eapply wConst.
      * rewrite <- (lookupDfn_weaken' n). eassumption. 
      * apply IHWcbvEval. assumption. 
  - eapply wAppLam.
    + apply IHWcbvEval1. assumption.                           
    + apply IHWcbvEval2. assumption.
    + apply IHWcbvEval3. assumption.
  - eapply wLetIn; intuition.
  - eapply wAppFix; try eassumption; intuition.
  - eapply wCase; try eassumption; intuition.
  - eapply wProj; try eassumption; intuition.
Qed.

Lemma WcbvEval_wndEvalRTC:
  forall (p:environ Term), WFaEnv p ->
    forall t s, WcbvEval p t s -> WFapp t -> wndEvalRTC p t s.
Proof.
  intros p hp. induction 1; intros; try (solve [constructor]).
  - inversion_Clear H1. intuition.
    eapply wndEvalRTC_App_Proof; try eassumption. reflexivity.
  - eapply wERTCtrn; intuition. eapply wERTCtrn.
    + apply wERTCstep. apply sConst. apply lookupDfn_LookupDfn. eassumption.
    + apply IHWcbvEval. eapply (lookupDfn_pres_WFapp hp).  eassumption. 
  - inversion_Clear H2. intuition.
    eapply (@wERTCtrn _ _ (TApp (TLambda nm bod) a1)).
    + apply wndEvalRTC_App_fn; assumption. 
    + eapply (@wERTCtrn _ _ (TApp (TLambda nm bod) a1')).
      * eapply wndEvalRTC_App_arg; try reflexivity. assumption.
      * apply (@wERTCtrn _ _ (whBetaStep bod a1')).
        -- apply wERTCstep. apply sBeta.
        -- apply IHWcbvEval3. apply whBetaStep_pres_WFapp.
           ++ pose proof (WcbvEval_pres_WFapp H hp H5). inversion_Clear H4.
              assumption.
           ++ eapply WcbvEval_pres_WFapp; eassumption.
  - inversion_Clear H1. eapply (@wERTCtrn _ _ (TLetIn nm dfn' bod)).
    + apply wndEvalRTC_LetIn_dfn. intuition.
    + eapply wERTCtrn.
      * apply wERTCstep. apply sLetIn.
      * apply IHWcbvEval2. apply instantiate_pres_WFapp; try assumption.
        eapply WcbvEval_pres_WFapp; eassumption.
  - inversion_clear H2. intuition.
    assert (j2: WFapp (TFix dts m)).
    { refine (WcbvEval_pres_WFapp _ _ _); eassumption. }
    inversion_Clear j2.
    assert (j3: WFapp x).
    { refine (dnthBody_pres_WFapp _ _ _); eassumption. }
    assert (j4: WFapp (pre_whFixStep x dts arg)).
    { refine (pre_whFixStep_pres_WFapp _ _ _); try assumption. }
    intuition.
    refine (@wERTCtrn _ _ (TApp (TFix dts m) arg) _ _ _).
    + apply wndEvalRTC_App_fn; try assumption.
    + eapply (@wERTCtrn _ _  (pre_whFixStep x dts arg)).
      * eapply wERTCstep. eapply sFix; try eassumption.
      * assumption.
  - inversion_Clear H2.
    specialize (IHWcbvEval1 H5). specialize (IHWcbvEval2 H6).
    apply wndEvalRTC_App_fn_arg; assumption.
  - inversion_Clear H4. intuition.
    pose proof (WcbvEval_pres_WFapp H hp H7) as j0.
    pose proof (canonicalP_pres_WFapp H0 eq_refl j0) as j1.
    pose proof (tskipn_pres_WFapp j1 _ H1) as j2.
    pose proof (whCaseStep_pres_WFapp H9 j2 _ H2) as j3.
    intuition. eapply wERTCtrn. instantiate (1:= (TCase ml Mch brs)).
    + eapply wndEvalRTC_Case_mch. assumption.
    + eapply wERTCtrn. instantiate (1:= cs).
      * eapply wERTCstep. eapply sCase; try eassumption.
      * assumption.
  - inversion_Clear H3. intuition.
    assert (j2: WFapp Bod).
    { refine (WcbvEval_pres_WFapp _ _ _); eassumption. }
    assert (j3: WFapp x).
    { refine (WFapps_all _ _ _); try eassumption.
      eapply canonicalP_pres_WFapp; try eassumption. reflexivity. }
    intuition. eapply wERTCtrn; try eassumption.
    inversion_Clear H3.
    + apply wERTCstep. eapply sProj; eassumption.
    + eapply wERTCtrn. instantiate (1:= (TProj (ind, npars, arg) Bod)).
      apply wndEvalRTC_Proj_bod; try assumption.
      * apply wERTCstep. assumption.
      * apply wERTCstep. eapply sProj; eassumption.
    + eapply wERTCtrn. instantiate (1:= (TProj (ind, npars, arg) Bod)).
      * eapply wERTCtrn. apply wndEvalRTC_Proj_bod; try eassumption.
        apply wndEvalRTC_Proj_bod; try eassumption.
        eapply wndEvalRTC_pres_WFapp; eassumption.
      * eapply wERTCstep. econstructor; eassumption.
Qed.


(** now an executable weak-call-by-value evaluation **)
(** use a timer to make this terminate **)
Section wcbvEval_sec.
Variable p:environ Term.

Local Open Scope string_scope.

Function wcbvEval
         (tmr:nat) (t:Term) {struct tmr}: exception Term :=
  match tmr with 
  | 0 => raise ("out of time: " ++ print_term t)
  | S n =>
    match t with      (** look for a redex **)
    | TConst nm =>
      match (lookup nm p) with
      | Some (AstCommon.ecTrm t) => wcbvEval n t
      (** note hack coding of axioms in environment **)
      | Some (AstCommon.ecTyp _ _) => raise ("wcbvEval, TConst ecTyp " ++ string_of_kername nm)
      | _ => raise "wcbvEval: TConst environment miss"
      end
    | TProof => Ret TProof
    | TApp fn a1 =>
      match wcbvEval n fn with
      | Exc str =>  raise ("(wcbvEval;TApp:fn" ++ str ++ ")")
      | Ret TProof =>          (* Proof redex *)
        match wcbvEval n a1 with
        | Exc s =>  raise ("wcbvEval,ProofRedex,arg: " ++ s)
        | Ret _ => Ret TProof 
        end
      | Ret (TLambda _ bod) =>
        match wcbvEval n a1 with
        | Exc s =>  raise ("wcbvEval beta:arg: "
                             ++ print_term a1 ++ ";" ++ s)
        | Ret b1 => wcbvEval n (whBetaStep bod b1)
        end
      | Ret (TFix dts m) =>           (* Fix redex *)
        match dnthBody m dts with
        | None => raise ("wcbvEval TApp: dnthBody doesn't eval: ")
        | Some (x,_) => wcbvEval n (pre_whFixStep x dts a1)
        end
      | Ret (_ as u) =>
        match wcbvEval n a1 with
        | Exc s =>  raise ("wcbvEval,Cong,arg: " ++ s)
        | Ret b1 => ret (TApp u b1)  (* congruence *)
        end
      end
    | TCase (ind,m) mch brs =>
      match wcbvEval n mch with
      | Exc str => Exc str
      | Ret emch =>
        match canonicalP emch with
        | None =>
          raise ("(wcbvEval:Case, discriminee not canonical: "
                   ++ print_inductive ind ++ " " ++ print_term mch ++
                   " " ++ print_term emch ++ ")")
        | Some (r, _, _, args) =>
          match tskipn m args with
          | None => raise "wcbvEval: Case, tskipn"
          | Some ts =>
            match whCaseStep r ts brs with
            | None => raise "wcbvEval: Case,whCaseStep"
            | Some cs => wcbvEval n cs
            end
          end
        end
      end
    | TLetIn nm df bod =>
      match wcbvEval n df with
      | Ret df' => wcbvEval n (instantiate df' 0 bod)
      | Exc s => raise ("wcbvEval: TLetIn: " ++ s)
      end
    | TProj (_, npars, arg) bod =>
      match wcbvEval n bod with
      | Exc s => raise ("(wcbvEval:TProj,bod: " ++ s ++ ")")
      | Ret Bod =>
        match canonicalP Bod with
        | None =>
          raise ("(wcbvEval:Proj,canonicalP: " ++ print_term bod ++
                   " " ++ print_term Bod ++ ")")
        | Some (_, mpars, nargs, args) =>
          match List.nth_error args (npars + arg) with
          | None => raise ("wcbvEval:TProj,nth_error")
          | Some x =>
            match Nat.eqb npars mpars with
            | true => wcbvEval n x
            | false => raise ("wcbvEval:TProj,nth_error")
            end
          end
        end
      end
    (** already in whnf ***)
    | (TLambda _ _) as u
    | (TConstruct _ _ _ _) as u
    | (TFix _ _) as u => ret u
    (** should never appear **)
    | TRel _ => raise "wcbvEval: unbound Rel"
    | TWrong s => raise ("(TWrong:" ++ s ++")")
    end
  end.

(**********************
with wcbvEvals (tmr:nat) (ts:Terms) {struct tmr} : exception Terms :=
       match tmr with 
        | 0 => raise "out of time"
        | S n => match ts with             (** look for a redex **)
                 | tnil => ret tnil
                 | tcons s ss =>
                   match wcbvEval n s, wcbvEvals n ss with
                   | Ret es, Ret ess => ret (tcons es ess)
                   | Exc s, _ => raise s
                   | Ret _, Exc s => raise s
                   end
                 end
        end.

Functional Scheme wcbvEval_ind' := Induction for wcbvEval Sort Prop
  with wcbvEvals_ind' := Induction for wcbvEvals Sort Prop.
Combined Scheme wcbvEvalEvals_ind from wcbvEval_ind', wcbvEvals_ind'.
*******************)

(** wcbvEval and WcbvEval are the same relation **)
Lemma wcbvEval_WcbvEval:
  forall tmr t s, wcbvEval tmr t = Ret s -> WcbvEval p t s.
Proof.
  intros tmr t.
  functional induction (wcbvEval tmr t); intros; try discriminate;
  try (myInjection H); try(solve[constructor]); intuition.
  - eapply wConst; intuition.
    + unfold lookupDfn. rewrite e1. reflexivity.
  - specialize (IHe _ e1). specialize (IHe0 _ e2).
    eapply wAppProof; eassumption.
  - specialize (IHe _ e1). specialize (IHe0 _ e2). specialize (IHe1 _ H).
    eapply wAppLam; eassumption.
  - specialize (IHe _ e1). specialize (IHe0 _ H).
    eapply wAppFix; try eassumption.
  - specialize (IHe _ e1). specialize (IHe0 _ e2).
    eapply wAppCong; try assumption. repeat split; intros h.
    + dstrctn h. subst. contradiction.
    + dstrctn h. subst. contradiction. 
    + subst. contradiction. 
  - specialize (IHe _ e1). specialize (IHe0 _ H).
    eapply wCase; try eassumption.
  - specialize (IHe _ e1). specialize (IHe0 _ H).
    eapply wLetIn; eassumption.
  - specialize (IHe _ e1). specialize (IHe0 _ H).
    rewrite <- (Nat_eqb_rfl _ _ e4) in e2. eapply wProj; try eassumption.  
Qed.

(** need strengthening to large-enough fuel to make the induction
 *** go through **)
Lemma pre_WcbvEval_wcbvEval:
  forall t s, WcbvEval p t s ->
              exists n, forall m, m >= n -> wcbvEval (S m) t = Ret s.
Proof.
  assert (j:forall m, m > 0 -> m = S (m - 1)).
  { induction m; intuition. }
  induction 1; intros; try (exists 0; intros mx h; reflexivity).
  - destruct IHWcbvEval1, IHWcbvEval2. exists (S (max x x0)). intros mx h.
    assert (l1:= max_fst x x0). assert (l2:= max_snd x x0).
    simpl. rewrite (j mx); try omega. rewrite H1; try omega.
    rewrite H2; try omega. reflexivity.
  - dstrctn IHWcbvEval.
    exists (S x). intros m hm. simpl. rewrite (j m); try omega.
    unfold lookupDfn in H.
    + destruct (lookup nm p).
      * destruct e. myInjection H. apply j0. omega. discriminate.
      * discriminate.
  - destruct IHWcbvEval1, IHWcbvEval2, IHWcbvEval3.
    exists (S (max x (max x0 x1))). intros m h.
    assert (j1:= max_fst x (max x0 x1)). 
    assert (lx: m > x). omega.
    assert (j2:= max_snd x (max x0 x1)).
    assert (j3:= max_fst x0 x1).
    assert (lx0: m > x0). omega.
    assert (j4:= max_snd x0 x1).
    assert (j5:= max_fst x0 x1).
    assert (lx1: m > x1). omega.
    assert (k:wcbvEval m fn = Ret (TLambda nm bod)).
    { rewrite (j m). apply H2.
      assert (l:= max_fst x (max x0 x1)); omega. omega. }
    assert (k0:wcbvEval m a1 = Ret a1').
    { rewrite (j m). apply H3. 
      assert (l:= max_snd x (max x0 x1)). assert (l':= max_fst x0 x1).
      omega. omega. }
    simpl. rewrite (j m); try omega.
    rewrite H2; try omega. rewrite H3; try omega. rewrite H4; try omega.
    reflexivity.
  - destruct IHWcbvEval1, IHWcbvEval2. exists (S (max x x0)). intros mx h.
    assert (l1:= max_fst x x0). assert (l2:= max_snd x x0).
    simpl. rewrite (j mx); try omega. rewrite H1; try omega.
    rewrite H2; try omega. reflexivity.
  - destruct IHWcbvEval1, IHWcbvEval2. exists (S (max x0 x1)). intros mx h.
    assert (l1:= max_fst x0 x1). assert (l2:= max_snd x0 x1).
    cbn. rewrite (j mx); try omega. rewrite H2; try omega.
   rewrite H0; try omega. rewrite H3; try omega. reflexivity.
  - destruct IHWcbvEval1, IHWcbvEval2. exists (S (max x x0)). intros mx h.
    assert (l1:= max_fst x x0). assert (l2:= max_snd x x0).
    destruct H0 as [a [b c]].
    simpl. rewrite (j mx); try omega. rewrite H2; try omega.
    destruct fn'; try rewrite H3; try omega; try reflexivity.
    + elim c. reflexivity.
    + elim a. auto.
    + elim b. auto.
  - destruct IHWcbvEval1, IHWcbvEval2. exists (S (max x x0)). intros mx h.
    assert (l1:= max_fst x x0). assert (l2:= max_snd x x0).
    simpl. destruct ml. rewrite (j mx); try omega. rewrite H4; try omega.  
    rewrite H0. unfold snd in H1. rewrite H1. rewrite H2.
    rewrite H5; try omega. reflexivity.
  - destruct IHWcbvEval1, IHWcbvEval2. exists (S (max x0 x1)). intros mx h.
    assert (l1:= max_fst x0 x1). assert (l2:= max_snd x0 x1).
    simpl. rewrite (j mx); try omega. rewrite H3; try omega.
    rewrite H0. rewrite H1. rewrite rfl_Nat_eqb.
    rewrite H4; try omega. reflexivity.
Qed.

Lemma WcbvEval_wcbvEval:
  forall t s, WcbvEval p t s ->
             exists n, forall m, m >= n -> wcbvEval m t = Ret s.
Proof.
  intros t s h.
  edestruct (pre_WcbvEval_wcbvEval). eassumption.
  exists (S x). intros m hm. specialize (H (m - 1)).
  assert (k: m = S (m - 1)). { omega. }
  rewrite k. apply H. omega.
Qed.

Lemma wcbvEval_up:
 forall t s tmr,
   wcbvEval tmr t = Ret s ->
   exists n, forall m, m >= n -> wcbvEval m t = Ret s.
Proof.
  intros. destruct (WcbvEval_wcbvEval (wcbvEval_WcbvEval tmr t H)). 
  exists x. apply H0.
Qed.

End wcbvEval_sec.

