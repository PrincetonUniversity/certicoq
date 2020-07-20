(** Uncurrying written as a guarded rewrite rule *)

Require Import Coq.Strings.String Coq.Classes.Morphisms.
Require Import Coq.NArith.BinNat Coq.PArith.BinPos Coq.Sets.Ensembles Lia.
Require Import L6.Prototype.
Require Import L6.proto_util.
Require Import L6.cps_proto.
Require Import identifiers.  (* for max_var, occurs_in_exp, .. *)
Require Import L6.Ensembles_util L6.List_util L6.cps_util L6.state.

Require Import Coq.Lists.List.
Import ListNotations.

Require L6.cps.

Set Universe Polymorphism.
Unset Strict Unquote Universe Mode.

(** * Uncurrying as a guarded rewrite rule *)

(* Hack: the pretty-printer uses cdata to associate strings with freshly generated names.
   In order to be able to pretty-print our terms, we'll need to update cdata accordingly even
   though we don't use it to generate fresh names. [set_name] and [set_names_lst] are analogues
   of [get_name] and [get_names_lst] from state.v. *)

Definition set_name old_var new_var suff cdata :=
  let '{| next_var := n; nect_ctor_tag := c; next_ind_tag := i; next_fun_tag := f;
          cenv := e; fenv := fenv; nenv := names; log := log |} := cdata
  in
  let names' := add_entry names new_var old_var suff in
  {| next_var := (1 + Pos.max old_var new_var)%positive; nect_ctor_tag := c;
     next_ind_tag := i; next_fun_tag := f; cenv := e; fenv := fenv;
     nenv := names'; log := log |}.

Definition set_names_lst olds news suff cdata :=
  fold_right (fun '(old, new) cdata => set_name old new suff cdata) cdata (combine olds news).

(** * Auxiliary data used by the rewriter *)

(* true if in cps mode *)
Definition I_R : forall {A}, frames_t A exp_univ_exp -> bool -> Prop := (I_R_plain (R:=bool)).

(* pair of 
   1 - max number of arguments 
   2 - encoding of inlining decision for beta-contraction phase *)
Definition St : Set := (nat * (cps.PM nat))%type.
(* 0 -> Do not inline, 1 -> uncurried function, 2 -> continuation of uncurried function *)

(* Maps (arity+1) to the right fun_tag *)
Definition arity_map : Set := cps.PM fun_tag.
Definition local_map : Set := cps.PM bool.
 
(* The state for this includes 
   1 - a boolean for tracking whether or not a reduction happens
   2 - Map recording the (new) fun_tag associated to each arity
   3 - local map from var to if function has already been uncurried
   4 - Map for uncurried functions for a version of inlining *)
Definition S_misc : Set := bool * arity_map * local_map * St * comp_data.

(* Based on [get_fun_tag] from uncurry.v *)
Definition get_fun_tag (n : N) (ms : S_misc) : fun_tag * S_misc :=
  let '(b, aenv, lm, s, cdata) := ms in
  let n' := N.succ_pos n in
  match M.get n' aenv with
  | Some ft => (ft, ms)
  | None =>
    let '(mft, (cdata, tt)) := compM.runState (get_ftag n) tt (cdata, tt) in
    match mft with
    | compM.Err _ => (mk_fun_tag xH, ms) (* bogus *)
    | compM.Ret ft =>
      let ft := mk_fun_tag ft in
      (ft, (b, M.set n' ft aenv, lm, s, cdata))
    end
  end.

Inductive uncurry_step : exp -> exp -> Prop :=
(* Uncurrying for CPS *)
| uncurry_cps :
  forall (C : frames_t exp_univ_list_fundef exp_univ_exp)
    (f f1 : var) (ft ft1 : fun_tag) (k k' : var) (kt : fun_tag) (fv fv1 : list var)
    (g g' : var) (gt : fun_tag) (gv gv1 : list var) (ge : exp) (fds : list fundef)
    (lhs rhs : list fundef) fp_numargs (ms ms' : S_misc),
  (* Non-linear LHS constraints *)
  k = k' /\
  g = g' /\
  (* Guards: *)
  (* (1) g can't be recursive or invoke k *)
  ~ ![g] \in used_vars ![ge] /\
  ~ ![k] \in used_vars ![ge] /\
  (* (2) gv1, fv1, f1 must be fresh and contain no duplicates *)
  lhs = Ffun f ft (k :: fv) (Efun [Ffun g gt gv ge] (Eapp k' kt [g'])) :: fds /\
  rhs = Ffun f ft (k :: fv1) (Efun [Ffun g gt gv1 (Eapp f1 ft1 (gv1 ++ fv1))] (Eapp k kt [g]))
        :: Ffun f1 ft1 (gv ++ fv) ge :: fds /\
  fresh_copies (used_vars (exp_of_proto (C ⟦ lhs ⟧))) gv1 /\ length gv1 = length gv /\
  fresh_copies (used_vars (exp_of_proto (C ⟦ lhs ⟧)) :|: FromList ![gv1]) fv1 /\ length fv1 = length fv /\
  ~ ![f1] \in (used_vars (exp_of_proto (C ⟦ lhs ⟧)) :|: FromList ![gv1] :|: FromList ![fv1]) /\
  (* (3) generate fun_tag + update ms *)
  fp_numargs = length fv + length gv /\
  (ft1, ms') = get_fun_tag (N.of_nat fp_numargs) ms ->
  (* The rewrite *)
  uncurry_step
    (C ⟦ Ffun f ft (k :: fv) (Efun [Ffun g gt gv ge] (Eapp k' kt [g'])) :: fds ⟧)
    (C ⟦ (* Rewrite f as a wrapper around the uncurried f1 and recur on fds *)
         (Ffun f ft (k :: fv1) (Efun [Ffun g gt gv1 (Eapp f1 ft1 (gv1 ++ fv1))] (Eapp k kt [g]))
          :: Ffun f1 ft1 (gv ++ fv) ge :: Rec fds) ⟧)
(* Uncurrying for ANF *)
| uncurry_anf :
  forall (C : frames_t exp_univ_list_fundef exp_univ_exp)
    (f f1 : var) (ft ft1 : fun_tag) (fv fv1 : list var)
    (g g' : var) (gt : fun_tag) (gv gv1 : list var) (ge : exp) (fds : list fundef)
    (lhs rhs : list fundef)
    fp_numargs (ms ms' : S_misc),
  (* Non-linear LHS constraints *)
  g = g' /\
  (* Guards: *)
  (* (1) g can't be recursive *)
  ~ ![g] \in used_vars ![ge] /\
  (* (2) gv1, fv1, f1 must be fresh and contain no duplicates *)
  lhs = Ffun f ft fv (Efun [Ffun g gt gv ge] (Ehalt g')) :: fds /\
  rhs = Ffun f ft fv1 (Efun [Ffun g gt gv1 (Eapp f1 ft1 (gv1 ++ fv1))] (Ehalt g))
        :: Ffun f1 ft1 (gv ++ fv) ge :: fds /\
  fresh_copies (used_vars (exp_of_proto (C ⟦ lhs ⟧))) gv1 /\ length gv1 = length gv /\
  fresh_copies (used_vars (exp_of_proto (C ⟦ lhs ⟧)) :|: FromList ![gv1]) fv1 /\ length fv1 = length fv /\
  ~ ![f1] \in (used_vars (exp_of_proto (C ⟦ lhs ⟧)) :|: FromList ![gv1] :|: FromList ![fv1]) /\
  (* (3) generate fun_tag + update ms *)
  fp_numargs = length fv + length gv /\
  (ft1, ms') = get_fun_tag (N.of_nat fp_numargs) ms ->
  (* The rewrite *)
  uncurry_step
    (C ⟦ Ffun f ft fv (Efun [Ffun g gt gv ge] (Ehalt g')) :: fds ⟧)
    (C ⟦ (* Rewrite f as a wrapper around the uncurried f1 and recur on fds *)
         (Ffun f ft fv1 (Efun [Ffun g gt gv1 (Eapp f1 ft1 (gv1 ++ fv1))] (Ehalt g))
          :: Ffun f1 ft1 (gv ++ fv) ge :: Rec fds) ⟧).

Definition I_S : forall {A}, frames_t A exp_univ_exp -> univD A -> _ -> Prop :=
  I_S_prod (I_S_plain (S:=S_misc)) (@I_S_fresh).

(** * Uncurrying as a recursive function *)

Set Printing Universes.

Lemma bool_true_false b : b = false -> b <> true. Proof. now destruct b. Qed.

Local Ltac clearpose H x e :=
  pose (x := e); assert (H : x = e) by (subst x; reflexivity); clearbody x.

Definition metadata_update (f g f1 : var) fp_numargs (fv gv fv1 gv1 : list var) (ms : S_misc) : S_misc :=
  let '(b, aenv, lm, s, cdata) := ms in
  (* Set flag to indicate that a rewrite was performed (used to iterate to fixed point) *)
  let b := true in
  (* Mark g as uncurried *)
  let lm := M.set ![g] true lm in
  (* Update inlining heuristic so inliner knows to inline fully saturated calls to f *)
  let s := (max (fst s) fp_numargs, (M.set ![f] 1 (M.set ![g] 2 (snd s)))) in
  (* Hack: update cdata to agree with fresh names generated above *)
  let cdata :=
    set_name ![f] ![f1] "_uncurried"
    (set_names_lst ![fv] ![fv1] ""
    (set_names_lst ![gv] ![gv1] "" cdata))
  in
  (b, aenv, lm, s, cdata).

Definition rw_uncurry :
  rewriter exp_univ_exp true tt uncurry_step _ (I_D_plain (D:=unit)) _ (@I_R) _ (@I_S).
Proof.
  mk_rw; mk_easy_delay.
  (* Obligation 1: uncurry_cps side conditions *)
  - intros; unfold delayD, Delayed_id_Delay in *.
    (* Check nonlinearities *)
    destruct k as [k], k' as [k'], g as [g], g' as [g'].
    destruct (eq_var k k') eqn:Hkk'; [|cond_failure].
    destruct (eq_var g g') eqn:Hgg'; [|cond_failure].
    rewrite Pos.eqb_eq in Hkk', Hgg'.
    (* Unpack parameter and state *)
    rename r into mr; unfold Param, I_R, I_R_plain in mr; destruct mr as [mr _].
    destruct s as [[ms next_x] Hnext_x] eqn:Hs.
    destruct ms as [[[[b aenv] lm] heuristic] cdata] eqn:Hms.
    (* Check whether g has already been uncurried before *)
    destruct (mr && negb (match M.get g lm with Some true => true | _ => false end))%bool
      as [|] eqn:Huncurried; [|cond_failure].
    (* Check that {g, k} ∩ vars(ge) = ∅ *)
    destruct (occurs_in_exp g ![ge]) eqn:Hocc_g; [cond_failure|]. (* TODO: avoid the conversion *)
    destruct (occurs_in_exp k ![ge]) eqn:Hocc_k; [cond_failure|]. (* TODO: avoid the conversion *)
    apply bool_true_false in Hocc_g; apply bool_true_false in Hocc_k.
    rewrite occurs_in_exp_iff_used_vars in Hocc_g, Hocc_k.
    (* Generate ft1 + new misc state ms *)
    pose (fp_numargs := length fv + length gv).
    cond_success success; specialize success with (ms := ms) (fp_numargs := fp_numargs).
    destruct (get_fun_tag (BinNatDef.N.of_nat fp_numargs) ms) as [ft1 ms'] eqn:Hms'.
    (* Generate f1, fv1, gv1, next_x *)
    clearpose Hxgv1 xgv1 (gensyms next_x gv); destruct xgv1 as [next_x0 gv1].
    clearpose Hxfv1 xfv1 (gensyms next_x0 fv); destruct xfv1 as [next_x1 fv1].
    clearpose Hf1 f1 next_x1.
    specialize success with (f1 := mk_var f1) (fv1 := fv1) (gv1 := gv1).
    (* Prove that all the above code actually satisfies the side condition *)
    unfold I_S, I_S_prod, I_S_plain, I_S_fresh in *.
    specialize (success fds d f ft (mk_var k) fv (mk_var g) gt gv ge (mk_var k') kt (mk_var g') ft1).
    pose (lhs := Ffun f ft (mk_var k :: fv)
                   (Efun [Ffun (mk_var g) gt gv ge] (Eapp (mk_var k') kt [mk_var g'])) :: fds).
    pose (rhs := Ffun f ft (mk_var k :: fv1)
                  (Efun [Ffun (mk_var g) gt gv1 (Eapp (mk_var f1) ft1 (gv1 ++ fv1))]
                    (Eapp (mk_var k) kt [mk_var g])) :: Ffun (mk_var f1) ft1 (gv ++ fv) ge :: fds).
    specialize (success lhs rhs ms').
    eapply success; [|reflexivity|reflexivity| |];
    try lazymatch goal with
    | |- «_» => unerase; destruct Hnext_x as [? Hnext_x]; 
      (edestruct (@gensyms_spec var) as [Hgv_copies [Hfresh_gv Hgv_len]]; try exact Hxgv1; [eassumption|]);
      (edestruct (@gensyms_spec var) as [Hfv_copies [Hfresh_fv Hfv_len]]; try exact Hxfv1; [eassumption|]);
      repeat match goal with |- _ /\ _ => split end;
      try solve [reflexivity|eassumption|subst;reflexivity|reflexivity]
    | |- Delay _ _ => exact d
    | |- Param _ _ => exists mr; unerase; exact I
    end.
    + apply fresher_than_not_In; subst f1; exact Hfresh_fv.
    + (* Explain how to update state.
         There are two parts: update various pieces of metadata and show that next_x is still fresh *)
      exists (metadata_update f [g]! [f1]! fp_numargs fv gv fv1 gv1 ms', next_x1 + 1)%positive.
      unerase; split; [exact I|].
      destruct Hnext_x as [? Hnext_x];
      edestruct (@gensyms_spec var) as [Hgv_copies [Hfresh_gv Hgv_len]]; try exact Hxgv1; [eassumption|].
      edestruct (@gensyms_spec var) as [Hfv_copies [Hfresh_fv Hfv_len]]; try exact Hxfv1; [eassumption|].
      match type of Hfresh_fv with
      | fresher_than _ ?S =>
        assert (Hunion : fresher_than (next_x1 + 1)%positive (S :|: [set f1]))
      end.
      apply fresher_than_Union; [|subst; simpl; intros y Hy; inversion Hy; lia].
      eapply fresher_than_monotonic; eauto; lia.
      eapply fresher_than_antimon; [|eassumption].
      rewrite used_iso, isoABA, used_app.
      change (exp_of_proto ?A) with ![A].
      rewrite used_iso, isoABA, used_app.
      unfold used; simpl; unbox_newtypes.
      do 10 normalize_used_vars'; repeat normalize_sets.
      rewrite !strip_vars_app; repeat normalize_sets.
      intros arbitrary; rewrite !In_or_Iff_Union; clear; tauto.
  (* Obligation 2: uncurry_anf side conditions *)
  - intros; unfold delayD, Delayed_id_Delay in *.
    (* Check nonlinearities *)
    destruct g as [g], g' as [g'].
    destruct (eq_var g g') eqn:Hgg'; [|cond_failure].
    rewrite Pos.eqb_eq in Hgg'.
    (* Unpack parameter and state *)
    rename r into mr; unfold Param, I_R, I_R_plain in mr; destruct mr as [mr _].
    destruct s as [[ms next_x] Hnext_x] eqn:Hs.
    destruct ms as [[[[b aenv] lm] heuristic] cdata] eqn:Hms.
    (* Check whether g has already been uncurried before *)
    destruct (negb mr && negb (match M.get g lm with Some true => true | _ => false end))%bool
      as [|] eqn:Huncurried; [|cond_failure].
    (* Check that {g, k} ∩ vars(ge) = ∅ *)
    destruct (occurs_in_exp g ![ge]) eqn:Hocc_g; [cond_failure|]. (* TODO: avoid the conversion *)
    apply bool_true_false in Hocc_g.
    rewrite occurs_in_exp_iff_used_vars in Hocc_g.
    (* Generate ft1 + new misc state ms *)
    pose (fp_numargs := length fv + length gv).
    cond_success success; specialize success with (ms := ms) (fp_numargs := fp_numargs).
    destruct (get_fun_tag (BinNatDef.N.of_nat fp_numargs) ms) as [ft1 ms'] eqn:Hms'.
    (* Generate f1, fv1, gv1, next_x *)
    clearpose Hxgv1 xgv1 (gensyms next_x gv); destruct xgv1 as [next_x0 gv1].
    clearpose Hxfv1 xfv1 (gensyms next_x0 fv); destruct xfv1 as [next_x1 fv1].
    clearpose Hf1 f1 next_x1.
    specialize success with (f1 := mk_var f1) (fv1 := fv1) (gv1 := gv1).
    specialize (success fds d f ft fv (mk_var g) gt gv ge (mk_var g') ft1).
    pose (lhs := Ffun f ft fv (Efun [Ffun (mk_var g) gt gv ge] (Ehalt (mk_var g'))) :: fds).
    pose (rhs := Ffun f ft fv1
                   (Efun [Ffun (mk_var g) gt gv1 (Eapp (mk_var f1) ft1 (gv1 ++ fv1))] (Ehalt (mk_var g)))
                 :: Ffun (mk_var f1) ft1 (gv ++ fv) ge :: fds).
    specialize (success lhs rhs ms').
    (* Prove that all the above code actually satisfies the side condition *)
    eapply success; [|reflexivity|reflexivity| |];
    try lazymatch goal with
    | |- «_» => unerase; destruct Hnext_x as [? Hnext_x]; 
      (edestruct (@gensyms_spec var) as [Hgv_copies [Hfresh_gv Hgv_len]]; try exact Hxgv1; [eassumption|]);
      (edestruct (@gensyms_spec var) as [Hfv_copies [Hfresh_fv Hfv_len]]; try exact Hxfv1; [eassumption|]);
      repeat match goal with |- _ /\ _ => split end;
      try solve [reflexivity|eassumption|subst;reflexivity|reflexivity]
    | |- Delay _ _ => exact d
    | |- Param _ _ => exists mr; unerase; exact I
    end.
    + apply fresher_than_not_In; subst f1; exact Hfresh_fv.
    + exists (metadata_update f [g]! [f1]! fp_numargs fv gv fv1 gv1 ms', next_x1 + 1)%positive.
      unerase; split; [exact I|].
      destruct Hnext_x as [? Hnext_x];
      edestruct (@gensyms_spec var) as [Hgv_copies [Hfresh_gv Hgv_len]]; try exact Hxgv1; [eassumption|].
      edestruct (@gensyms_spec var) as [Hfv_copies [Hfresh_fv Hfv_len]]; try exact Hxfv1; [eassumption|].
      match type of Hfresh_fv with
      | fresher_than _ ?S =>
        assert (Hunion : fresher_than (next_x1 + 1)%positive (S :|: [set f1]))
      end.
      apply fresher_than_Union; [|subst; simpl; intros y Hy; inversion Hy; lia].
      eapply fresher_than_monotonic; eauto; lia.
      eapply fresher_than_antimon; [|eassumption].
      rewrite used_iso, isoABA, used_app.
      change (exp_of_proto ?A) with ![A].
      rewrite used_iso, isoABA, used_app.
      unfold used; simpl; unbox_newtypes.
      do 10 normalize_used_vars'; repeat normalize_sets.
      rewrite !strip_vars_app; repeat normalize_sets.
      intros arbitrary; rewrite !In_or_Iff_Union; clear; tauto.
Defined.

Set Extraction Flag 2031. (* default + linear let + linear beta *)
Recursive Extraction rw_uncurry.

Lemma uncurry_one (cps : bool) (ms : S_misc) (e : exp) (s : State (@I_S_fresh) (erase <[]>) e)
  : option (result (Root:=exp_univ_exp) uncurry_step (@I_S) (erase <[]>) e).
Proof.
  Print run_rewriter'.
  pose (res := run_rewriter' rw_uncurry e (exist _ cps I) (exist _ (ms, proj1_sig s) (conj I (proj2_sig s))));
               destruct res eqn:Hres.
  exact (let 'exist ((b, _, _, _, _), _) _ := resState in if b then Some res else None).
Defined.

Fixpoint uncurry_fuel (cps : bool) (n : nat) (ms : S_misc) (e : exp)
         (s : State (@I_S_fresh) (erase <[]>) e) {struct n}
  : result (Root:=exp_univ_exp) uncurry_step (@I_S) (erase <[]>) e.
Proof.
  destruct n as [|n].
  - unshelve econstructor; [exact e|exact (exist _ (ms, proj1_sig s) (conj I (proj2_sig s)))|do 2 constructor].
  - pose (res := uncurry_one cps ms e s).
    refine (match res with Some res' => _ | None => _ end).
    + destruct res'.
      destruct resState as [[[[[[? aenv] lm] st] cdata] resState] Hstate].
      unfold I_S, I_S_prod in Hstate.
      destruct (uncurry_fuel cps n (false, aenv, lm, st, cdata) resTree)
        as [resTree' resState' resProof'].
      * exists resState; unerase; now destruct Hstate.
      * unshelve econstructor; [exact resTree'|auto|].
        eapply Relation_Operators.rt_trans; eauto.
    + unshelve econstructor; [exact e|exact (exist _ (ms, proj1_sig s) (conj I (proj2_sig s)))
                              |apply Relation_Operators.rt_refl].
Defined.

Definition uncurry_top (cps : bool) (n : nat) (cdata : comp_data) (e : exp) : exp * M.t nat * comp_data.
Proof.
  refine (
    let '{| resTree := e'; resState := exist (ms, _) (conj I _) |} := uncurry_fuel cps n _ e (initial_fresh e) in
    _).
  - exact (false, M.empty _, M.empty _, (0%nat, (M.empty _)), cdata).
  - destruct ms as [[[[? ?] ?] [? st]] cdata'].
    exact (e', st, cdata').
Defined.
