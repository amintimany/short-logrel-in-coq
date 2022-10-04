From Coq.Unicode Require Import Utf8.
From Coq.Lists Require Import List.
From Autosubst Require Import Autosubst.
From Coq.Relations Require Import Relations.
From Coq.micromega Require Import Lia.
From ShortLogrels Require Import prelude language systemF_cbv.


Definition rel_in_env (Δ : environment (expr → Prop)) (X : var) (v : expr) : Prop :=
  is_val v ∧ match lookup Δ X with Some P => P v | None => True end.

Fixpoint val_rel (Δ : environment (expr → Prop)) (τ : type) (v : expr) : Prop :=
  match τ with
  |TUnit => v = TT
  |TVar X => rel_in_env Δ X v
  |TProd τ1 τ2 => ∃ v1 v2, v = Pair v1 v2 ∧ val_rel Δ τ1 v1 ∧ val_rel Δ τ2 v2
  |TFun τ1 τ2 => is_val v ∧ ∀ w, val_rel Δ τ1 w → Normalizes (val_rel Δ τ2) (App v w)
  |TForAll τ => is_val v ∧ ∀ P, Normalizes (val_rel (P :: Δ) τ) (TApp v)
  end.

Lemma val_rel_is_val Δ τ v : val_rel Δ τ v → is_val v.
Proof.
  revert Δ v; induction τ; intros Δ v; simpl in *; subst.
  - intros ?; subst; constructor.
  - intros Hv; apply Hv.
  - firstorder; subst; constructor; eauto.
  - tauto.
  - intros Hv; eapply Hv.
Qed.

Definition expr_rel (Δ : environment (expr → Prop)) (τ : type) (e : expr) :=
  Normalizes (val_rel Δ τ) e.

Lemma val_rel_weaken_gen Δ1 Δ' Δ2 τ v :
  val_rel (Δ1 ++ Δ2) τ v ↔ val_rel (Δ1 ++ Δ' ++ Δ2) (weaken (length Δ1) (length Δ') τ) v.
Proof.
  revert Δ1 Δ' Δ2 v.
  induction τ as [| X | | |]; intros Δ1 Δ' Δ2 v.
  - simpl; tauto.
  - simpl.
    rewrite (@weaken_var type); [|apply _]; simpl.
    unfold rel_in_env.
    destruct Nat.ltb eqn:Hlt.
    + apply PeanoNat.Nat.ltb_lt in Hlt.
      repeat (rewrite lookup_app_l; [|assumption]).
      tauto.
    + apply PeanoNat.Nat.ltb_ge in Hlt.
      rewrite app_assoc.
      rewrite lookup_app_r; [|assumption].
      rewrite lookup_app_r; [|rewrite app_length; lia].
      rewrite app_length.
      replace (X + length Δ' - (length Δ1 + length Δ')) with (X - length Δ1) by lia.
      tauto.
  - split; intros (?&?&?&?&?); eexists _, _; repeat split; eauto;
      match goal with H : _ |- _ => apply H; eauto | H : _ |- _ => apply <- H; eauto end.
  - split; intros [? Happ];
      split; [assumption|intros; eapply Normalizes_mono; [intros|eapply Happ]|
               assumption|intros; eapply Normalizes_mono; [intros|eapply Happ]];
      match goal with H : _ |- _ => apply H; eauto | H : _ |- _ => apply <- H; eauto end.
  - split; intros [? Htapp].
    + split; [assumption|].
      intros ?. eapply Normalizes_mono; [|eapply Htapp; fail].
      intros ? ?.
      apply (IHτ (_ :: _)); eassumption.
    + split; [assumption|].
      intros ?.
      eapply Normalizes_mono; [|eapply Htapp; fail].
      intros w Hw.
      eapply (IHτ (_ :: _)) in Hw; eauto.
Qed.

Lemma val_rel_weaken Δ1 Δ2 τ v :
  val_rel Δ2 τ v ↔ val_rel (Δ1 ++ Δ2) τ.[ren (+length Δ1)] v.
Proof.
  rewrite (val_rel_weaken_gen nil Δ1 Δ2); simpl.
  rewrite weaken_0; asimpl; tauto.
Qed.

Lemma env_rel_weaken Δ1 Δ' Δ2 Γ env :
  env_rel (val_rel (Δ1 ++ Δ2)) Γ env ↔
    env_rel (val_rel (Δ1 ++ Δ' ++ Δ2)) (map (weaken (length Δ1) (length Δ')) Γ) env.
Proof.
  revert env.
  induction Γ as [|τ Γ IHΓ]; intros env.
  - split.
    + intros ->%env_rel_inv_nil_l; apply env_rel_nil.
    + intros ->%env_rel_inv_nil_l; apply env_rel_nil.
  - split; simpl.
    + intros (?&?&->&?&?)%env_rel_inv_cons_l.
      apply env_rel_cons; [|apply IHΓ; eauto; fail].
      apply val_rel_weaken_gen; auto.
    + intros (?&?&->&?&?)%env_rel_inv_cons_l.
      apply env_rel_cons; [|apply IHΓ; eauto; fail].
      apply <- val_rel_weaken_gen; eauto.
Qed.

Lemma env_rel_weaken1 P Δ Γ env :
  env_rel (val_rel Δ) Γ env → env_rel (val_rel (P :: Δ)) (map (rename (+1)) Γ) env.
Proof. rewrite (env_rel_weaken (nil) (cons P nil) Δ); simpl; rewrite weaken_0; trivial. Qed.

Lemma val_rel_subst_gen Δ1 τ' Δ2 τ v :
  val_rel (Δ1 ++ (val_rel Δ2 τ') :: Δ2) τ v ↔ val_rel (Δ1 ++ Δ2) τ.[upn (length Δ1) (τ'.: ids)] v.
Proof.
  revert Δ1 Δ2 v.
  induction τ as [| X | | |]; intros Δ1 Δ2 v.
  - simpl; tauto.
  - asimpl.
    rewrite upn_ext.
    destruct Nat.ltb eqn:Hlt.
    + apply PeanoNat.Nat.ltb_lt in Hlt.
      simpl; unfold rel_in_env; simpl.
      repeat (rewrite lookup_app_l; [|assumption]); tauto.
    + apply PeanoNat.Nat.ltb_ge in Hlt.
      destruct (PeanoNat.Nat.eq_dec X (length Δ1)) as [->|].
      * rewrite PeanoNat.Nat.sub_diag; asimpl.
        unfold rel_in_env.
        rewrite lookup_app_r; [|lia].
        rewrite PeanoNat.Nat.sub_diag; simpl.
        rewrite <- val_rel_weaken; intuition; eauto using val_rel_is_val.
      * simpl; unfold rel_in_env; simpl.
        rewrite lookup_app_r; [|lia].
        destruct (X - length Δ1) as [|z] eqn:Heq; [lia|].
        simpl; unfold rel_in_env; simpl.
        rewrite lookup_app_r; [|lia].
        replace (length Δ1 + z - length Δ1) with z by lia.
        tauto.
  - split; intros (?&?&?&?&?); eexists _, _; repeat split; eauto;
      match goal with H : _ |- _ => apply H; eauto | H : _ |- _ => apply <- H; eauto end.
  - split; intros [? Happ];
      split; [assumption|intros; eapply Normalizes_mono; [intros|eapply Happ]|
               assumption|intros; eapply Normalizes_mono; [intros|eapply Happ]];
      match goal with H : _ |- _ => apply H; eauto | H : _ |- _ => apply <- H; eauto end.
  - split; intros [? Htapp].
    + split; [assumption|].
      intros ?. eapply Normalizes_mono; [|eapply Htapp; fail].
      intros ? ?.
      apply (IHτ (_ :: _)); eassumption.
    + split; [assumption|].
      intros ?.
      eapply Normalizes_mono; [|eapply Htapp; fail].
      intros w Hw.
      eapply (IHτ (_ :: _)) in Hw; eauto.
Qed.

Lemma val_rel_subst τ' Δ τ v : val_rel (val_rel Δ τ' :: Δ) τ v ↔ val_rel Δ τ.[τ'/] v.
Proof. apply (val_rel_subst_gen nil). Qed.

Theorem Fundamental Γ e τ :
  typed Γ e τ → ∀ Δ env, env_rel (val_rel Δ) Γ env → expr_rel Δ τ e.[env_subst env].
Proof.
  intros Htp.
  induction Htp; intros Δ env Henv; simpl.
  - simpl.
    assert (val_rel Δ τ (env_subst env v)).
    { eapply env_rel_lookup1 in Henv as [? [? ?]]; [|eauto; fail].
      erewrite env_subst_lookup; eauto. }
    apply Normalizes_val; [eapply val_rel_is_val; eauto|assumption].
  - apply Normalizes_val; [constructor|simpl; trivial].
  - eapply (Normalizes_bind _ _ _ (λ e, Pair e _));
      [repeat econstructor; fail|apply IHHtp1; eassumption; fail|].
    intros v1 Hv11 Hv12.
    eapply (Normalizes_bind _ _ _ (λ e, Pair _ e)); [|apply IHHtp2; eassumption; fail|].
    { repeat econstructor; trivial. }
    intros v2 Hv21 Hv22.
    apply Normalizes_val; [constructor; trivial; fail|eexists _, _; eauto].
  - eapply (Normalizes_bind _ _ _ (λ e, Fst e));
      [repeat econstructor; fail|apply IHHtp; eassumption; fail|].
    intros v Hv1 (v1 & v2 & -> & Hv1r & Hv2r).
    inversion Hv1; subst.
    eapply Normalizes_head_step_back; [solve_det_head_step|].
    apply Normalizes_val; assumption.
  - eapply (Normalizes_bind _ _ _ (λ e, Snd e));
      [repeat econstructor; fail|apply IHHtp; eassumption; fail|].
    intros v Hv1 (v1 & v2 & -> & Hv1r & Hv2r).
    inversion Hv1; subst.
    eapply Normalizes_head_step_back; [solve_det_head_step|].
    apply Normalizes_val; assumption.
  - apply Normalizes_val; [constructor; fail|].
    split; [constructor; fail|].
    intros w Hw.
    assert (is_val w) by (eapply val_rel_is_val; eauto).
    eapply Normalizes_head_step_back; [solve_det_head_step|].
    asimpl.
    apply (IHHtp Δ (_ :: _)).
    apply env_rel_cons; assumption.
  - eapply (Normalizes_bind _ _ _ (λ e, App e _));
      [repeat econstructor; fail|apply IHHtp1; eassumption; fail|].
    intros v1 Hv11 Hv12.
    eapply (Normalizes_bind _ _ _ (λ e, App _ e)); [|apply IHHtp2; eassumption; fail|].
    { repeat econstructor; trivial. }
    intros v2 Hv21 Hv22.
    apply Hv12; trivial.
  - apply Normalizes_val; [constructor; fail|].
    split; [constructor; fail|].
    intros P.
    eapply Normalizes_head_step_back; [solve_det_head_step|].
    apply IHHtp.
    apply env_rel_weaken1; trivial.
  - eapply (Normalizes_bind _ _ _ (λ e, TApp e));
      [repeat econstructor; fail|apply IHHtp; eassumption; fail|].
    intros v ? [? Hv].
    eapply Normalizes_mono; [|apply Hv; fail].
    intros ? ?; rewrite <- val_rel_subst; eassumption.
Qed.

Corollary type_safety e τ : typed nil e τ → Normalizes (λ _, True) e.
Proof.
  intros Htp.
  eapply Normalizes_mono; [tauto|].
  replace e with e.[env_subst nil] by (asimpl; reflexivity).
  eapply (Fundamental nil _ _ Htp nil); apply env_rel_nil.
Qed.
