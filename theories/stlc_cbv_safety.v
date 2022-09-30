From Coq.Unicode Require Import Utf8.
From Coq.Lists Require Import List.
From Autosubst Require Import Autosubst.
From Coq.Relations Require Import Relations.
From ShortLogrels Require Import prelude language stlc_cbv.

Fixpoint val_rel (τ : type) (v : expr) : Prop :=
  match τ with
  | TUnit => v = TT
  | TProd τ1 τ2 => ∃ v1 v2, v = Pair v1 v2 ∧ val_rel τ1 v1 ∧ val_rel τ2 v2
  | TFun τ1 τ2 => is_val v ∧ ∀ w, val_rel τ1 w → Safe (val_rel τ2) (App v w)
  end.

Lemma val_rel_is_val τ v : val_rel τ v → is_val v.
Proof.
  revert v; induction τ; intros v; simpl in *; subst.
  - intros ?; subst; constructor.
  - firstorder; subst; constructor; auto.
  - intuition.
Qed.

Definition expr_rel (τ : type) (e : expr) := Safe (val_rel τ) e.

Theorem Fundamental Γ e τ :
  typed Γ e τ → ∀ env, env_rel val_rel Γ env → expr_rel τ e.[env_subst env].
Proof.
  intros Htp.
  induction Htp; intros env Henv; simpl.
  - simpl.
    assert (val_rel tp (env_subst env v)).
    { eapply env_rel_lookup1 in Henv as [? [? ?]]; [|eauto; fail].
      erewrite env_subst_lookup; eauto. }
    apply Safe_val; [eapply val_rel_is_val; eauto|assumption].
  - apply Safe_val; [constructor|simpl; trivial].
  - eapply (Safe_bind _ _ _ (λ e, Pair e _));
      [repeat econstructor; fail|apply IHHtp1; trivial; fail|].
    intros v1 Hv11 Hv12.
    eapply (Safe_bind _ _ _ (λ e, Pair _ e)); [|apply IHHtp2; trivial; fail|].
    { repeat econstructor; trivial. }
    intros v2 Hv21 Hv22.
    apply Safe_val; [constructor; trivial; fail|eexists _, _; eauto].
  - eapply (Safe_bind _ _ _ (λ e, Fst e));
      [repeat econstructor; fail|apply IHHtp; trivial; fail|].
    intros v Hv1 (v1 & v2 & -> & Hv1r & Hv2r).
    inversion Hv1; subst.
    eapply Safe_head_step_back; [solve_det_head_step|].
    apply Safe_val; assumption.
  - eapply (Safe_bind _ _ _ (λ e, Snd e));
      [repeat econstructor; fail|apply IHHtp; trivial; fail|].
    intros v Hv1 (v1 & v2 & -> & Hv1r & Hv2r).
    inversion Hv1; subst.
    eapply Safe_head_step_back; [solve_det_head_step|].
    apply Safe_val; assumption.
  - apply Safe_val; [constructor; fail|].
    split; [constructor; fail|].
    intros w Hw.
    assert (is_val w) by (eapply val_rel_is_val; eauto).
    eapply Safe_head_step_back; [solve_det_head_step|].
    asimpl.
    apply (IHHtp (_ :: _)).
    apply env_rel_cons; assumption.
  - eapply (Safe_bind _ _ _ (λ e, App e _));
      [repeat econstructor; fail|apply IHHtp1; trivial; fail|].
    intros v1 Hv11 Hv12.
    eapply (Safe_bind _ _ _ (λ e, App _ e)); [|apply IHHtp2; trivial; fail|].
    { repeat econstructor; trivial. }
    intros v2 Hv21 Hv22.
    apply Hv12; trivial.
Qed.

Corollary type_safety e τ : typed nil e τ → Safe (λ _, True) e.
Proof.
  intros Htp.
  eapply Safe_mono; [tauto|].
  replace e with e.[env_subst nil] by (asimpl; reflexivity).
  eapply (Fundamental nil); [eassumption|apply env_rel_nil].
Qed.
