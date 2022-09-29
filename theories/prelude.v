From Coq.Unicode Require Import Utf8.
From Coq.Lists Require Import List.
From Autosubst Require Import Autosubst.
From Coq.Relations Require Import Relations.

Section autosubst.
  Context {expr} `{!Ids expr, !Rename expr, !Subst expr, !SubstLemmas expr}.

  Definition environment := list expr.

  Definition lookup (env : environment) (x : var) : option expr := nth_error env x.

  Lemma lookup_nil x : lookup nil x = None.
  Proof. destruct x; trivial. Qed.

  Lemma lookup_Some env x : (∃ e, lookup env x = Some e) ↔ x < length env.
  Proof.
    unfold lookup; split.
    - intros [e He].
      apply nth_error_Some; rewrite He; congruence.
    - intros Hxenv; rewrite nth_error_nth' with (d := ids 0); [eauto|assumption].
  Qed.

  Fixpoint env_subst (env : environment) : var → expr :=
    match env with
    | nil => ids
    | cons g env' => g .: env_subst env'
    end.

  Lemma env_subst_lookup env x e : lookup env x = Some e → env_subst env x = e.
  Proof.
    revert e x.
    induction env as [|g env IHenv]; intros e x Hxe.
    - rewrite lookup_nil in Hxe; congruence.
    - destruct x; simpl in *; [congruence|auto; fail].
  Qed.

End autosubst.

Arguments environment expr: clear implicits.

Section env_rel.
  Context {A B} (P : A → B → Prop).

  Definition env_rel (env1 : environment A) (env2 : environment B) : Prop := Forall2 P env1 env2.

  Lemma env_rel_lookup1 env1 env2 x a :
    env_rel env1 env2 → lookup env1 x = Some a → ∃ b, lookup env2 x = Some b ∧ P a b.
  Proof.
    intros Her.
    revert x a.
    induction Her.
    - intros ??; rewrite lookup_nil; congruence.
    - intros z a.
      destruct z; simpl; [|eauto; fail].
      simplify_eq 1; intros ?; subst; eauto.
  Qed.

  Lemma env_rel_lookup2 env1 env2 x b :
    env_rel env1 env2 → lookup env2 x = Some b → ∃ a, lookup env1 x = Some a ∧ P a b.
  Proof.
    intros Her.
    revert x b.
    induction Her.
    - intros ??; rewrite lookup_nil; congruence.
    - intros z b.
      destruct z; simpl; [|eauto; fail].
      simplify_eq 1; intros ?; subst; eauto.
  Qed.

  Lemma env_rel_nil : env_rel nil nil.
  Proof. apply Forall2_nil. Qed.

  Lemma env_rel_cons a env b env' : P a b → env_rel env env' → env_rel (a :: env) (b :: env').
  Proof. apply Forall2_cons; trivial. Qed.

End env_rel.

Class valid_language {expr : Type}
    (is_val : expr → Prop)
    (is_ectx : (expr → expr) → Prop)
    (head_step : expr → expr → Prop) : Type :=
ValidLang {
  is_val_no_head_step : ∀ v, is_val v → ∀ e', ¬ head_step v e';
  is_val_under_ectx : ∀ e K , is_ectx K → is_val (K e) → is_val e;
  is_ectx_id : is_ectx (λ e, e);
  is_val_dec : ∀ e, is_val e ∨ ¬ is_val e;
  ectx_head_step : ∀ K e e', is_ectx K → head_step (K e) e' → (∀ f, K f = f) ∨ is_val e;
  ectx_inj : ∀ K e e', is_ectx K → K e = K e' → e = e';
  ectx_compose : ∀ K K', is_ectx K → is_ectx K' → is_ectx (λ e, K (K' e));
  ectxs_nesting : ∀ K e K' e',
      is_ectx K →
      is_ectx K' →
      K e = K' e' →
      ¬ is_val e →
      ¬ is_val e' →
      (∃ K'', is_ectx K'' ∧ ∀ f, K f = K' (K'' f)) ∨ (∃ K'', is_ectx K'' ∧ ∀ f, K' f = K (K'' f))
}.

Inductive step {expr is_val is_ectx head_step} `{@valid_language expr is_val is_ectx head_step} :
  expr → expr → Prop :=
| Step K e1 e2 : is_ectx K → head_step e1 e2 → step (K e1) (K e2).

Definition steps {expr is_val is_ectx head_step} `{@valid_language expr is_val is_ectx head_step} :=
  clos_refl_trans _ step.

Definition det_head_step
  {expr is_val is_ectx head_step} `{@valid_language expr is_val is_ectx head_step} e e' :=
  head_step e e' ∧ ∀ e'', head_step e e'' → e'' = e'.

Definition det_step
  {expr is_val is_ectx head_step} `{@valid_language expr is_val is_ectx head_step} e e' :=
  step e e' ∧ ∀ e'', step e e'' → e'' = e'.

Section language.
  Context {expr is_val is_ectx head_step} `{@valid_language expr is_val is_ectx head_step}.

  Lemma steps_ind (P : expr → expr → Prop) :
    (∀ e, P e e) →
    (∀ e e' e'', step e e' → steps e' e'' → P e' e'' → P e e'') →
    ∀ e e', steps e e' → P e e'.
  Proof.
    intros Hrfl Hstp e e' Hsteps.
    apply clos_rt_rt1n_iff in Hsteps.
    induction Hsteps; [apply Hrfl|].
    eapply Hstp; [eassumption|apply clos_rt_rt1n_iff; assumption|assumption].
  Qed.

  Lemma val_no_step e : is_val e → ∀ e', ¬ step e e'.
  Proof.
    intros He e' Hstp.
    inversion Hstp as [K e1 e2 HK Hhs]; subst; clear Hstp.
    apply is_val_under_ectx in He; [|assumption].
    eapply is_val_no_head_step; eauto.
  Qed.

  Lemma val_steps_eq e e' : is_val e → steps e e' → e = e'.
  Proof.
    induction 2 as [| |???? IH1 ? IH2]; subst; [|trivial; fail|].
    - exfalso; eapply val_no_step; eauto.
    - assert (x = y) by (apply IH1; trivial); subst.
      apply IH2; trivial.
  Qed.

  Lemma head_step_step e e' : head_step e e' → step e e'.
  Proof. intros; eapply (Step (λ e, e)); [apply is_ectx_id|assumption]. Qed.

  Lemma ectx_step e e' K : is_ectx K → step e e' → step (K e) (K e').
  Proof.
    intros ?; inversion 1 as [K' e1 e2]; subst.
    eapply (Step (λ e, K (K' e))); [apply ectx_compose; assumption|assumption].
  Qed.

  Lemma steps_eq_or_step_iff e e' : steps e e' ↔ e = e' ∨ ∃ e'', step e e'' ∧ steps e'' e'.
  Proof.
    split.
    - intros Hsteps; apply clos_rt_rt1n_iff in Hsteps.
      inversion Hsteps as [|??? Hsteps']; [eauto; fail|].
      apply clos_rt_rt1n_iff in Hsteps'; eauto.
    - intros [->|[? [? ?]]]; apply clos_rt_rt1n_iff;
        [constructor; fail|econstructor; [|apply clos_rt_rt1n_iff]]; eauto.
  Qed.

  Lemma step_under_ectx K e e' :
    is_ectx K → step (K e) e' →
    (is_val e) ∨ (∃ e'', step e e'' ∧ e' = K e'').
  Proof.
    intros HK Hstp.
    destruct (is_val_dec e) as [Hiv|Hniv].
    - auto.
    - right.
      inversion Hstp as [K' e1 e2 HK' Hhs HKe1e]; subst.
      destruct (ectxs_nesting _ _ _ _ HK' HK HKe1e) as [[K'' [HK''1 HK''2]]|[K'' [HK''1 HK''2]]];
      [intros ?; contradict Hhs; apply is_val_no_head_step; assumption|assumption| |].
      + rewrite HK''2 in HKe1e.
        apply ectx_inj in HKe1e; [|assumption].
        subst.
        exists (K'' e2); rewrite HK''2; split; [|reflexivity].
        constructor; trivial.
      + rewrite HK''2 in HKe1e.
        apply ectx_inj in HKe1e; [|assumption].
        subst.
        pose proof Hhs as Hhs'.
        apply ectx_head_step in Hhs as [Hhs|Hhs]; [|tauto|assumption].
        rewrite Hhs in Hhs'.
        exists e2; split; [apply head_step_step; assumption|].
        rewrite HK''2, Hhs; trivial.
  Qed.

  Definition Safe (P : expr → Prop) (e : expr) :=
    ∀ e', steps e e' → (is_val e' ∧ P e') ∨ ∃ e'', step e' e''.

  Lemma Safe_mono (P Q : expr → Prop) e : (∀ v, P v → Q v) → Safe P e → Safe Q e.
  Proof. unfold Safe; firstorder. Qed.

  Lemma Safe_val (P : expr → Prop) e : is_val e → P e → Safe P e.
  Proof.
    unfold Safe; intros He HPe e' Hstp.
    left.
    apply val_steps_eq in Hstp; subst; auto.
  Qed.

  Lemma Safe_val_inv (P : expr → Prop) e : is_val e → Safe P e → P e.
  Proof.
    unfold Safe; intros He HSf.
    destruct (HSf e) as [|[e' He']]; [apply steps_eq_or_step_iff; eauto; fail|tauto|].
    contradict He'; apply val_no_step; trivial.
  Qed.

  Lemma Safe_step (P : expr → Prop) e e' : step e e' → Safe P e → Safe P e'.
  Proof.
    intros Hstep HSf ei Hsteps.
    apply HSf.
    apply steps_eq_or_step_iff; eauto.
  Qed.

  Lemma det_head_step_det_step e e' : det_head_step e e' → det_step e e'.
  Proof.
    intros [Hhs Hdt]; split; [apply head_step_step; assumption|].
    intros e'' Hstp.
    inversion Hstp as [? ? ? ? Hhs']; subst.
    apply ectx_head_step in Hhs as [Hid|Hvl]; [| |assumption].
    - rewrite Hid; rewrite Hid in Hdt. apply Hdt; assumption.
    - contradict Hhs'; apply is_val_no_head_step; trivial.
  Qed.

  Lemma Safe_det_step_back (P : expr → Prop) e e' : det_step e e' → Safe P e' → Safe P e.
  Proof.
    intros Hdstep HSf ei Hsteps.
    apply steps_eq_or_step_iff in Hsteps as [->|(e'' & He''1 & He''2)].
    - right; eexists; apply Hdstep.
    - apply Hdstep in He''1; subst.
      apply HSf; assumption.
  Qed.

  Lemma Safe_head_step_back (P : expr → Prop) e e' : det_head_step e e' → Safe P e' → Safe P e.
  Proof.
    intros.
    eapply Safe_det_step_back; [apply det_head_step_det_step|]; eassumption.
  Qed.

  Lemma Safe_bind (P Q : expr → Prop) e K :
    is_ectx K → Safe P e → (∀ v, is_val v → P v → Safe Q (K v)) → Safe Q (K e).
  Proof.
    intros HK He HKSf e' Hstps.
    remember (K e) as Ke.
    revert e HeqKe He.
    pattern Ke; pattern e'.
    match goal with
    | |- (λ e2, (λ e1, ?P) _) _ => simpl; apply (steps_ind (λ e1 e2, P))
    end; [| |assumption]; clear e' Ke Hstps.
    - intros ? e ? He; subst.
      destruct (is_val_dec (K e)).
      + assert (is_val e) by (eapply is_val_under_ectx; eauto).
        eapply (HKSf e);
          [assumption|eapply Safe_val_inv; assumption| apply steps_eq_or_step_iff; auto].
      + destruct (is_val_dec e).
        * eapply (HKSf e);
          [assumption|eapply Safe_val_inv; assumption| apply steps_eq_or_step_iff; auto].
        * destruct (He e) as [|[e' He']]; [apply steps_eq_or_step_iff; auto|tauto|].
          right; eexists; apply ectx_step; eauto.
    - intros e e' e'' Hstp Hstps IHstps ei ? Hei; subst.
      pose proof Hstp as Hvlstp; apply step_under_ectx in Hvlstp as [Hvl|[e3 [He31 He32]]];
        [|subst|assumption].
      + eapply (HKSf ei);
          [assumption|eapply Safe_val_inv; assumption| apply steps_eq_or_step_iff; eauto].
      + eapply IHstps; [reflexivity|].
        eapply Safe_step; eauto.
  Qed.

End language.
