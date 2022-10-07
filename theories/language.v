From Coq.Unicode Require Import Utf8.
From Coq.Lists Require Import List.
From Coq.Relations Require Import Relations.
From Coq.micromega Require Import Lia.

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

Inductive nsteps {expr is_val is_ectx head_step} `{@valid_language expr is_val is_ectx head_step} :
  nat → expr → expr → Prop :=
| NSO e : nsteps 0 e e
| NSS n e1 e2 e3 : step e1 e2 → nsteps n e2 e3 → nsteps (S n) e1 e3.

Definition det_head_step
  {expr is_val is_ectx head_step} `{@valid_language expr is_val is_ectx head_step} e e' :=
  head_step e e' ∧ ∀ e'', head_step e e'' → e'' = e'.

Definition det_step
  {expr is_val is_ectx head_step} `{@valid_language expr is_val is_ectx head_step} e e' :=
  step e e' ∧ ∀ e'', step e e'' → e'' = e'.

Section language.
  Context {expr is_val is_ectx head_step} `{@valid_language expr is_val is_ectx head_step}.

  Lemma nsteps_refl e : nsteps 0 e e.
  Proof. constructor; fail. Qed.

  Lemma step_nsteps e e' : step e e' → nsteps 1 e e'.
  Proof. econstructor; [eassumption|econstructor]. Qed.

  Lemma nsteps_trans n n' e e' e'' : nsteps n e e' → nsteps n' e' e'' → nsteps (n + n') e e''.
  Proof.
    induction 1; [trivial; fail|].
    simpl.
    econstructor; [eassumption|auto].
  Qed.

  Lemma nsteps_take_step n e e' e'' :
    step e e' → nsteps n e' e'' → nsteps (S n) e e''.
  Proof. intros ? ?; eapply (nsteps_trans 1); [apply step_nsteps|]; eauto. Qed.

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

  Lemma steps_refl e : steps e e.
  Proof. constructor; fail. Qed.

  Lemma step_steps e e' : step e e' → steps e e'.
  Proof. constructor; assumption. Qed.

  Lemma steps_trans e e' e'' : steps e e' → steps e' e'' → steps e e''.
  Proof. econstructor; eauto; fail. Qed.

  Lemma steps_nsteps e e' : steps e e' → ∃ n, nsteps n e e'.
  Proof.
    induction 1 as [| |? ? ? ? [n Hn] ? [k Hk]];
      [eexists; eapply step_nsteps; assumption|exists 0; apply nsteps_refl|].
    eexists (_ + _); eapply nsteps_trans; eauto.
  Qed.

  Lemma nsteps_steps n e e' : nsteps n e e' → steps e e'.
  Proof.
    induction 1; [econstructor; fail|eapply steps_trans; [apply step_steps; eassumption|trivial]].
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
    intros Hiv Hstps; revert Hiv.
    pattern e; pattern e'.
    match goal with
    | |- (λ e', (λ e, ?P) _) _ => simpl; apply (steps_ind (λ e e', P))
    end; [| |assumption]; clear e' e Hstps.
    - trivial.
    - intros ???????.
      exfalso; eapply val_no_step; eauto.
  Qed.

  Lemma head_step_step e e' : head_step e e' → step e e'.
  Proof. intros; eapply (Step (λ e, e)); [apply is_ectx_id|assumption]. Qed.

  Lemma ectx_step e e' K : is_ectx K → step e e' → step (K e) (K e').
  Proof.
    intros ?; inversion 1 as [K' e1 e2]; subst.
    eapply (Step (λ e, K (K' e))); [apply ectx_compose; assumption|assumption].
  Qed.

  Lemma ectx_steps e e' K : is_ectx K → steps e e' → steps (K e) (K e').
  Proof.
    intros HK Hstep.
    pattern e; pattern e'.
    match goal with
    | |- (λ e2, (λ e1, ?P) _) _ => simpl; apply (steps_ind (λ e1 e2, P))
    end; [| |assumption]; clear e e' Hstep.
    - intros ?; apply steps_refl.
    - intros e e' e'' Hstep Hsteps HKsteps.
      eapply steps_trans; [apply step_steps, ectx_step|]; eassumption.
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
    destruct (HSf e) as [|[e' He']]; [apply steps_refl|tauto|].
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

  Lemma steps_under_ectx K e e' :
    is_ectx K → steps (K e) e' →
    (∃ e'', e' = K e'' ∧ steps e e'') ∨ ∃ v, is_val v ∧ steps e v ∧ steps (K v) e'.
  Proof.
    intros HK [n Hstps]%steps_nsteps.
    revert e e' HK Hstps.
    induction n; intros e e' HK Hstps.
    - inversion Hstps; subst; left; eexists _; split; [eauto|apply steps_refl].
    - inversion Hstps as [|? ? ex]; subst.
      destruct (step_under_ectx K e ex) as [|(e'' & He''1 & He''2)];
        [assumption|assumption| |subst].
      + right; eexists e; split; [assumption|].
        split; [apply steps_refl|eapply nsteps_steps; eassumption].
      + destruct (IHn e'' e') as [(? & -> &?)|(?&?&?&?)]; [assumption|assumption| |].
        * left; eexists; split; [reflexivity|eapply steps_trans; [apply step_steps|]; eauto].
        * right; eexists _; split; [eassumption|].
          split; [eapply steps_trans; [apply step_steps|]; eauto|assumption].
  Qed.

  Lemma Safe_bind (P Q : expr → Prop) e K :
    is_ectx K → Safe P e → (∀ v, is_val v → P v → Safe Q (K v)) → Safe Q (K e).
  Proof.
    intros HK He HKSf e' Hstps.
    apply steps_under_ectx in Hstps as [(e'' & -> & He'')|(v & Hv & Hv1 & Hv2)]; [| |assumption].
    - apply He in He'' as [[Hie'' HPe'']|[e3 He3]].
      + eapply HKSf; [eassumption|eassumption|apply steps_refl].
      + right; eexists; apply ectx_step; eauto.
    - apply He in Hv1 as [[]|[]]; [|exfalso; eapply val_no_step; eauto; fail].
      eapply HKSf; [eassumption|assumption|assumption].
  Qed.

  Definition Normalizes (P : expr → Prop) (e : expr) := ∃ v, is_val v ∧ steps e v ∧ P v.

  Lemma Normalizes_mono (P Q : expr → Prop) e : (∀ v, P v → Q v) → Normalizes P e → Normalizes Q e.
  Proof. unfold Safe; firstorder. Qed.

  Lemma Normalizes_val (P : expr → Prop) e : is_val e → P e → Normalizes P e.
  Proof.
    intros ? ?; eexists; repeat split; [eassumption|apply steps_refl|eassumption].
  Qed.

  Lemma Normalizses_val_inv (P : expr → Prop) e : is_val e → Normalizes P e → P e.
  Proof.
    intros Hiv (e' & He'1 & He'2 & He'3).
    apply val_steps_eq in He'2; [subst; trivial|assumption].
  Qed.

  Lemma Normalizes_step_back (P : expr → Prop) e e' : step e e' → Normalizes P e' → Normalizes P e.
  Proof.
    intros Hstep (v & Hv1 & Hv2 & Hv3).
    exists v; repeat split; [assumption| |assumption].
    apply steps_eq_or_step_iff; eauto.
  Qed.

  Lemma Normalizes_head_step_back (P : expr → Prop) e e' :
    head_step e e' → Normalizes P e' → Normalizes P e.
  Proof.
    intros Hstep (v & Hv1 & Hv2 & Hv3).
    exists v; repeat split; [assumption| |assumption].
    apply steps_eq_or_step_iff; eauto using head_step_step.
  Qed.

  Lemma Normalizes_det_step (P : expr → Prop) e e' :
    det_step e e' → Normalizes P e → Normalizes P e'.
  Proof.
    intros Hdstep (v & Hv1 & Hv2 & Hv3).
    exists v; repeat split; [assumption| |assumption].
    apply steps_eq_or_step_iff in Hv2 as [->|(e'' & He''1 & He''2)].
    - destruct Hdstep as [Hstp%val_no_step ?]; tauto.
    - pose proof He''1 as ->%Hdstep; assumption.
  Qed.

  Lemma Normalizes_bind (P Q : expr → Prop) e K :
    is_ectx K → Normalizes P e → (∀ v, is_val v → P v → Normalizes Q (K v)) → Normalizes Q (K e).
  Proof.
    intros HK He HKnrm.
    destruct He as (v & Hv1 & Hv2 & Hv3).
    destruct (HKnrm v) as (w & Hw1 & Hw2 & Hw3); [assumption|assumption|].
    exists w; repeat split; [assumption| |assumption].
    eapply steps_trans; [|eassumption].
    apply ectx_steps; assumption.
  Qed.

  Lemma val_nsteps_eq n e e' : is_val e → nsteps n e e' → n = 0 ∧ e = e'.
  Proof.
    inversion 2; subst; [split; reflexivity|].
    exfalso; eapply val_no_step; eauto.
  Qed.

  Lemma nsteps_eq_or_step_iff n e e' :
    nsteps n e e' ↔ (n = 0 ∧ e = e') ∨ ∃ n' e'', n = S n' ∧ step e e'' ∧ nsteps n' e'' e'.
  Proof.
    split.
    - intros Hsteps.
      inversion Hsteps; subst.
      + left; auto.
      + right; eexists _, _; split; [reflexivity|]; split; [eassumption|eassumption].
    - intros [[-> ->]|(?&?&->&?&?)]; [constructor|econstructor; eauto].
  Qed.

  Lemma ectx_nsteps n e e' K : is_ectx K → nsteps n e e' → nsteps n (K e) (K e').
  Proof. induction 2; econstructor; eauto using ectx_step. Qed.

  Definition SISafe (P : nat → expr → Prop) (n : nat) (e : expr) :=
    ∀ k e', k ≤ n → nsteps k e e' → (is_val e' ∧ P (n - k) e') ∨ ∃ e'', step e' e''.

  Lemma SISafe_mono (P Q : nat → expr → Prop) n e :
    (∀ n' v, n' ≤ n → P n' v → Q n' v) → SISafe P n e → SISafe Q n e.
  Proof.
    intros HPQ HSf ??? Hstps.
    apply HSf in Hstps as [?|?]; [|auto; fail|lia].
    left; split; [tauto|apply HPQ; [lia|tauto]].
  Qed.

  Lemma SISafe_val (P : nat → expr → Prop) n e : is_val e → P n e → SISafe P n e.
  Proof.
    intros He HPe k e' Hk Hstp.
    left.
    apply val_nsteps_eq in Hstp as [? ?]; subst; [|assumption].
    replace (n - 0) with n by lia; auto.
  Qed.

  Lemma SISafe_val_inv (P : nat → expr → Prop) n e : is_val e → SISafe P n e → P n e.
  Proof.
    unfold Safe; intros He HSf.
    destruct (HSf 0 e) as [[Hiv HP]|[e' He']]; [lia|apply nsteps_refl| |].
    - replace (n - 0) with n in HP by lia; trivial.
    - contradict He'; apply val_no_step; trivial.
  Qed.

  Lemma SISafe_step (P : nat → expr → Prop) e e' n :
    step e e' → SISafe P (S n) e → SISafe P n e'.
  Proof.
    intros Hstep HSf k ei Hk Hsteps.
    apply (HSf (S k)); [lia|].
    econstructor; eauto.
  Qed.

  Lemma SISafe_det_step_back (P : nat → expr → Prop) e e' n :
    det_step e e' → (0 < n → SISafe P (n - 1) e') → SISafe P n e.
  Proof.
    intros Hdstep HSf k ei Hk Hsteps.
    apply nsteps_eq_or_step_iff in Hsteps as [[-> ->]|(m & e'' & -> & He''1 & He''2)].
    - right; eexists; apply Hdstep.
    - apply Hdstep in He''1; subst.
      destruct n as [|n]; [lia|].
      pose proof (λ H, HSf H m ei) as HSf'. simpl in *.
      replace (n - 0) with n in HSf' by lia.
      apply HSf'; [lia|lia|assumption].
  Qed.

  Lemma SISafe_head_step_back (P : nat → expr → Prop) e e' n :
    det_head_step e e' → (0 < n → SISafe P (n - 1) e') → SISafe P n e.
  Proof.
    intros.
    eapply SISafe_det_step_back; [apply det_head_step_det_step|]; eassumption.
  Qed.

  Lemma nsteps_under_ectx n K e e' :
    is_ectx K → nsteps n (K e) e' →
    (∃ e'', e' = K e'' ∧ nsteps n e e'') ∨
      ∃ k v, k ≤ n ∧ is_val v ∧ nsteps k e v ∧ nsteps (n - k) (K v) e'.
  Proof.
    revert e e'.
    induction n; intros e e' HK Hstps.
    - inversion Hstps; subst; left; eexists _; split; [eauto|econstructor].
    - inversion Hstps as [|? ? ex]; subst.
      destruct (step_under_ectx K e ex) as [|(e'' & He''1 & He''2)];
        [assumption|assumption| |subst].
      + right; eexists 0, e; split; [lia|split]; [assumption|].
        split; [econstructor|].
        rewrite PeanoNat.Nat.sub_0_r; trivial.
      + destruct (IHn e'' e') as [(? & -> &?)|(?&?&?&?&?&?)]; [assumption|assumption| |].
        * left; eexists; split; [reflexivity|econstructor; eauto].
        * right; eexists (S _), _; repeat split; [|eassumption| |eassumption]; [lia|].
          econstructor; eauto.
  Qed.

  Lemma SISafe_bind (P Q : nat → expr → Prop) e K n :
    is_ectx K →
    SISafe P n e →
    (∀ k v, k ≤ n → is_val v → P k v → SISafe Q k (K v)) →
    SISafe Q n (K e).
  Proof.
    intros HK He HKSf k e' Hk Hstps.
    apply nsteps_under_ectx in Hstps as [(e'' & -> & He'')|(m & ? & v & Hv & Hv1 & Hv2)];
      [| |assumption].
    - apply He in He'' as [[Hie'' HPe'']|[e3 He3]]; [| |lia].
      + apply HKSf in HPe''; [|lia|assumption].
        pose proof (HPe'' 0) as HPe3.
        replace (n - k - 0) with (n - k) in HPe3 by lia.
        apply HPe3; [lia|]; apply nsteps_refl.
      + right; eexists; apply ectx_step; eauto.
    - apply He in Hv1 as [[? HPkv]|[]]; [|exfalso; eapply val_no_step; eauto; fail|lia].
      apply HKSf in HPkv; [|lia|assumption].
      specialize (HPkv (k - m) e'); simpl in *.
      replace (n - m - (k - m)) with (n - k) in HPkv by lia.
      apply HPkv; [lia |assumption].
  Qed.

  Lemma SISafe_adequacy P e : (∀ n, SISafe (λ _ v, P v) n e) → Safe P e.
  Proof.
    intros HSI e' [n Hstps]%steps_nsteps.
    eapply (HSI n); [|eassumption]; lia.
  Qed.

End language.
