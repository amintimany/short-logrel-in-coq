From Coq.Unicode Require Import Utf8.
From Coq.Lists Require Import List.
From Autosubst Require Import Autosubst.
From Coq.Relations Require Import Relations.
From Coq.micromega Require Import Lia.
From ShortLogrels Require Import prelude language systemF_rec_cbv.

Local Obligation Tactic := idtac.

Record SIPred :=
{ sipred :> nat → expr → Prop;
  sipred_over_val : ∀ n e, sipred n e → is_val e;
  sipred_down_closed : ∀ n n' e, n' ≤ n → sipred n e → sipred n' e }.

Local Hint Resolve sipred_over_val : core.

Definition expr_rel (P : SIPred) := SISafe P.

Lemma expr_rel_down_closed P n n' e : n' ≤ n → expr_rel P n e → expr_rel P n' e.
Proof.
  intros ? Hn ??? Hstps.
  apply Hn in Hstps as [[]|]; [|right; assumption|lia].
  left; split; [assumption|].
  eapply sipred_down_closed; [|eassumption]; lia.
Qed.

Program Definition SIPred_true : SIPred := {| sipred _ e := is_val e |}.
Next Obligation. trivial. Qed.
Next Obligation. trivial. Qed.

Definition SIPred_dist (P1 P2 : SIPred) (n : nat) : Prop := ∀ k e, k < n → P1 k e ↔ P2 k e.

Lemma SIPred_dist_0 P1 P2 : SIPred_dist P1 P2 0.
Proof. intros ???; lia. Qed.
Lemma SIPred_dist_le P1 P2 n m : n ≤ m → SIPred_dist P1 P2 m → SIPred_dist P1 P2 n.
Proof. intros ? Hm ? ? ?; eapply Hm; lia. Qed.
Lemma SIPred_dist_refl P n: SIPred_dist P P n.
Proof. unfold SIPred_dist; tauto. Qed.
Lemma SIPred_dist_sym P1 P2 n: SIPred_dist P1 P2 n → SIPred_dist P2 P1 n.
Proof. unfold SIPred_dist; firstorder. Qed.
Lemma SIPred_dist_trans P1 P2 P3 n: SIPred_dist P1 P2 n → SIPred_dist P2 P3 n → SIPred_dist P1 P3 n.
Proof. intros H12 H23; split; intros ?; [apply H23; [|apply H12]|apply H12; [|apply H23]]; auto. Qed.

Definition NonExpansive (Ψ : SIPred → SIPred) : Prop :=
  ∀ P1 P2 n, SIPred_dist P1 P2 n → SIPred_dist (Ψ P1) (Ψ P2) n.

Definition NonExpansive2 (Ψ : SIPred → SIPred → SIPred) : Prop :=
  ∀ P11 P12 P21 P22 n,
    SIPred_dist P11 P12 n → SIPred_dist P21 P22 n → SIPred_dist (Ψ P11 P12) (Ψ P21 P22) n.

Definition Contractive (Ψ : SIPred → SIPred) : Prop :=
  ∀ P1 P2 n, SIPred_dist P1 P2 n → SIPred_dist (Ψ P1) (Ψ P2) (S n).

Program Definition later (P : SIPred) : SIPred :=
  {| sipred n e := match n return Prop with 0 => is_val e | S n' => P n' e end |}.
Next Obligation. simpl; intros ?[]??; [assumption|eapply sipred_over_val; eauto]. Qed.
Next Obligation.
  simpl.
  intros P n n' e Hle ?.
  destruct n; destruct n'; [assumption|lia| |].
  - eapply sipred_over_val; eauto.
  - eapply sipred_down_closed; [|eassumption]; lia.
Qed.

Lemma later_0 P e : later P 0 e ↔ is_val e.
Proof. simpl; tauto. Qed.
Lemma later_S P n e : later P (S n) e ↔ P n e.
Proof. simpl; tauto. Qed.
Lemma later_contractive : Contractive later.
Proof. intros ??? Hltr [] ??; simpl; [tauto|apply Hltr; lia]. Qed.

Opaque later.

Lemma Contractive_NonExpansive Ψ : Contractive Ψ → NonExpansive Ψ.
Proof. intros Hcn ???????; eapply Hcn; [eassumption|]; lia. Qed.

Fixpoint iter (Ψ : SIPred → SIPred) (n : nat) : SIPred :=
  match n with | 0 => SIPred_true | S n' => Ψ (iter Ψ n') end.

Lemma iter_dist Ψ (HΨ : Contractive Ψ) n m : n ≤ m → SIPred_dist (iter Ψ m) (iter Ψ n) n.
Proof.
  revert n; induction m as [|m IHm]; intros n Hnm.
  - replace n with 0 by lia. apply SIPred_dist_refl.
  - destruct n as [|n].
    + apply SIPred_dist_0.
    + simpl. apply HΨ.
      apply IHm; lia.
Qed.

Program Definition fixpoint (Ψ : SIPred → SIPred) (HΨ : Contractive Ψ) : SIPred :=
  {| sipred n v := iter Ψ (S n) n v |}.
Next Obligation. simpl; intros; eapply sipred_over_val; eauto. Qed.
Next Obligation.
  simpl.
  intros Ψ HΨ n; induction n as [|n IHn]; intros n' e Hle Hn.
  - replace n' with 0 by lia. trivial.
  - assert (SIPred_dist (Ψ (iter Ψ (S n))) (Ψ (iter Ψ n')) (S n')) as Hhlp.
    { apply HΨ. apply iter_dist; [assumption|lia]. }
    apply Hhlp; [lia|].
    apply (sipred_down_closed _ (S n)); [lia|trivial].
Qed.

Lemma Ψ_fixpoint (Ψ : SIPred → SIPred) (HΨ : Contractive Ψ) n e :
  Ψ (fixpoint Ψ HΨ) n e ↔ Ψ (Ψ (iter Ψ n)) n e.
Proof.
  eapply (HΨ _ _ n); [|lia].
  clear e; intros k e' Hlt; simpl.
  eapply (HΨ _ _ k); [|lia].
  apply SIPred_dist_sym; apply iter_dist; [assumption|lia].
Qed.

Lemma fixpoint_dist (Ψ : SIPred → SIPred) (HΨ : Contractive Ψ) n :
  SIPred_dist (fixpoint Ψ HΨ) (Ψ (fixpoint Ψ HΨ)) n.
Proof.
  intros k e Hlt.
  rewrite Ψ_fixpoint; simpl.
  eapply (HΨ _ _ k); [|lia].
  clear n e Hlt.
  induction k as [|k IHn].
  - apply SIPred_dist_0.
  - intros n e Hlt.
    simpl.
    eapply (HΨ _ _ k); [|assumption].
    trivial.
Qed.

Lemma fixpoint_unfold (Ψ : SIPred → SIPred) (HΨ : Contractive Ψ) n e :
  fixpoint Ψ HΨ n e ↔ Ψ (fixpoint Ψ HΨ) n e.
Proof. eapply (fixpoint_dist _ _ (S n)); lia. Qed.

Lemma fixpoint_ne (Ψ Φ : SIPred → SIPred) (HΨ : Contractive Ψ) (HΦ : Contractive Φ) n :
  (∀ P, SIPred_dist (Ψ P) (Φ P) n) → SIPred_dist (fixpoint Ψ HΨ) (fixpoint Φ HΦ) n.
Proof.
  intros HΨΦ.
  induction n as [|n IHn].
  - apply SIPred_dist_0.
  - eapply SIPred_dist_trans; [apply fixpoint_dist|].
    eapply SIPred_dist_trans; [|apply SIPred_dist_sym; apply fixpoint_dist].
    eapply SIPred_dist_trans; [apply HΨΦ|].
    apply (HΦ _ _ n).
    apply IHn.
    intros.
    eapply SIPred_dist_le; [|apply HΨΦ]; lia.
Qed.

Opaque fixpoint.

Definition SIEnv := environment SIPred.

Definition SIEnv_dist (Δ1 Δ2 : SIEnv) (n : nat) : Prop :=
  env_rel (λ P1 P2, SIPred_dist P1 P2 n) Δ1 Δ2.

Lemma SIEnv_dist_le Δ1 Δ2 n m : n ≤ m → SIEnv_dist Δ1 Δ2 m → SIEnv_dist Δ1 Δ2 n.
Proof. intros ?; apply env_rel_impl; intros ? ?; eapply SIPred_dist_le; trivial. Qed.
Lemma SIEnv_dist_refl Δ n: SIEnv_dist Δ Δ n.
Proof. apply env_rel_refl; intros; apply SIPred_dist_refl. Qed.
Lemma SIEnv_dist_sym Δ1 Δ2 n: SIEnv_dist Δ1 Δ2 n → SIEnv_dist Δ2 Δ1 n.
Proof. apply env_rel_sym; intros; apply SIPred_dist_sym; trivial. Qed.
Lemma SIEnv_dist_trans Δ1 Δ2 Δ3 n: SIEnv_dist Δ1 Δ2 n → SIEnv_dist Δ2 Δ3 n → SIEnv_dist Δ1 Δ3 n.
Proof. apply env_rel_trans; intros; eapply SIPred_dist_trans; eauto. Qed.

Definition NonExpansive_env_map (Ψ : SIEnv → SIPred) : Prop :=
  ∀ Δ1 Δ2 n, SIEnv_dist Δ1 Δ2 n → SIPred_dist (Ψ Δ1) (Ψ Δ2) n.

Record Interp := mkInterp { irp_fun :> SIEnv → SIPred; irp_ne : NonExpansive_env_map irp_fun }.

Program Definition rel_in_env (X : var) : Interp :=
  mkInterp (λ Δ, match lookup Δ X return SIPred with Some P => P | None => SIPred_true end) _.
Next Obligation.
Proof.
  intros ? Δ1 Δ2 ?????.
  destruct (lookup Δ1 X) eqn:Heq.
  - eapply env_rel_lookup1 in Heq as (?& -> & Hdst); [|eassumption].
    apply Hdst; trivial.
  - eapply env_rel_lookup1_None in Heq as ->; [|eassumption].
    tauto.
Qed.

Program Definition unit_rel : Interp :=
  mkInterp (λ _, {| sipred n e := e = TT |}) _.
Next Obligation. simpl; intros; subst; constructor. Qed.
Next Obligation. trivial. Qed.
Next Obligation.
Proof. intros ???????; tauto. Qed.

Program Definition tprod_rel (interp1 interp2 : Interp) : Interp :=
  mkInterp (λ Δ, {| sipred n e := ∃ e1 e2, e = Pair e1 e2 ∧ interp1 Δ n e1 ∧ interp2 Δ n e2 |}) _.
Next Obligation. simpl; intros; firstorder; subst; econstructor; eauto. Qed.
Next Obligation.
  simpl; intros; firstorder; subst.
  eexists _, _; split; [reflexivity|]; split; eapply sipred_down_closed; eauto.
Qed.
Next Obligation.
Proof.
  intros ?????????; simpl.
  firstorder; subst.
  - eexists _, _; split; [reflexivity|].
    split; (eapply irp_ne; [apply SIEnv_dist_sym| |]); eauto.
  - eexists _, _; split; [reflexivity|].
    split; eapply irp_ne; eauto.
Qed.

Program Definition tfun_rel (interp1 interp2 : Interp) : Interp :=
  mkInterp
    (λ Δ,
      {| sipred n v :=
          is_val v ∧
            ∀ n' w, n' ≤ n → interp1 Δ n' w → expr_rel (interp2 Δ) n' (App v w)
      |}) _.
Next Obligation. simpl; intros; tauto. Qed.
Next Obligation.
  simpl.
  intros ? ? Δ n n' v Hn'n [? Hv].
  split; [assumption|].
  intros k w Hkn' Hw.
  eapply SISafe_mono; [|eapply Hv; [|eauto]]; [|lia].
  simpl; intros.
  eapply sipred_down_closed; [|eassumption]; lia.
Qed.
Next Obligation.
Proof.
  intros ?????????; simpl.
  intuition.
  - eapply SISafe_mono; [|match goal with H : _ |- _ => eapply H end];
    [|eassumption|eapply irp_ne; [eassumption| |eassumption]]; [|lia].
    simpl; intros ????.
    eapply irp_ne; [apply SIEnv_dist_sym; eassumption| |eassumption].
    lia.
  - eapply SISafe_mono; [|match goal with H : _ |- _ => apply H end];
    [|eassumption|eapply irp_ne; [apply SIEnv_dist_sym; eassumption| |eassumption]];
      [|lia].
    simpl; intros ????.
    eapply irp_ne; [eassumption| |eassumption]. lia.
Qed.

Program Definition tforall_rel (interp : Interp) : Interp :=
  mkInterp
    (λ Δ,
      {| sipred n v :=
          is_val v ∧
            ∀ (P : SIPred), SISafe (interp (P :: Δ)) n (TApp v) |})
    _.
Next Obligation. simpl; intros; tauto. Qed.
Next Obligation.
  simpl; intros interp Δ n n' v Hn'n [? Hv].
  split; [assumption|].
  intros P.
  eapply expr_rel_down_closed; [|eapply Hv]; lia.
Qed.
Next Obligation.
Proof.
  intros ????????; simpl.
  intuition.
  - eapply SISafe_mono; [|match goal with H : _ |- _ => apply H end].
    simpl; intros ????.
    eapply irp_ne; [| |eassumption].
    + apply env_rel_cons; [|apply SIEnv_dist_sym; eassumption].
      apply SIPred_dist_refl.
    + lia.
  - eapply SISafe_mono; [|match goal with H : _ |- _ => apply H end].
    simpl; intros ????.
    eapply irp_ne; [| |eassumption].
    + apply env_rel_cons; [|eassumption].
      apply SIPred_dist_refl.
    + lia.
Qed.

Program Definition trec_rel1 (Ψ : SIPred → SIPred) (P : SIPred) : SIPred :=
  {| sipred n v := ∃ w, v = Fold w ∧ later (Ψ P) n w |}.
Next Obligation.
Proof.
  simpl; intros ? ? n ? (?& -> &?).
  destruct n; [constructor; assumption|].
  constructor; eapply sipred_over_val; eauto.
Qed.
Next Obligation.
Proof.
  simpl; intros ? P n n' e Hn'n Hv.
  destruct Hv as (?& -> &?).
  eexists _; split; [reflexivity|].
  eapply sipred_down_closed; eauto.
Qed.

Lemma trec_rel1_ne (Ψ Φ : SIPred → SIPred) P n e :
  (∀ Q, SIPred_dist (Ψ Q) (Φ Q) n) → trec_rel1 Ψ P n e ↔ trec_rel1 Φ P n e.
Proof.
  intros HΨΦ.
  unfold trec_rel1; simpl.
  firstorder; subst; (eexists _; split; [reflexivity|]).
  - eapply (later_contractive _ _ n); [|lia|eassumption].
    intros ???; symmetry; eapply HΨΦ; eauto.
  - eapply (later_contractive _ _ n); [|lia|eassumption].
    intros ???; eapply HΨΦ; eauto.
Qed.

Lemma trec_rel1_contractive Ψ : NonExpansive Ψ → Contractive (trec_rel1 Ψ).
Proof.
  unfold trec_rel1; intros HΨ ??? HPs ???; simpl.
  eapply HΨ in HPs.
  apply later_contractive in HPs.
  firstorder; subst; (eexists _; split; [reflexivity|apply HPs]).
Qed.

Program Definition trec_rel (interp : Interp) : Interp :=
  mkInterp (λ Δ, fixpoint (trec_rel1 (λ P, interp (P :: Δ))) _) _.
Next Obligation.
Proof.
  intros ??????.
  apply trec_rel1_contractive; [|assumption].
  intros ????.
  apply irp_ne.
  apply env_rel_cons; [assumption|].
  apply SIEnv_dist_refl.
Qed.
Next Obligation.
Proof.
  intros ????????.
  eapply fixpoint_ne; [|eassumption].
  intros P ?.
  eapply SIPred_dist_trans.
  { intros z ??.
    apply trec_rel1_ne.
    intros ????.
    eapply irp_ne; [|eassumption].
    apply env_rel_cons; [apply SIPred_dist_refl|].
    eapply SIEnv_dist_le; [|eassumption]; lia. }
  apply SIPred_dist_refl.
Qed.

Fixpoint val_rel (τ : type) {struct τ} : Interp :=
  match τ with
  | TUnit => unit_rel
  | TVar X => rel_in_env X
  | TProd τ1 τ2 => tprod_rel (val_rel τ1) (val_rel τ2)
  | TFun τ1 τ2 => tfun_rel (val_rel τ1) (val_rel τ2)
  | TForAll τ => tforall_rel (val_rel τ)
  | TRec τ => trec_rel (val_rel τ)
  end.

Local Notation env_rel Δ n Γ env := (env_rel (λ τ, val_rel τ Δ n) Γ env).

Lemma val_rel_is_val Δ τ n v : val_rel τ Δ n v → is_val v.
Proof. apply sipred_over_val. Qed.

Lemma val_rel_weaken_gen Δ1 Δ' Δ2 n τ v :
  val_rel τ (Δ1 ++ Δ2) n v ↔ val_rel (weaken (length Δ1) (length Δ') τ) (Δ1 ++ Δ' ++ Δ2) n v.
Proof.
  revert Δ1 Δ' Δ2 n v.
  induction τ as [| X | | | |]; intros Δ1 Δ' Δ2 n v.
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
  - simpl.
    split; intros [? Happ];
      split; [assumption|intros; eapply SISafe_mono; [intros|eapply Happ]|
               assumption|intros; eapply SISafe_mono; [intros|eapply Happ]]; eauto;
      repeat match goal with H : _ |- _ => apply H; eauto | H : _ |- _ => apply <- H; eauto end.
  - split; intros [? Htapp].
    + split; [assumption|].
      intros ?. eapply SISafe_mono; [|eapply Htapp; fail].
      intros ???.
      apply (IHτ (_ :: _)); eassumption.
    + split; [assumption|].
      intros ?.
      eapply SISafe_mono; [|eapply Htapp; fail].
      intros ?? w Hw.
      eapply (IHτ (_ :: _)) in Hw; eauto.
  - simpl.
    eapply (fixpoint_ne _ _ _ _ (S n)); [|lia].
    intros P k e Hk.
    split; intros [? [? Hltr]]; subst; eexists _; (split; [reflexivity|]).
    + destruct k; [rewrite later_0; rewrite later_0 in Hltr; assumption|].
      rewrite later_S; rewrite later_S in Hltr.
      apply (IHτ (_ :: _)); trivial.
    + destruct k; [rewrite later_0; rewrite later_0 in Hltr; assumption|].
      rewrite later_S; rewrite later_S in Hltr.
      apply (IHτ (_ :: _)) in Hltr; trivial.
Qed.

Lemma val_rel_weaken Δ1 Δ2 τ n v : val_rel τ Δ2 n v ↔ val_rel τ.[ren (+length Δ1)] (Δ1 ++ Δ2) n v.
Proof.
  rewrite (val_rel_weaken_gen nil Δ1 Δ2); simpl.
  rewrite weaken_0; asimpl; tauto.
Qed.

Lemma env_rel_weaken Δ1 Δ' Δ2 n Γ env :
  env_rel (Δ1 ++ Δ2) n Γ env ↔
  env_rel (Δ1 ++ Δ' ++ Δ2) n (map (weaken (length Δ1) (length Δ')) Γ) env.
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

Lemma env_rel_weaken1 P Δ Γ n env :
  env_rel Δ n Γ env → env_rel (P :: Δ) n (map (rename (+1)) Γ) env.
Proof. rewrite (env_rel_weaken (nil) (cons P nil) Δ); simpl; rewrite weaken_0; trivial. Qed.

Lemma val_rel_subst_gen Δ1 τ' Δ2 τ n v :
  val_rel τ (Δ1 ++ (val_rel τ' Δ2) :: Δ2) n v ↔
  val_rel τ.[upn (length Δ1) (τ'.: ids)] (Δ1 ++ Δ2) n v.
Proof.
  revert Δ1 Δ2 n v.
  induction τ as [| X | | | |]; intros Δ1 Δ2 n v.
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
  - simpl.
    split; intros [? Happ];
      split; [assumption|intros; eapply SISafe_mono; [intros|eapply Happ]|
               assumption|intros; eapply SISafe_mono; [intros|eapply Happ]]; eauto;
      repeat match goal with H : _ |- _ => apply H; eauto | H : _ |- _ => apply <- H; eauto end.
  - split; intros [? Htapp].
    + split; [assumption|].
      intros ?. eapply SISafe_mono; [|eapply Htapp; fail].
      intros ???.
      apply (IHτ (_ :: _)); eassumption.
    + split; [assumption|].
      intros ?.
      eapply SISafe_mono; [|eapply Htapp; fail].
      intros ?? w Hw.
      eapply (IHτ (_ :: _)) in Hw; eauto.
  - simpl.
    eapply (fixpoint_ne _ _ _ _ (S n)); [|lia].
    intros P k e Hk.
    split; intros [? [? Hltr]]; subst; eexists _; (split; [reflexivity|]).
    + destruct k; [rewrite later_0; rewrite later_0 in Hltr; assumption|].
      rewrite later_S; rewrite later_S in Hltr.
      apply (IHτ (_ :: _)); trivial.
    + destruct k; [rewrite later_0; rewrite later_0 in Hltr; assumption|].
      rewrite later_S; rewrite later_S in Hltr.
      apply (IHτ (_ :: _)) in Hltr; trivial.
Qed.

Lemma val_rel_subst τ' Δ τ n v : val_rel τ (val_rel τ' Δ :: Δ) n v ↔ val_rel τ.[τ'/] Δ n v.
Proof. apply (val_rel_subst_gen nil). Qed.

Lemma env_rel_down_closed Δ n n' Γ env : n' ≤ n → env_rel Δ n Γ env → env_rel Δ n' Γ env.
Proof.
  revert env.
  induction Γ as [|τ Γ IHΓ]; intros env ?.
  - intros ->%env_rel_inv_nil_l; apply env_rel_nil.
  - simpl.
    intros (?&?&->&?&?)%env_rel_inv_cons_l.
    apply env_rel_cons; [|apply IHΓ; eauto; fail].
    eapply sipred_down_closed; eauto.
Qed.

Theorem Fundamental Γ e τ :
  typed Γ e τ → ∀ n Δ env, env_rel Δ n Γ env → expr_rel (val_rel τ Δ) n e.[env_subst env].
Proof.
  intros Htp.
  induction Htp; intros n Δ env Henv; simpl.
  - simpl.
    assert (val_rel τ Δ n (env_subst env v)).
    { eapply env_rel_lookup1 in Henv as [? [? ?]]; [|eauto; fail].
      erewrite env_subst_lookup; eauto. }
    apply SISafe_val; [eapply val_rel_is_val; eauto|].
    eapply sipred_down_closed; [|eassumption]; lia.
  - apply SISafe_val; [constructor|simpl; trivial].
  - eapply (SISafe_bind _ _ _ (λ e, Pair e _));
      [repeat econstructor; fail|eapply IHHtp1; eauto; fail|].
    intros k v1 ? Hv11 Hv12; simpl.
    eapply (SISafe_bind _ _ _ (λ e, Pair _ e)).
    { repeat econstructor; trivial. }
    { eapply IHHtp2; eapply env_rel_down_closed; [|eassumption]; trivial. }
    intros k' ? v2 Hv21 Hv22.
    apply SISafe_val; [constructor; trivial; fail|].
    eexists _, _; split; [reflexivity|].
    split; [|assumption].
    eapply sipred_down_closed; [|eassumption]; assumption.
  - eapply (SISafe_bind _ _ _ (λ e, Fst e));
      [repeat econstructor; fail|apply IHHtp; eassumption; fail|].
    intros ? v ? Hv1 (v1 & v2 & -> & Hv1r & Hv2r).
    inversion Hv1; subst.
    eapply SISafe_head_step_back; [solve_det_head_step|intros ?].
    apply SISafe_val; [assumption|].
    eapply sipred_down_closed; [|eassumption]; lia.
  - eapply (SISafe_bind _ _ _ (λ e, Snd e));
      [repeat econstructor; fail|apply IHHtp; eassumption; fail|].
    intros ? v ? Hv1 (v1 & v2 & -> & Hv1r & Hv2r).
    inversion Hv1; subst.
    eapply SISafe_head_step_back; [solve_det_head_step|intros ?].
    apply SISafe_val; [assumption|].
    eapply sipred_down_closed; [|eassumption]; lia.
  - apply SISafe_val; [constructor; fail|].
    simpl.
    split; [constructor; fail|].
    intros ? w ? Hw.
    assert (is_val w) by (eapply val_rel_is_val; eauto).
    eapply SISafe_head_step_back; [solve_det_head_step|intros ?].
    asimpl.
    apply (IHHtp _ Δ (_ :: _)).
    apply env_rel_cons;
      [eapply sipred_down_closed; [|eassumption]|eapply env_rel_down_closed; [|eassumption]]; lia.
  - eapply (SISafe_bind _ _ _ (λ e, App e _));
      [repeat econstructor; fail|apply IHHtp1; eassumption; fail|].
    intros ? v1 ? Hv11 Hv12.
    eapply (SISafe_bind _ _ _ (λ e, App _ e)); [| |].
    { repeat econstructor; trivial. }
    { eapply IHHtp2; eapply env_rel_down_closed; [|eassumption]; trivial. }
    intros ? v2 ? Hv21 Hv22.
    apply Hv12; trivial.
  - apply SISafe_val; [constructor; fail|].
    split; [constructor; fail|].
    intros P.
    eapply SISafe_head_step_back; [solve_det_head_step|intros ?].
    apply IHHtp.
    apply env_rel_weaken1; trivial.
    eapply env_rel_down_closed; [|eassumption]; lia.
  - eapply (SISafe_bind _ _ _ (λ e, TApp e));
      [repeat econstructor; fail|apply IHHtp; eassumption; fail|].
    intros ? v ? ? [? Hv].
    eapply SISafe_mono; [|apply Hv; fail].
    intros ????; rewrite <- val_rel_subst; eassumption.
  - eapply SISafe_mono.
    { intros ??? HP. rewrite fixpoint_unfold; exact HP. }
    eapply (SISafe_bind _ _ _ (λ e, Fold e));
      [repeat econstructor; fail|apply IHHtp; eassumption; fail|].
    intros ? v ? ? Hv.
    apply SISafe_val; [econstructor; assumption|].
    eexists _; split; [reflexivity|].
    destruct k; [apply later_0; assumption|].
    apply later_S.
    apply (val_rel_subst (TRec _)).
    eapply sipred_down_closed; [|eassumption]; lia.
  - eapply (SISafe_bind _ _ _ (λ e, Unfold e));
      [repeat econstructor; fail|apply IHHtp; eassumption; fail|].
    intros ? v ? Hiv Hv.
    simpl in *.
    rewrite fixpoint_unfold in Hv.
    destruct Hv as (w&->&Hw).
    inversion Hiv; subst.
    eapply SISafe_head_step_back; [solve_det_head_step|intros ?].
    apply SISafe_val; [assumption|].
    destruct k; [lia|].
    rewrite later_S in Hw.
    apply (val_rel_subst (TRec _)).
    simpl.
    replace (k - 0) with k by lia.
    assumption.
Qed.

Corollary type_safety e τ : typed nil e τ → Safe (λ _, True) e.
Proof.
  intros Htp.
  apply SISafe_adequacy; intros n.
  eapply SISafe_mono; [tauto|].
  replace e with e.[env_subst nil] by (asimpl; reflexivity).
  eapply (Fundamental nil _ _ Htp _ nil); apply env_rel_nil.
Qed.
