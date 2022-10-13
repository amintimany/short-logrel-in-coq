From Coq.Unicode Require Import Utf8.
From Coq.Lists Require Import List.
From Coq.Program Require Import Wf.
From Coq.Arith Require Import Wf_nat.
From Autosubst Require Import Autosubst.
From Coq.Relations Require Import Relations.
From Coq.micromega Require Import Lia.
From ShortLogrels Require Import prelude language systemF_rec_cbv.

Inductive type_lt : type → type → Prop :=
| TProd_lt1 τ τ' : type_lt τ (TProd τ τ')
| TProd_lt2 τ τ' : type_lt τ' (TProd τ τ')
| TFun_lt1 τ τ' : type_lt τ (TFun τ τ')
| TFun_lt2 τ τ' : type_lt τ' (TFun τ τ').

Definition wf_rel (nτ nτ' : nat * type) : Prop :=
  fst nτ < fst nτ' ∨ (fst nτ ≤ fst nτ' ∧ type_lt (snd nτ) (snd nτ')).

Lemma wf_rel_well_founded : well_founded wf_rel.
Proof.
  intros [n τ].
  revert τ; induction (lt_wf n) as [n Hn IHn]; intros τ.
  assert (∃ k, k = n ∧ k ≤ n) as [k [Heq Hk]] by (exists n; lia).
  rewrite <- Heq; clear Heq.
  revert k Hk; induction τ; intros k Hk.
  - constructor; intros [] Hlt.
    inversion Hlt as [|[? Hlt']]; simpl in *; [apply IHn; lia|subst].
    inversion Hlt'.
  - constructor; intros [] Hlt.
    inversion Hlt as [|[? Hlt']]; simpl in *; [apply IHn; lia|subst].
    inversion Hlt'.
  - constructor; intros [] Hlt.
    inversion Hlt as [|[? Hlt']]; simpl in *; [apply IHn; lia|subst].
    inversion Hlt'; subst.
    + eapply IHτ1; lia.
    + eapply IHτ2; lia.
  - constructor; intros [] Hlt.
    inversion Hlt as [|[? Hlt']]; simpl in *; [apply IHn; lia|subst].
    inversion Hlt'; subst.
    + eapply IHτ1; lia.
    + eapply IHτ2; lia.
  - constructor; intros [] Hlt.
    inversion Hlt as [|[? Hlt']]; simpl in *; [apply IHn; lia|subst].
    inversion Hlt'.
  - constructor; intros [] Hlt.
    inversion Hlt as [|[? Hlt']]; simpl in *; [apply IHn; lia|subst].
    inversion Hlt'.
Qed.

Ltac solve_wf_rel := solve [left; simpl; lia|right; split; [simpl; lia|simpl; constructor]].

Program Definition SISafe' (n : nat) (P : ∀ k, k < n → expr → Prop) (e : expr) :=
    ∀ k e' (Hle : k ≤ n),
      nsteps k e e' → (is_val e' ∧ ∀ (Hpos : 0 < k), P (n - k) _ e') ∨ ∃ e'', step e' e''.
Next Obligation.
Proof. lia. Qed.

Lemma SISafe'_ext (n : nat) (P Q : ∀ k, k < n → expr → Prop) (e : expr) :
  (∀ k Hle v, P k Hle v ↔ Q k Hle v) → SISafe' n P e ↔ SISafe' n Q e.
Proof.
  intros Hext; split; intros Hsf ????.
  - edestruct Hsf as [[]|]; [eassumption|left|right; assumption].
    split; [assumption|intros; apply Hext; auto].
  - edestruct Hsf as [[]|]; [eassumption|left|right; assumption].
    split; [assumption|intros; apply Hext; auto].
Qed.

Lemma SISafe'_SISafe P n e : ¬ is_val e → SISafe' n (λ k _ v, P k v) e ↔ SISafe P n e.
Proof.
  intros Hniv; split.
  - intros Hsf; intros k e' Hk Hstps.
    destruct k as [|k].
    + inversion Hstps; subst.
      destruct (Hsf 0 e' Hk Hstps) as [[]|]; tauto.
    + destruct (Hsf (S k) e' Hk Hstps) as [[? HP]|]; [|tauto].
      left; split; [assumption|].
      apply HP; lia.
  - intros Hsf; intros k e' Hk Hstps.
    destruct (Hsf k e' Hk Hstps) as [[? HP]|]; tauto.
Qed.

Lemma lt_le_le {n m l} : n < m → m ≤ l → n ≤ l.
Proof. lia. Qed.

Lemma prod_lt1 {k τ1 τ2} : wf_rel (k, τ1) (k, TProd τ1 τ2).
Proof. solve_wf_rel. Qed.
Lemma prod_lt2 {k τ1 τ2} : wf_rel (k, τ2) (k, TProd τ1 τ2).
Proof. solve_wf_rel. Qed.
Lemma fun_lt1 {n τ1 τ2 k} : k ≤ n → wf_rel (k, τ1) (n, TFun τ1 τ2).
Proof. solve_wf_rel. Qed.
Lemma fun_lt2 {n τ1 τ2 k} : k ≤ n → wf_rel (k, τ2) (n, TFun τ1 τ2).
Proof. solve_wf_rel. Qed.
Lemma si_lt {n τ τ' z} : z < n → wf_rel (z, τ') (n, τ).
Proof. solve_wf_rel. Qed.

Lemma pos_sub_lt {n m} : 0 < m → m ≤ n → n - m < n.
Proof. lia. Qed.
Lemma lt_eq_S n m : S n = m → n < m.
Proof. lia. Qed.

Definition val_rel_aux_prod {k τ1 τ2}
  (vlrl : ∀ nτ', wf_rel nτ' (k, TProd τ1 τ2) → expr → Prop) v :=
  ∃ v1 v2, v = Pair v1 v2 ∧ vlrl (k, τ1) prod_lt1 v1 ∧ vlrl (k, τ2) prod_lt2 v2.

Lemma val_rel_aux_prod_ext n τ1 τ2 (f g : ∀ nτ', wf_rel nτ' (n, TProd τ1 τ2) → expr → Prop) e :
  (∀ m τ Hrl e, f (m, τ) Hrl e ↔ g (m, τ) Hrl e) →
  val_rel_aux_prod f e ↔ val_rel_aux_prod g e.
Proof.
  intros Hfg; split; intros (?&?&->&?&?); (eexists _, _; split; [reflexivity|]; split);
    (apply Hfg; assumption).
Qed.

Definition val_rel_aux_fun {k τ1 τ2}
  (vlrl : ∀ nτ', wf_rel nτ' (k, TFun τ1 τ2) → expr → Prop) v :=
  is_val v ∧
  ∀ m w (Hle : m ≤ k),
    vlrl (m, τ1) (fun_lt1 Hle) w →
    SISafe' m (λ z Hlt u, vlrl (z, τ2) (fun_lt2 (lt_le_le Hlt Hle)) u) (App v w).

Lemma val_rel_aux_fun_ext n τ1 τ2 (f g : ∀ nτ', wf_rel nτ' (n, TFun τ1 τ2) → expr → Prop) e :
  (∀ m τ Hrl e, f (m, τ) Hrl e ↔ g (m, τ) Hrl e) →
  val_rel_aux_fun f e ↔ val_rel_aux_fun g e.
Proof.
  intros Hfg; split; intros [Hiv Hrl]; (split; [assumption|]).
  - intros m w Hle Hvrl.
    eapply SISafe'_ext; [|apply Hrl; apply Hfg; eassumption].
    intros; symmetry; apply Hfg.
  - intros m w Hle Hvrl.
    eapply SISafe'_ext; [|apply Hrl; apply Hfg; eassumption].
    intros; apply Hfg.
Qed.

Definition val_rel_aux_forall {k τ}
  (vlrl : ∀ nτ', wf_rel nτ' (k, TForAll τ) → expr → Prop) v :=
  is_val v ∧ ∀ τ', SISafe' k (λ z Hlt u, vlrl (z, τ.[τ'/]) (si_lt Hlt) u) (TApp v).

Lemma val_rel_aux_forall_ext n τ (f g : ∀ nτ', wf_rel nτ' (n, TForAll τ) → expr → Prop) e :
  (∀ m τ Hrl e, f (m, τ) Hrl e ↔ g (m, τ) Hrl e) →
  val_rel_aux_forall f e ↔ val_rel_aux_forall g e.
Proof.
  intros Hfg; split; intros [Hiv Hrl]; (split; [assumption|]);
    intros τ'.
  - eapply SISafe'_ext; [|apply Hrl; apply Hfg; eassumption].
    intros; symmetry; apply Hfg.
  - eapply SISafe'_ext; [|apply Hrl; apply Hfg; eassumption].
    intros; apply Hfg.
Qed.

Definition val_rel_aux_rec {k τ}
  (vlrl : ∀ nτ', wf_rel nτ' (k, TRec τ) → expr → Prop) v :=
  is_val v ∧
    ∃ w, v = Fold w ∧
      match k as u return u = k → Prop with
      | 0 => λ _, True
      | S n' => λ Heq, vlrl (n', τ.[TRec τ/]) (si_lt (lt_eq_S _ _ Heq)) w
      end eq_refl.

Lemma val_rel_aux_rec_ext n τ (f g : ∀ nτ', wf_rel nτ' (n, TRec τ) → expr → Prop) e :
  (∀ m τ Hrl e, f (m, τ) Hrl e ↔ g (m, τ) Hrl e) →
  val_rel_aux_rec f e ↔ val_rel_aux_rec g e.
Proof.
  intros Hfg; split; intros [Hiv (w & -> & Hw)]; (split; [assumption|]).
  - eexists _; split; [reflexivity|].
    destruct n; [tauto|].
    apply Hfg; assumption.
  - eexists _; split; [reflexivity|].
    destruct n; [tauto|].
    apply Hfg; assumption.
Qed.

Definition val_rel_aux
  (nτ : nat * type) (vlrl : ∀ nτ', wf_rel nτ' nτ → expr → Prop) (v : expr) : Prop :=
  match snd nτ as u return (∀ nτ', wf_rel nτ' (fst nτ, u) → expr → Prop) → Prop with
  | TUnit => λ _, v = TT
  | TVar X => λ _, False
  | TProd τ1 τ2 => λ vlrl', val_rel_aux_prod vlrl' v
  | TFun τ1 τ2 => λ vlrl', val_rel_aux_fun vlrl' v
  | TForAll τ => λ vlrl', val_rel_aux_forall vlrl' v
  | TRec τ => λ vlrl', val_rel_aux_rec vlrl' v
  end vlrl.

Lemma val_rel_aux_ext n τ (f g : ∀ nτ', wf_rel nτ' (n, τ) → expr → Prop) e :
  (∀ m τ Hrl e, f (m, τ) Hrl e ↔ g (m, τ) Hrl e) →
  val_rel_aux (n, τ) f e ↔ val_rel_aux (n, τ) g e.
Proof.
  intros Hfg.
  induction τ; simpl; [tauto|tauto| | | |].
  - apply val_rel_aux_prod_ext; auto.
  - apply val_rel_aux_fun_ext; auto.
  - apply val_rel_aux_forall_ext; auto.
  - apply val_rel_aux_rec_ext; auto.
Qed.

Fixpoint val_rel_aux' (nτ : nat * type) (Hacc : Acc wf_rel nτ) (v : expr) : Prop :=
  match Hacc return Prop with
  | Acc_intro _ MkAcc => val_rel_aux nτ (λ nτ' Hnτ', val_rel_aux' nτ' (MkAcc _ Hnτ')) v
  end.

Lemma val_rel_aux'_irrel (nτ : nat * type) (Hacc Hacc' : Acc wf_rel nτ) (v : expr) :
  val_rel_aux' nτ Hacc v ↔ val_rel_aux' nτ Hacc' v.
Proof.
  revert Hacc Hacc' v.
  induction (wf_rel_well_founded nτ) as [[n τ] ? IH]; intros Hacc Hacc' v.
  destruct Hacc; destruct Hacc'; simpl.
  apply val_rel_aux_ext.
  intros m τ' Hrl e'; simpl.
  apply IH; assumption.
Qed.

Definition val_rel (τ : type) (n : nat) (v : expr) :=
  val_rel_aux' (n, τ) (wf_rel_well_founded (n, τ)) v.

Lemma val_rel_unfold n τ e :
  val_rel τ n e ↔ val_rel_aux (n, τ) (λ nτ' _ e', val_rel (snd nτ') (fst nτ') e') e.
Proof.
  remember (n, τ) as nτ; symmetry in Heqnτ.
  revert n τ Heqnτ e.
  induction (wf_rel_well_founded nτ) as [[n τ] ? IH]; intros n' τ' Heqnτ e.
  inversion Heqnτ; subst; clear Heqnτ.
  unfold val_rel.
  destruct wf_rel_well_founded; simpl.
  apply val_rel_aux_ext.
  intros m τ' Hrl e'; simpl.
  apply val_rel_aux'_irrel.
Qed.

Opaque val_rel.

Definition expr_rel (τ : type) (n : nat) (e : expr) := SISafe (val_rel τ) n e.

Lemma val_rel_unit n e : val_rel TUnit n e ↔ e = TT.
Proof. rewrite val_rel_unfold; destruct n; simpl; tauto. Qed.

Lemma val_rel_var X n e : val_rel (TVar X) n e ↔ False.
Proof. rewrite val_rel_unfold; destruct n; simpl; tauto. Qed.

Lemma val_rel_prod τ1 τ2 n e :
  val_rel (TProd τ1 τ2) n e ↔ ∃ v1 v2, e = Pair v1 v2 ∧ val_rel τ1 n v1 ∧ val_rel τ2 n v2.
Proof. rewrite val_rel_unfold; simpl; tauto. Qed.

Lemma val_rel_fun τ1 τ2 n e :
  val_rel (TFun τ1 τ2) n e ↔ is_val e ∧ ∀ k w, k ≤ n → val_rel τ1 k w → expr_rel τ2 k (App e w).
Proof.
  rewrite val_rel_unfold; unfold val_rel_aux; simpl; unfold val_rel_aux_fun.
  split; intros [? Her]; (split; [assumption|]);
    intros; (apply SISafe'_SISafe; [inversion 1|apply Her; eauto]).
Qed.

Lemma val_rel_tforall τ n e :
  val_rel (TForAll τ) n e ↔ is_val e ∧ ∀ τ', expr_rel τ.[τ'/] n (TApp e).
Proof.
  rewrite val_rel_unfold; simpl.
  split; intros [? Her]; (split; [assumption|]);
    intros; (apply SISafe'_SISafe; [inversion 1|apply Her]).
Qed.

Lemma val_rel_trec τ n e :
  val_rel (TRec τ) n e ↔
  is_val e ∧ ∃ w, e = Fold w ∧ match n with 0 => True | S n' => val_rel τ.[TRec τ/] n' w end.
Proof.
  rewrite val_rel_unfold.
  unfold val_rel_aux; simpl; unfold val_rel_aux_rec; simpl.
  destruct n; firstorder.
Qed.

Ltac simpl_val_rel := rewrite ?val_rel_unit, ?val_rel_var,
    ?val_rel_prod, ?val_rel_fun, ?val_rel_tforall, ?val_rel_trec.

Lemma val_rel_is_val τ n v : val_rel τ n v → is_val v.
Proof. revert n v; induction τ; intros n v; simpl_val_rel; firstorder; subst; constructor; eauto. Qed.

Lemma val_rel_down_closed τ n n' v : n' ≤ n → val_rel τ n v → val_rel τ n' v.
Proof.
  remember (n, τ) as nτ; symmetry in Heqnτ.
  revert n' v n τ Heqnτ.
  induction (wf_rel_well_founded nτ) as [[n τ] ? IH]; intros n' v ? ?.
  inversion 1; subst.
  intros Hn'.
  destruct τ; simpl_val_rel; [tauto|tauto| | | |].
  - firstorder; subst; eexists _, _; split; [reflexivity|];
      split; eapply IH; eauto; solve_wf_rel.
  - intros [? Hsf]; split; [assumption|].
    intros; eapply SISafe_mono; [|apply Hsf; [lia|assumption]].
    intros; eapply IH; [| | |eassumption]; [|reflexivity|lia]; solve_wf_rel.
  - intros [? Hsf]; split; [assumption|].
    intros; eapply SISafe_down_closed'; [inversion 1| | |eapply Hsf]; [assumption|].
    intros ?????; eapply IH; [|reflexivity|assumption]; solve_wf_rel.
  - intros [? (?&->&Hsf)]; split; [assumption|].
    eexists _; split; [reflexivity|].
    destruct n; destruct n'; [tauto|lia|tauto|].
    eapply IH; [|reflexivity| |eassumption]; [|lia]; solve_wf_rel.
Qed.

Definition expr_rel_down_closed τ n n' e : n' ≤ n → expr_rel τ n e → expr_rel τ n' e.
Proof.
  intros; eapply SISafe_down_closed; [eassumption| |eassumption].
  intros; eapply val_rel_down_closed; eauto.
Qed.

Local Notation env_rel n Γ env := (env_rel (λ τ, val_rel τ n) Γ env).

Lemma env_rel_down_closed n n' Γ env : n' ≤ n → env_rel n Γ env → env_rel n' Γ env.
Proof.
  revert env.
  induction Γ as [|τ Γ IHΓ]; intros env ?.
  - intros ->%env_rel_inv_nil_l; apply env_rel_nil.
  - simpl.
    intros (?&?&->&?&?)%env_rel_inv_cons_l.
    apply env_rel_cons; [|apply IHΓ; eauto; fail].
    eapply val_rel_down_closed; eauto.
Qed.

Theorem Fundamental Γ e τ f :
  typed Γ e τ → ∀ n env, env_rel n (map (subst f) Γ) env → expr_rel τ.[f] n e.[env_subst env].
Proof.
  intros Htp; revert f.
  induction Htp; intros f n env Henv; simpl.
  - assert (val_rel τ.[f] n (env_subst env v)).
    { eapply env_rel_lookup1 in Henv as [? [? ?]]; [|apply lookup_map; eassumption].
      erewrite env_subst_lookup; eauto. }
    apply SISafe_val; [eapply val_rel_is_val; eauto|assumption].
  - apply SISafe_val; [constructor|].
    simpl_val_rel; destruct n; [constructor|reflexivity].
  - eapply (SISafe_bind _ _ _ (λ e, Pair e _));
      [repeat econstructor; fail|apply IHHtp1; eassumption; fail|].
    intros ? v1 ? Hv11 Hv12.
    eapply (SISafe_bind _ _ _ (λ e, Pair _ e));
      [|eapply IHHtp2; eapply env_rel_down_closed; eauto; fail|].
    { repeat econstructor; trivial. }
    intros z v2 ? Hv21 Hv22.
    apply SISafe_val; [constructor; trivial|].
    simpl_val_rel.
    eexists _, _; split; [reflexivity|];
    split; (eapply val_rel_down_closed; [|eauto]); lia.
  - eapply (SISafe_bind _ _ _ (λ e, Fst e));
      [repeat econstructor; fail|apply IHHtp; eassumption; fail|].
    intros k v ? Hv1; simpl.
    simpl_val_rel.
    intros (v1 & v2 & -> & Hv1r & Hv2r).
    inversion Hv1; subst.
    eapply SISafe_head_step_back; [solve_det_head_step|]; intros ?.
    destruct k; [lia|]; simpl in *.
    apply SISafe_val; [assumption|].
    eapply val_rel_down_closed; [|eassumption]; lia.
  - eapply (SISafe_bind _ _ _ (λ e, Snd e));
      [repeat econstructor; fail|apply IHHtp; eassumption; fail|].
    intros k v ? Hv1; simpl.
    simpl_val_rel.
    intros (v1 & v2 & -> & Hv1r & Hv2r).
    inversion Hv1; subst.
    eapply SISafe_head_step_back; [solve_det_head_step|]; intros.
    apply SISafe_val; [assumption|].
    eapply val_rel_down_closed; [|eassumption]; lia.
  - apply SISafe_val; [constructor; fail|].
    simpl_val_rel.
    split; [constructor; fail|].
    intros k w ? Hw.
    assert (is_val w) by (eapply val_rel_is_val; eauto).
    eapply SISafe_head_step_back; [solve_det_head_step|]; intros ?.
    asimpl.
    apply (IHHtp _ _ (_ :: _)).
    apply env_rel_cons;
      [eapply val_rel_down_closed; [|eassumption]|eapply env_rel_down_closed; [|eassumption]];
      lia.
  - eapply (SISafe_bind _ _ _ (λ e, App e _));
      [repeat econstructor; fail|apply IHHtp1; eassumption; fail|].
    intros ? v1 ? Hv11.
    simpl; simpl_val_rel; intros Hv12.
    eapply (SISafe_bind _ _ _ (λ e, App _ e));
      [|apply IHHtp2; eapply env_rel_down_closed; eauto; fail|].
    { repeat econstructor; trivial. }
    intros ? v2 ? Hv21 Hv22.
    eapply Hv12 ; trivial.
  - apply SISafe_val; [constructor; fail|].
    simpl_val_rel.
    split; [constructor; fail|].
    intros τ'.
    eapply SISafe_head_step_back; [solve_det_head_step|]; intros.
    eapply (expr_rel_down_closed _ n); [lia|].
    asimpl; apply IHHtp.
    erewrite map_map, map_ext; [eassumption|].
    intros ?; asimpl; reflexivity.
  - eapply (SISafe_bind _ _ _ (λ e, TApp e));
      [repeat econstructor; fail|apply IHHtp; eassumption; fail|].
    intros ? v ? ?.
    simpl; simpl_val_rel; intros [? Hv].
    eapply SISafe_mono; [|apply Hv].
    intros ???. asimpl; eauto.
  - eapply (SISafe_bind _ _ _ (λ e, Fold e));
      [repeat econstructor; fail|apply IHHtp; eassumption; fail|].
    intros ? v ? ? Hv.
    apply SISafe_val; [constructor; assumption|].
    simpl_val_rel.
    split; [constructor; assumption|].
    eexists _; split; [reflexivity|].
    destruct k as [|k]; [tauto|].
    asimpl in *.
    eapply val_rel_down_closed; [|eassumption]; lia.
  - eapply (SISafe_bind _ _ _ (λ e, Unfold e));
      [repeat econstructor; fail|apply IHHtp; eassumption; fail|].
    intros ? v ? ?.
    simpl; simpl_val_rel; intros [Hiv (?&->&Hv)].
    inversion Hiv; subst.
    eapply SISafe_head_step_back; [solve_det_head_step|]; intros.
    destruct k as [|k]; [lia|]; asimpl in *.
    apply SISafe_val; [assumption|].
    eapply val_rel_down_closed; [|eassumption]; lia.
Qed.

Corollary type_safety e τ : typed nil e τ → Safe (λ _, True) e.
Proof.
  intros Htp.
  apply SISafe_adequacy; intros n.
  replace e with e.[env_subst nil] by (asimpl; reflexivity).
  eapply SISafe_mono; [tauto|].
  pose proof (Fundamental nil _ _ ids Htp n nil) as Hfm.
  replace τ.[ids] with τ in Hfm by (asimpl; reflexivity).
  eapply Hfm.
  apply env_rel_nil.
Qed.
