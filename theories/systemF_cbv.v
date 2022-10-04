From Coq.Unicode Require Import Utf8.
From Coq.Lists Require Import List.
From Autosubst Require Import Autosubst.
From Coq.Relations Require Import Relations.
From ShortLogrels Require Import prelude language.

Inductive expr :=
| Var (v : var)
| TT
| Pair (e1 e2 : expr)
| Fst (e : expr)
| Snd (e : expr)
| Lam (e : {bind expr})
| App (e1 e2 : expr)
| TLam (e : expr)
| TApp (e : expr).

Global Instance Ids_expr : Ids expr. derive. Defined.
Global Instance Rename_expr : Rename expr. derive. Defined.
Global Instance Subst_expr : Subst expr. derive. Defined.
Global Instance SubstLemmas_expr : SubstLemmas expr. derive. Qed.

Inductive is_val : expr → Prop :=
| IVTT : is_val TT
| IVPair e1 e2 : is_val e1 → is_val e2 → is_val (Pair e1 e2)
| IVLam e : is_val (Lam e)
| IVTLam e : is_val (TLam e).

Inductive type :=
| TUnit
| TVar (X : var)
| TProd (τ1 τ2 : type)
| TFun (τ1 τ2 : type)
| TForAll (τ : {bind type}).

Global Instance Ids_type : Ids type. derive. Defined.
Global Instance Rename_type : Rename type. derive. Defined.
Global Instance Subst_type : Subst type. derive. Defined.
Global Instance SubstLemmas_type : SubstLemmas type. derive. Qed.

Definition context := environment type.

Inductive typed : context → expr → type → Prop :=
| TPVar Γ v τ : lookup Γ v = Some τ → typed Γ (Var v) τ
| TPTT Γ : typed Γ TT TUnit
| TPPAIR Γ e1 τ1 e2 τ2 : typed Γ e1 τ1 → typed Γ e2 τ2 → typed Γ (Pair e1 e2) (TProd τ1 τ2)
| TPFst Γ e τ1 τ2 : typed Γ e (TProd τ1 τ2) → typed Γ (Fst e) τ1
| TPSnd Γ e τ1 τ2 : typed Γ e (TProd τ1 τ2) → typed Γ (Snd e) τ2
| TPLam Γ e τ1 τ2 : typed (τ1 :: Γ) e τ2 → typed Γ (Lam e) (TFun τ1 τ2)
| TPApp Γ e1 e2 τ1 τ2 : typed Γ e1 (TFun τ1 τ2) → typed Γ e2 τ1 → typed Γ (App e1 e2) τ2
| TPTLam Γ e τ : typed (map (rename (+1)) Γ) e τ → typed Γ (TLam e) (TForAll τ)
| TPTApp Γ e τ τ' : typed Γ e (TForAll τ) → typed Γ (TApp e) τ.[τ'/].

Inductive head_step : expr → expr → Prop :=
| SFst e1 e2 : is_val e1 → is_val e2 → head_step (Fst (Pair e1 e2)) e1
| SSnd e1 e2 : is_val e1 → is_val e2 → head_step (Snd (Pair e1 e2)) e2
| SApp e1 e2 : is_val e2 → head_step (App (Lam e1) e2) e1.[e2/]
| STApp e : head_step (TApp (TLam e)) e.

Inductive is_ectx : (expr → expr) → Prop :=
| ECTX_id : is_ectx (λ e, e)
| ECTX_Fst K : is_ectx K → is_ectx (λ e, Fst (K e))
| ECTX_Snd K : is_ectx K → is_ectx (λ e, Snd (K e))
| ECTX_Pair1 K e2 : is_ectx K → is_ectx (λ e, Pair (K e) e2)
| ECTX_Pair2 e1 K : is_val e1 → is_ectx K → is_ectx (λ e, Pair e1 (K e))
| ECTX_App1 K e2 : is_ectx K → is_ectx (λ e, App (K e) e2)
| ECTX_App2 e1 K : is_val e1 → is_ectx K → is_ectx (λ e, App e1 (K e))
| ECTX_TApp K : is_ectx K → is_ectx (λ e, TApp (K e)).

Local Hint Constructors is_ectx : is_ectx.

Lemma is_ectx_val : ∀ (e : expr) (K : expr → expr), is_ectx K → is_val (K e) → is_val e.
Proof.
  intros e K HK; revert e.
  induction HK; [trivial; fail|inversion 1; subst; auto .. ].
Qed.

Lemma is_val_dec e : is_val e ∨ ¬ is_val e.
Proof.
  induction e; try (right; inversion 1; fail).
  - left; constructor.
  - destruct IHe1; destruct IHe2; [left; constructor; auto; fail|right; inversion 1; tauto .. ].
  - left; constructor.
  - left; constructor.
Qed.

Lemma ectx_head_step K e e' : is_ectx K → head_step (K e) e' → (∀ f : expr, K f = f) ∨ is_val e.
Proof.
  intros HK; revert e e'.
  induction HK.
  - left; trivial.
  - inversion HK; inversion 1; subst; right; [econstructor; eauto|eapply is_ectx_val; eauto .. ].
  - inversion HK; inversion 1; subst; right; [econstructor; eauto|eapply is_ectx_val; eauto .. ].
  - inversion HK; inversion 1.
  - inversion HK; inversion 1.
  - inversion HK; inversion 1; subst; right; constructor.
  - inversion 1; subst; right; eapply is_ectx_val; eauto.
  - inversion HK;inversion 1; subst; right; constructor.
Qed.

Lemma ectx_inj K e e' : is_ectx K → K e = K e' → e = e'.
Proof.
  intros HK; revert e e'.
  induction HK; intros e e' Hee.
  - trivial.
  - intros; assert (K e = K e') by congruence; auto.
  - intros; assert (K e = K e') by congruence; auto.
  - intros; assert (K e = K e') by congruence; auto.
  - intros; assert (K e = K e') by congruence; auto.
  - intros; assert (K e = K e') by congruence; auto.
  - intros; assert (K e = K e') by congruence; auto.
  - intros; assert (K e = K e') by congruence; auto.
Qed.

Lemma ectx_compose K K' : is_ectx K → is_ectx K' → is_ectx (λ e : expr, K (K' e)).
Proof.
  intros HK; revert K'.
  induction HK; [trivial| intros; econstructor; eauto .. ].
Qed.

Lemma ectxs_nesting K e K' e' :
  is_ectx K → is_ectx K' → K e = K' e' → ¬ is_val e → ¬ is_val e' →
  (∃ K'' : expr → expr, is_ectx K'' ∧ (∀ f : expr, K f = K' (K'' f)))
  ∨ (∃ K'' : expr → expr, is_ectx K'' ∧ (∀ f : expr, K' f = K (K'' f))).
Proof.
  intros HK; revert e e' K'.
  induction HK as [|?? IHK|?? IHK | K e2 ? IHK|e1 K Hval ? IHK|K e2 ? IHK|e1 K Hval ? IHK|
                    K HK IHK];
    intros e e' K' HK' Hee Hnve Hnve'.
  - right; exists K'; auto.
  - destruct HK'; [left; exists (λ e, Fst (K e)); auto with is_ectx; fail| |congruence ..].
    destruct (IHK e e' _ HK') as [[K'' [? HK'']]|[K'' [? HK'']]];
      [congruence|assumption|assumption| left|right];
      (exists K''; split; [assumption|intros ?; rewrite HK''; trivial]).
  - destruct HK'; [left; exists (λ e, Snd (K e)); auto with is_ectx; fail|
                    congruence| |congruence ..].
    destruct (IHK e e' _ HK') as [[K'' [? HK'']]|[K'' [? HK'']]];
      [congruence|assumption| assumption|left|right];
      (exists K''; split; [assumption|intros ?; rewrite HK''; trivial]).
  - destruct HK' as [| | | |? ? Hval | | |];
      [left; eexists (λ e, Pair (K e) e2); eauto with is_ectx; fail|
        congruence|congruence | | |congruence .. ].
    + simplify_eq Hee; intros; subst.
      destruct (IHK e e' _ HK') as [[K'' [? HK'']]|[K'' [? HK'']]];
        [congruence|assumption|assumption|left|right];
        (exists K''; split; [assumption|intros ?; rewrite HK''; trivial]).
    + simplify_eq Hee; intros; subst.
      apply is_ectx_val in Hval; tauto.
  - destruct HK'; [left; eexists (λ e, Pair e1 (K e)); eauto with is_ectx; fail|
        congruence|congruence | | |congruence .. ].
    + simplify_eq Hee; intros; subst.
      apply is_ectx_val in Hval; tauto.
    + simplify_eq Hee; intros; subst.
      destruct (IHK e e' _ HK') as [[K'' [? HK'']]|[K'' [? HK'']]];
        [congruence|assumption|assumption|left|right];
        (exists K''; split; [assumption|intros ?; rewrite HK''; trivial]).
  - destruct HK' as [| | | | | |? ? Hval |];
      [left; exists (λ e, App (K e) e2); auto with is_ectx; fail|
        congruence|congruence| congruence|congruence| | |congruence].
    + simplify_eq Hee; intros; subst.
      destruct (IHK e e' _ HK') as [[K'' [? HK'']]|[K'' [? HK'']]];
      [congruence|assumption|assumption| left|right];
        (exists K''; split; [assumption|intros ?; rewrite HK''; trivial]).
    + simplify_eq Hee; intros; subst.
      apply is_ectx_val in Hval; tauto.
  - destruct HK';
      [left; exists (λ e, App e1 (K e)); auto with is_ectx; fail|
        congruence|congruence| congruence|congruence| | |congruence].
    + simplify_eq Hee; intros; subst.
      apply is_ectx_val in Hval; tauto.
    + simplify_eq Hee; intros; subst.
      destruct (IHK e e' _ HK') as [[K'' [? HK'']]|[K'' [? HK'']]];
      [congruence|assumption|assumption| left|right];
        (exists K''; split; [assumption|intros ?; rewrite HK''; trivial]).
  - destruct HK';
      [left; exists (λ e, TApp (K e)); auto with is_ectx; fail|
        congruence|congruence| congruence|congruence|congruence|congruence|].
    simplify_eq Hee; intros; subst.
    destruct (IHK e e' _ HK') as [[K'' [? HK'']]|[K'' [? HK'']]];
      [congruence|assumption|assumption| left|right];
        (exists K''; split; [assumption|intros ?; rewrite HK''; trivial]).
Qed.

Global Instance stlc_valid_language : valid_language is_val is_ectx head_step.
Proof.
  split.
  - inversion 1; inversion 1.
  - apply is_ectx_val.
  - constructor.
  - apply is_val_dec.
  - apply ectx_head_step.
  - apply ectx_inj.
  - apply ectx_compose.
  - apply ectxs_nesting.
Qed.

Lemma det_head_step_fst v1 v2 : is_val v1 → is_val v2 → det_head_step (Fst (Pair v1 v2)) v1.
Proof.
  intros; split; [constructor; assumption| inversion 1; subst; reflexivity].
Qed.

Lemma det_head_step_snd v1 v2 : is_val v1 → is_val v2 → det_head_step (Snd (Pair v1 v2)) v2.
Proof.
  intros; split; [constructor; assumption| inversion 1; subst; reflexivity].
Qed.

Lemma det_head_step_app e v : is_val v → det_head_step (App (Lam e) v) e.[v/].
Proof.
  intros; split; [econstructor; assumption| inversion 1; subst; reflexivity].
Qed.

Lemma det_head_step_tapp e : det_head_step (TApp (TLam e)) e.
Proof.
  intros; split; [econstructor; assumption| inversion 1; subst; reflexivity].
Qed.

Ltac solve_det_head_step :=
  solve [eapply det_head_step_fst; eassumption|
          eapply det_head_step_snd; eassumption|
          eapply det_head_step_app; eassumption|
          eapply det_head_step_tapp; eassumption].
