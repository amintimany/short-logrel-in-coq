From Coq.Unicode Require Import Utf8.
From Coq.Lists Require Import List.
From Autosubst Require Import Autosubst.
From Coq.Relations Require Import Relations.
From Coq.micromega Require Import Lia.

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

  Lemma lookup_app_l env1 env2 x : x < length env1 → lookup (env1 ++ env2) x = lookup env1 x.
  Proof. apply nth_error_app1. Qed.

  Lemma lookup_app_r env1 env2 x :
    length env1 ≤ x → lookup (env1 ++ env2) x = lookup env2 (x - length env1).
  Proof. apply nth_error_app2. Qed.

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

  Definition weaken (n m : nat) (e : expr) := e.[upn n (ren (+ m))].

  Lemma weaken_var n m x : weaken n m (ids x) = ids (if Nat.ltb x n then x else x + m).
  Proof.
    unfold weaken.
    asimpl.
    revert n m.
    induction x as [|x IHx]; intros n m.
    - destruct n; asimpl; trivial.
    - asimpl.
      destruct n as [|n]; asimpl; [f_equal; lia|].
      destruct n as [|n]; asimpl; [f_equal; lia|].
      rewrite IHx; asimpl.
      destruct Nat.leb; trivial.
  Qed.

  Lemma weaken_0 n : weaken 0 n = rename (+n).
  Proof.
    apply FunctionalExtensionality.functional_extensionality.
    unfold weaken. asimpl; trivial.
  Qed.

  Lemma upn_ext n f x : upn n f x = if Nat.ltb x n then ids x else (f (x - n)).[ren (+n)].
  Proof.
    revert x f. induction n as [|n IHn]; intros x f.
    + asimpl. rewrite PeanoNat.Nat.sub_0_r; trivial.
    + destruct x; [asimpl; reflexivity|].
      asimpl.
      rewrite IHn.
      destruct n; asimpl; [reflexivity|].
      destruct Nat.leb; [asimpl; reflexivity|].
      asimpl; trivial.
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

  Lemma env_rel_lookup1_None env1 env2 x :
    env_rel env1 env2 → lookup env1 x = None → lookup env2 x = None.
  Proof.
    intros Her.
    revert x.
    induction Her.
    - intros ??; rewrite lookup_nil; congruence.
    - intros z Hz.
      destruct z; simpl; [|eauto; fail].
      inversion Hz.
  Qed.

  Lemma env_rel_lookup2_None env1 env2 x :
    env_rel env1 env2 → lookup env2 x = None → lookup env1 x = None.
  Proof.
    intros Her.
    revert x.
    induction Her.
    - intros ??; rewrite lookup_nil; congruence.
    - intros z Hz.
      destruct z; simpl; [|eauto; fail].
      inversion Hz.
  Qed.

  Lemma env_rel_nil : env_rel nil nil.
  Proof. apply Forall2_nil. Qed.

  Lemma env_rel_cons a env b env' : P a b → env_rel env env' → env_rel (a :: env) (b :: env').
  Proof. apply Forall2_cons; trivial. Qed.

  Lemma env_rel_inv_nil_l env : env_rel nil env → env = nil.
  Proof. inversion 1; trivial. Qed.

  Lemma env_rel_inv_nil_r env : env_rel env nil → env = nil.
  Proof. inversion 1; trivial. Qed.

  Lemma env_rel_inv_cons_l x env env' :
    env_rel (x :: env) env' → ∃ y env'', env' = y :: env'' ∧ P x y ∧ env_rel env env''.
  Proof. inversion 1; eauto. Qed.

  Lemma env_rel_inv_cons_r env x env' :
    env_rel env (x :: env') → ∃ y env'', env = y :: env'' ∧ P y x ∧ env_rel env'' env'.
  Proof. inversion 1; eauto. Qed.

End env_rel.

Section env_rel.
  Context {A} (P : A → A → Prop).

  Lemma env_rel_refl env : (∀ x, P x x) → env_rel P env env.
  Proof. intros HP; induction env; [apply env_rel_nil|apply env_rel_cons; auto]. Qed.

  Lemma env_rel_sym env env' : (∀ x y, P x y → P y x) → env_rel P env env' → env_rel P env' env.
  Proof.
    intros HP; revert env'; induction env as [|x env IHenv]; intros env' Hee.
    - apply env_rel_inv_nil_l in Hee as ->; apply env_rel_nil.
    - apply env_rel_inv_cons_l in Hee as (?&?&->&?&?).
      apply env_rel_cons; auto.
  Qed.

  Lemma env_rel_trans env env' env'' :
    (∀ x y z, P x y → P y z → P x z) →
    env_rel P env env' → env_rel P env' env'' → env_rel P env env''.
  Proof.
    intros HP; revert env' env''; induction env as [|x env IHenv]; intros env' env'' Hee' He'e''.
    - apply env_rel_inv_nil_l in Hee' as ->.
      apply env_rel_inv_nil_l in He'e'' as ->.
      apply env_rel_nil.
    - apply env_rel_inv_cons_l in Hee' as (?&?&->&?&?).
      apply env_rel_inv_cons_l in He'e'' as (?&?&->&?&?).
      apply env_rel_cons; eauto.
  Qed.

End env_rel.

Lemma env_rel_impl {A B} (P Q : A → B → Prop) env env' :
  (∀ x y, P x y → Q x y) → env_rel P env env' → env_rel Q env env'.
Proof.
  intros HP; revert env'; induction env as [|x env IHenv]; intros env' Hee.
  - apply env_rel_inv_nil_l in Hee as ->; apply env_rel_nil.
  - apply env_rel_inv_cons_l in Hee as (?&?&->&?&?).
    apply env_rel_cons; auto.
Qed.
