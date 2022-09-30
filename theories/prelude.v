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
