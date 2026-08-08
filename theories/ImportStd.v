(** Common standard library imports. *)

From Stdlib Require List.
Export List.ListNotations.
Open Scope list_scope.
From Stdlib Require Export
  Relations Program Wellfounded
  Lia RelationClasses SetoidList Permutation SetoidPermutation
  FunInd Recdef PeanoNat Nat Program.Wf Classical Zify.
From Equations Require Export Equations.
Require Export Equations.Prop.Logic.

(** Use booleans as Prop *)
Coercion is_true : bool >-> Sortclass.
(** Add [=] before a tactic to unfold [is_true], sometimes needed to work with
    stdlib lemmas that usually use [= true] instead. *)
Tactic Notation "=" tactic(H) := unfold is_true in *; H.

Create HintDb ct.
Create Rewrite HintDb ct.

From Vct Require Atom.
Export Atom.Notations.
Open Scope atom_scope.

From Vct Require Export Tactics ListExt.

Hint Rewrite
  Exists_cons Forall_cons_iff
  Exists_app Forall_app
  Exists_nil Forall_nil_iff : list.

Lemma or_false_l : forall P, P \/ False <-> P.
Proof. tauto. Qed.
Lemma or_false_r : forall P, False \/ P <-> P.
Proof. tauto. Qed.
Lemma and_true_l : forall P, P /\ True <-> P.
Proof. tauto. Qed.
Lemma and_true_r : forall P, True /\ P <-> P.
Proof. tauto. Qed.
Lemma imp_false_r : forall P, (False -> P) <-> True.
Proof. tauto. Qed.
Lemma imp_true_r : forall P, (True -> P) <-> P.
Proof. tauto. Qed.
Lemma imp_true_l : forall P, (P -> True) <-> True.
Proof. tauto. Qed.
Lemma imp_true_l_forall : forall {A} P, (forall (a : A), P a -> True) <-> True. (* common *)
Proof. tauto. Qed.
Lemma not_false : ~ False <-> True.
Proof. tauto. Qed.
Lemma not_true : ~ True <-> False.
Proof. tauto. Qed.
Lemma eq_true : forall {A} (a : A), a = a <-> True.
Proof. tauto. Qed.

Create Rewrite HintDb prop.
Hint Rewrite or_false_l or_false_r and_true_l and_true_r imp_false_r imp_true_r imp_true_l @imp_true_l_forall not_false not_true @eq_true : prop.

(* Rewriting bool expressions to props *)
Create Rewrite HintDb bool.
Hint Rewrite
  Bool.andb_true_iff Bool.andb_false_iff
  Bool.orb_true_iff Bool.orb_false_iff
  Bool.negb_true_iff Bool.negb_false_iff
  : bool.

(** Function pipeline operator *)
Notation "x |> f" := (f x) (at level 51, left associativity, only parsing).


Definition refl_closure {W} (R : relation W) : relation W :=
  fun w0 w1 => R w0 w1 \/ w0 = w1.

Global Instance refl_closure_refl : forall {W} (R : relation W), Reflexive (refl_closure R).
Proof. intros W R w. unfold refl_closure. now right. Qed.
