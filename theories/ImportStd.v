(** Common standard library imports. *)

From Stdlib Require List.
Export List.ListNotations.
Open Scope list_scope.
From Stdlib Require Export
  Relations Program Wellfounded
  Lia RelationClasses SetoidList Permutation SetoidPermutation
  FunInd Recdef PeanoNat Nat Program.Wf Classical.
From Equations Require Export Equations.
Require Export Equations.Prop.Logic.

(* Use booleans as Prop *)
Coercion is_true : bool >-> Sortclass.

Create HintDb ct.
Create Rewrite HintDb ct.

From CegarTableaux Require Export Tactics ListExt.

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
Lemma idem_f : False /\ False <-> False.
Proof. tauto. Qed.
Lemma idem_t : True /\ True <-> True.
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
Lemma not_true : ~ False <-> True.
Proof. tauto. Qed.

Create Rewrite HintDb prop.
Hint Rewrite or_false_l or_false_r and_true_l and_true_r idem_f idem_t imp_false_r imp_true_r imp_true_l @imp_true_l_forall not_false not_true : prop.


(** Function pipeline operator *)
Definition apply {A B} (x : A) (f : A -> B) := f x.
Arguments apply {A B} x f /.
Infix "|>" := apply (at level 51, left associativity).


Lemma negb_exb_forallb : forall {A} (f : A -> bool) (l : list A),
  negb (List.existsb f l) = List.forallb (fun a => negb (f a)) l.
Proof.
  intros A f l.
  induction l.
  - cbn. reflexivity.
  - cbn. rewrite Bool.negb_orb, IHl. reflexivity.
Qed.


Lemma nat_leb_total : forall n m, (n <=? m) = true \/ (m <=? n) = true.
Proof.
  intros n m. destruct (Nat.leb_spec n m).
  - now left.
  - right. rewrite Nat.leb_le. now apply Nat.lt_le_incl.
Qed.
