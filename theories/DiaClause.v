From CegarTableaux Require Lit BoxClause.
From CegarTableaux Require Import ImportStd.

(** An MCNF dia-clause [a -> <>b].

    The antecedent is always a positive literal. *)
Definition t : Type := nat * Lit.t.


Definition force {W} {R} (M : @Kripke.t W R) (w0 : W) (phi : t) : Prop :=
  Kripke.valuation M w0 (fst phi) -> (exists w1, R w0 w1 /\ Lit.force M w1 (snd phi)).

Arguments force {W R} M w0 phi /.


Definition atm_in (p : nat) (phi : t) : Prop :=
  (p = fst phi) \/ (p = Lit.atm (snd phi)).

Arguments atm_in p phi /.


Definition agree {W} {R} (phi : t) (M M' : @Kripke.t W R) : Prop :=
  forall (w0 : W) (p : nat), atm_in p phi -> (Kripke.valuation M w0 p <-> Kripke.valuation M' w0 p).


Lemma meaningful_valuations :
  forall {W} {R} (M M' : @Kripke.t W R) (phi : t) (w0 : W),
  agree phi M M' -> (force M w0 phi <-> force M' w0 phi).
Proof with simpl; auto.
  intros W R M M' phi w0 Hagree. revert w0.

  assert (
    forall w0 l, atm_in (Lit.atm l) phi ->
    Lit.force M w0 l <-> Lit.force M' w0 l
  ) as Heq_lit.
  {
    intros w0' l Hlin.
    unfold agree in Hagree.
    destruct l as [p | p]; simpl; rewrite Hagree; tauto.
  }

  unfold force in *. split.
  - intros HM_force_a HM'_force_a.
    unfold agree in Hagree.
    rewrite <- Hagree in HM'_force_a...
    forward HM_force_a by assumption.
    destruct HM_force_a as [w1 [HM_R_w1 HM_force_b]].
    exists w1.
    split...
    apply Heq_lit...

  - intros HM'_force_a HM_force_a.
    unfold agree in Hagree.
    rewrite Hagree in HM_force_a...
    forward HM'_force_a by assumption.
    destruct HM'_force_a as [w1 [HM_R_w1 HM_force_b]].
    exists w1.
    split...
    apply Heq_lit...
Qed.


Definition max_atm (phi : t) : nat :=
  Nat.max (fst phi) (Lit.atm (snd phi)).


Lemma atm_le_max : forall (phi : t) (p : nat),
  atm_in p phi -> p <= (max_atm phi).
Proof. exact BoxClause.atm_le_max. Qed.
