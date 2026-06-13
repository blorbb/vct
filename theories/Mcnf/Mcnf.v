(** MCNF type with basic lemmas and definitions *)

From CegarTableaux Require Lit Nnf Kripke Mclause.
From CegarTableaux Require Import ImportStd Utils.


(** An MCNF formula, a list of modal clauses. *)
Definition t := list Mclause.t.


Fixpoint force {W} {R} (M : @Kripke.t W R) (w0 : W) (phi : t) : Prop :=
  match phi with
  | [] => True
  | head :: tail => Mclause.force M w0 head /\ force M w0 tail
  end.


Definition satisfiable (phi : t) : Prop :=
  exists W R (M : @Kripke.t W R) (w0 : W), force M w0 phi.


Fixpoint atm_in (p : nat) (phi : t) : Prop :=
  match phi with
  | [] => False
  | head :: tail => Mclause.atm_in p head \/ atm_in p tail
  end.


(** Mini lemmas useful for simplifications. *)
Section Simplify.
  Lemma in_mcnf_or :
    forall (A B : t) (p : nat),
    atm_in p (A ++ B) <-> atm_in p A \/ atm_in p B .
  Proof.
    intros A B p.
    induction A as [| head tail IHl]; simpl in *; tauto.
  Qed.


  Lemma in_ctx_iff_in_mcnf :
    forall (phi : t) (p : nat),
    atm_in p (List.map Mclause.Ctx phi) <-> atm_in p phi.
  Proof.
    intros phi p.
    induction phi as [| head tail IHphi]; simpl in *; tauto.
  Qed.


  Lemma mcnf_force_and :
    forall {W} {R} (M : @Kripke.t W R) (w0 : W) (A B : t),
    force M w0 (A ++ B) <-> force M w0 A /\ force M w0 B.
  Proof.
    intros W R M w0 A B.
    split.
    - intro Hforce_lr.
      induction A as [| head tail IHl]; simpl in *; tauto.
    - intros [Hforce_l Hforce_r].
      induction A as [| head tail IHl]; simpl in *; tauto.
  Qed.


  Lemma w0_force_ctx_iff_w1_force_phi :
    forall {W} {R} (M : @Kripke.t W R) (w0 : W) (phi : t),
      force M w0 (List.map Mclause.Ctx phi) <->
      (forall (w1 : W), R w0 w1 -> force M w1 phi).
  Proof with simpl; auto.
    intros W R M w0 phi.
    induction phi as [| head tail IHphi].
    - simpl. tauto.
    - simpl in *. split.
      + intros [Hforce_w1 Hforce_ctx_tail] w1 Hrel_w1.
        split... apply IHphi...
      + intros Hw1_forces_head_tail.
        split.
        * intros w1 Hrel_w1.
          now apply Hw1_forces_head_tail.
        * apply IHphi. apply Hw1_forces_head_tail.
  Qed.
End Simplify.


Definition agree {W} {R} (phi : t) (M M' : @Kripke.t W R) : Prop :=
  forall (w0 : W) (p : nat), atm_in p phi -> (Kripke.valuation M w0 p <-> Kripke.valuation M' w0 p).


Lemma meaningful_valuations :
  forall {W} {R} (M M' : @Kripke.t W R) (phi : t) (w0 : W),
  agree phi M M' -> (force M w0 phi <-> force M' w0 phi).
Proof with simpl; auto.
  intros W R M M' phi w0 Hval.

  induction phi as [|head tail IHphi].
  - tauto.
  - assert (forall w' p, atm_in p tail -> Kripke.valuation M w' p <-> Kripke.valuation M' w' p) as Hval_tail.
    {
      intros w' p Hp_tail.
      apply Hval...
    }
    assert (forall w' p, Mclause.atm_in p head -> Kripke.valuation M w' p <-> Kripke.valuation M' w' p) as Hval_head.
    {
      intros w' p Hp_head.
      apply Hval...
    }

    rewrite (mcnf_force_and M w0 [head] tail).
    rewrite (mcnf_force_and M' w0 [head] tail).
    split.
    + intros [Hhead Htail].
      split.
      (* force head *)
      * simpl in *. split... destruct Hhead as [Hhead _].
        rewrite <- (Mclause.meaningful_valuations M M')...
      (* force tail by IH *)
      * apply IHphi...
    + intros [Hhead Htail].
      split.
      * simpl in *. split... destruct Hhead as [Hhead _].
        rewrite (Mclause.meaningful_valuations M M')...
      * apply IHphi...
Qed.
