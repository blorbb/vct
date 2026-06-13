From CegarTableaux Require Lit Kripke CplClause BoxClause DiaClause.
From CegarTableaux Require Import ImportStd Utils.

(** An MCNF clause with an arbitrary number of boxes. *)
Inductive t : Type :=
  | Cpl (cpl : CplClause.t)
  | Box (box : BoxClause.t)
  | Dia (dia : DiaClause.t)
  (* new modal context: []phi *)
  | Ctx (phi : t).


Fixpoint force {W} {R} (M : @Kripke.t W R) (w0 : W) (phi : t) : Prop :=
  match phi with
  | Cpl A => CplClause.force M w0 A
  | Box A => BoxClause.force M w0 A
  | Dia A => DiaClause.force M w0 A
  | Ctx A => forall w1, R w0 w1 -> force M w1 A
  end.


Fixpoint atm_in (x : nat) (phi : t) : Prop :=
  match phi with
  | Cpl A => CplClause.atm_in x A
  | Box A => BoxClause.atm_in x A
  | Dia A => DiaClause.atm_in x A
  | Ctx ctx => atm_in x ctx
  end.


Definition agree {W} {R} (phi : t) (M M' : @Kripke.t W R) : Prop :=
  forall (w : W) (x : nat), atm_in x phi -> (Kripke.valuation M w x <-> Kripke.valuation M' w x).


Lemma meaningful_valuations :
  forall {W} {R} (M M' : @Kripke.t W R) (phi : t) (w0 : W),
  agree phi M M' -> (force M w0 phi <-> force M' w0 phi).
Proof with simpl; auto.
  intros W R M M' phi w0 Hagree.
  revert w0.

  induction phi as
    [ A
    | A
    | A
    | A IHA
    ]; intro w0.

  - apply CplClause.meaningful_valuations...
  - apply BoxClause.meaningful_valuations...
  - apply DiaClause.meaningful_valuations...

  (* context *)
  - simpl. split.
    + intros HM_force w1 HR_w1.
      specialize (HM_force w1 HR_w1).
      destruct IHA with (w0 := w1)...

    + intros HM'_force w1 HR_w1.
      specialize (HM'_force w1 HR_w1).
      destruct IHA with (w0 := w1)...
Qed.
