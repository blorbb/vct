From CegarTableaux Require Import ImportStd.
From CegarTableaux Require Lit.

From stdpp Require Import countable.

(** A list of unit assumptions. *)
Definition t := list Lit.t.


Definition atm_in (p : nat) (phi : t) : Prop := List.In p (List.map Lit.atm phi).

Arguments atm_in p phi /.

Global Instance eq_decision : EqDecision t := _.

Global Instance countable : Countable t := _.
