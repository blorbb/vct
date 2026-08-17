From Vct Require Kripke Valuation.
From Vct Require Import ImportStd.

Scheme All for list.

(** A Kripke model with a tree structure. *)
Inductive t :=
  | make
      (V : Valuation.t)
      (* A list of sub-trees reachable from here. *)
      (children : list t).


Definition empty := make [] [].

Definition cons_child tree child :=
  match tree with
  | make V children => make V (child :: children)
  end.

(* The tree defines a Kripke model. *)

Definition valuation (tree : t) (atm : Atom.t) : Prop :=
  match tree with
  | make V _ => Valuation.forces_atm V atm
  end.


Definition R (w0 w1 : t) : Prop :=
  match w0 with
  | make _ children => List.In w1 children
  end.

Definition R_kt := refl_closure R.

Global Instance R_kt_refl : Reflexive R_kt := _.

Definition as_k : @Kripke.t t R := Kripke.make t R valuation.
Definition as_kt : @Kripke.t t R_kt := Kripke.to_kt as_k.
