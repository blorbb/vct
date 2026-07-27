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


Definition relation (w0 w1 : t) : Prop :=
  match w0 with
  | make _ children => List.In w1 children
  end.

Definition relation_refl (w0 w1 : t) : Prop :=
  w0 = w1 \/
  match w0 with
  | make _ children => List.In w1 children
  end.

Global Instance relation_refl_refl : Reflexive relation_refl.
Proof. now left. Qed.

Definition as_kripke : @Kripke.t t relation := Kripke.make t relation valuation.
Definition as_refl : @Kripke.t t relation_refl := Kripke.make t relation_refl valuation.
