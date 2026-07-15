From CegarTableaux Require Kripke Valuation.
From CegarTableaux Require Import ImportStd.

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

Definition valuation (tree : t) (atm : nat) : Prop :=
  match tree with
  | make V _ => Valuation.forces_atm V atm
  end.


Definition relation (w0 w1 : t) : Prop :=
  match w0 with
  | make _ children => List.In w1 children
  end.

Definition as_kripke : @Kripke.t t relation := Kripke.make t relation valuation.
