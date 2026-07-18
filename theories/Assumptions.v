From CegarTableaux Require Import ImportStd.
From CegarTableaux Require Lit.

(** A list of unit assumptions. *)
Definition t := list Lit.t.


Definition atm_in (p : Atom.t) (phi : t) : Prop := List.In p (List.map Lit.atm phi).

Arguments atm_in p phi /.
