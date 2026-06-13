From CegarTableaux Require Lit.

(** A list of unit assumptions. *)
Definition t := list Lit.t.


Definition atm_in (t : t) (p : nat) : Prop := List.In p (List.map Lit.atm t).
