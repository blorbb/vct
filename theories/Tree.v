From CegarTableaux Require Kripke Valuation.
From CegarTableaux Require Import ImportStd.


(* Rocq does not generate a useful induction theorem. Need to make our own. *)
Unset Elimination Schemes.

(** A Kripke model with a tree structure. *)
Inductive t :=
  | make
      (V : Valuation.t)
      (* A list of sub-trees reachable from here. *)
      (children : list t).

Set Elimination Schemes.

Definition t_ind :
  forall P : t -> Prop,
  (forall V children, List.Forall P children -> P (make V children)) ->
  forall tr, P tr.
Proof.
  intros P H.
  (* Assume the goal as IH, but argument 1 (tr) must be decreasing. *)
  fix IH 1.
  intros [V children].
  apply H.
  induction children; auto.
Qed.

Definition empty := make [] [].

Definition cons_child tree child :=
  match tree with
  | make V children => make V (child :: children)
  end.

(* The tree defines a Kripke model. *)

Definition valuation (tree : t) (atm : nat) : Prop :=
  match tree with
  | make V _ => Valuation.forces_atm V atm = true
  end.


Definition relation (w0 w1 : t) : Prop :=
  match w0 with
  | make _ children => List.In w1 children
  end.

Definition as_kripke : @Kripke.t t relation := Kripke.make t relation valuation.
