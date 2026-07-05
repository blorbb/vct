(** A concrete derivation of unsatisfiability. *)

From CegarTableaux Require Mcnf Assumptions CplSolver Lclauses.
From CegarTableaux Require Import ImportStd.
From CegarTableaux.Solver Require Import McnfExt.


(** A closed tableau derivation.

    There are no constraints the values provided, so the inhabitance of this
    type is _not_ a proof of unsatisfiability. The necessary properties are
    described externally with [conds]. It is proven that these conditions are
    held by the solver and that having such conditions _is_ a proof of
    unsatisfiability. *)
Inductive t : Type :=
| Id (core : Assumptions.t)
| JumpRestart
  (** Valuation returned by a sat solver. *)
  (V : Valuation.t)
  (** Failed jump. *)
  (failed_dia : DiaClause.t)
  (jump_deriv : t)
  (** Failed restart *)
  (rs_deriv : t).


(* In the jump restart case, gets the core of the restart tableau.
    The jump core has already been used to do the restart (making the
    conflict set). The restart core is for the parent context to use. *)
Fixpoint get_core (t : t) :=
  match t with
  | Id core => core
  | JumpRestart _ _ _ rs_deriv => get_core rs_deriv
  end.


Inductive conds : Mcnf.t -> Assumptions.t -> t -> Prop :=
| IdCond : forall mc0 A core, CplSolution.Unsat core = cpl_solve mc0 A -> conds mc0 A (Id core)
| JumpRestartCond : forall mc0 A V failed_dia jump_deriv rs_deriv,
  CplSolution.Sat V = cpl_solve mc0 A ->
  List.In failed_dia (first_dias mc0) ->
  Valuation.forces_atm V (fst failed_dia) = true ->
  (* Jump tableau also satisfies conds. *)
  conds (next_ctx mc0) (snd failed_dia :: fired_boxes mc0 V) jump_deriv ->
  (* Restart tableau also satisfies conds. *)
  conds (add_conflict_set mc0 (conflict_set_of mc0 V (fst failed_dia) (get_core jump_deriv))) A rs_deriv ->
  conds mc0 A (JumpRestart V failed_dia jump_deriv rs_deriv).
