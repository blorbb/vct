(** A closed CEGAR-Tableau derivation of unsatisfiability. *)

From Vct Require Mcnf Assumptions CplSolver Lclauses.
From Vct Require Import ImportStd.
From Vct.Solver Require Import McnfExt.


(** A closed tableau derivation.

    There are no constraints the values provided, so the inhabitance of this
    type is _not_ a proof of unsatisfiability. The necessary properties are
    described externally with [wf]. It is proven that these conditions are
    held by the solver and that having such conditions _is_ a proof of
    unsatisfiability. *)
Inductive t : Type :=
| Local (core : Assumptions.t)
| JumpRestart
  (** Valuation returned by a sat solver. *)
  (V : Valuation.t)
  (** Failed jump. *)
  (failed_dia : DiaClause.t)
  (jump_cct : t)
  (** Failed restart *)
  (rs_cct : t).


(* In the jump restart case, gets the core of the restart tableau.
    The jump core has already been used to do the restart (making the
    conflict set). The restart core is for the parent context to use. *)
Fixpoint get_core (t : t) :=
  match t with
  | Local core => core
  | JumpRestart _ _ _ rs_cct => get_core rs_cct
  end.


(** Conditions for a well-formed cct. *)
Inductive wf : t -> Mcnf.t -> Assumptions.t -> Prop :=
| LocalCond : forall mc0 A core,
  List.incl core A ->
  Cnf.unsatisfiable (Cnf.from_assumptions core ++ Mcnf.fst_cpls mc0) ->
  wf (Local core) mc0 A
| JumpRestartCond : forall mc0 A V failed_dia jump_cct rs_cct,
  Cnf.cpl_forceb V (Cnf.from_assumptions A ++ Mcnf.fst_cpls mc0) ->
  List.In failed_dia (Mcnf.fst_dias mc0) ->
  Valuation.forces_atm V (fst failed_dia) ->
  (* Jump tableau also satisfies wf. *)
  wf jump_cct (Mcnf.next_mc mc0) (snd failed_dia :: fired_boxes mc0 V) ->
  (* Restart tableau also satisfies wf. *)
  wf rs_cct (Mcnf.add_cs mc0 ((fst failed_dia) :: box_culprits mc0 V (get_core jump_cct))) A ->
  wf (JumpRestart V failed_dia jump_cct rs_cct) mc0 A.


(** Example well-formed cct for the negation of the K axiom. *)
Section NegKEx.
  Local Definition p := Atom.one.
  Local Definition q := Atom.succ p.
  Local Definition n := Atom.succ q.
  Local Definition m := Atom.succ n.
  Local Notation "- p" := (Lit.Neg p) (at level 35).
  Local Notation "+ p" := (Lit.Pos p) (at level 35).

  Local Example wf_cct_neg_k :
    wf
      (JumpRestart [n] (n, -q)
        (Local [-q; +m; +p])
        (Local []))
      [ Lclauses.make [[+n]] [(n, +m); (n, +p)] [(n, -q)]
      ; Lclauses.make [[-m; -p; +q]] [] []]
      [].
  Proof.
    constructor; cbn.
    - auto.
    - now left.
    - auto.
    - constructor; cbn.
      + change (Valuation.forces_atm [n] n) with true. cbn. easy.
      + intros Hsat. unfold Cnf.satisfiable in Hsat. deex.
        autorewrite with ct prop in Hsat.
        intuition.
    - constructor.
      + easy.
      + unfold box_culprits. cbn.
        change (Valuation.forces_atm [n] n) with true. cbn.
        repeat rewrite Atom.eqb_refl, Bool.orb_true_r. cbn.
        intros Hsat. unfold Cnf.satisfiable in Hsat. deex.
        autorewrite with ct prop in Hsat.
        intuition.
  Qed.
End NegKEx.
