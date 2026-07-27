(** CEGARBox decision procedure.

    The algorithm and variants are implemented in the modules [Spec], [TailRec],
    [NoModel], [Cached]. This module contains some basic lemmas required for
    their definition (i.e. their termination). *)


From Vct Require CplSolver Lit Mcnf Assumptions Valuation Tree.
From Vct Require Export ImportStd.
From Vct.Solver Require Export McnfExt.
From Vct.Solver Require Derivation.


(** Default auto-solver simplifies a bit too much. *)
#[export] Obligation Tactic := intros; try solve [ cbn; auto ].


(** CONVENTIONS: l<n> means the local clauses at world n,
    mc<n> means the whole modal context chain starting from n onwards. *)

(** When proving termination / obligations, Equations doesn't keep all
    information about which specific branch is being taken. The [inspect]
    function and [eqn:Heqn] adds hypotheses to the context about which
    context was taken. This is only necessary for hypotheses needed
    for the obligations, as using [funelim] correctly keeps information
    about the branches taken. *)
Notation "x 'eqn' ':' p" := (exist _ x p) (only parsing, at level 20).


(** * Measurement *)

(** Lexicographic ordering of a pair of naturals. *)
Definition lexnat2_lt : nat * nat -> nat * nat -> Prop :=
  slexprod _ _ lt lt.

(** [lexnat2_lt] is well-founded. *)
Instance lexnat2_lt_wf : WellFounded lexnat2_lt.
Proof.
  unfold lexnat2_lt.
  apply wf_slexprod; apply Wf_nat.lt_wf.
Qed.


Lemma decreasing_sat_vals : forall s0 A mc0 V c jump_core,
  CplSolver.solve_with_assumptions s0 A = CplSolution.Sat V ->
  Valuation.forces_atm V c ->
  let cs := conflict_set_of mc0 V c jump_core in
  let s0' := CplSolver.add_conflict_set s0 cs in
  (List.length (CplSolver.every_sat_valuation s0' A) <
  List.length (CplSolver.every_sat_valuation s0 A))%nat.
Proof with auto with typeclass_instances datatypes ct; try lia.
  intros * HV_sat Hforce_c cs s0'.
  set (s0'_sats := CplSolver.every_sat_valuation s0' A) in *.
  set (s0_sats := CplSolver.every_sat_valuation s0 A) in *.

  assert (inclA Valuation.eq s0'_sats s0_sats) as Hincl. {
    apply CplSolver.refined_solver_sat_vals_subset with (clause := List.map Lit.Neg cs).
    - apply val_subset_no_new_atms with (V := V)...
      apply conflict_set_incl_val with (s := s0) (A := A)...
    - subst s0'. reflexivity.
  }

  apply Nat.le_neq. split.
  - apply NoDupA_incl_length with (eqA := Valuation.eq)...
    apply CplSolver.every_sat_valuation_nodup.
  - intro Hlen.

    apply CplSolver.refined_solver_diff_val with A V cs s0'.
    + apply conflict_set_incl_val with s0 A...
    + subst cs. unfold conflict_set_of.
      discriminate.
    + subst s0'. unfold CplSolver.add_conflict_set. rewrite CplSolver.add_clause_cons.
      now left.
    + apply PermutationA_inA with (l := s0_sats)...
      2: { now apply CplSolver.valuation_in_every_sat_valuation. }
      subst s0_sats s0'_sats. apply NoDup_PermutationA_bis...
      apply NoDupA_length_incl...
Qed.


(** For proofs, we don't want to write [tableau mc0 (cplsolver_mcnf mc0)] every time.

    This notation can be seen as expanding [$mc0] to [mc0 (cplsolver_mcnf mc0)]. *)
Notation "fn $ var" := (fn var (cplsolver_mcnf var)) (at level 10, left associativity).
