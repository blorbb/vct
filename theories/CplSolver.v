(** An assumed classical SAT-solver oracle.

    We define [Parameter] types and functions which must be filled in during
    program extraction. They must also satisfy the axioms as defined in
    [solver_axioms].

    See the Extract module for details about our Minisat implementation. *)

From CegarTableaux Require CplClause Assumptions Lit Cnf Valuation.
From CegarTableaux Require Import ImportStd Utils ListExt.
From CegarTableaux.CplSolver Require Solution.


(** A (possibly stateful) classical SAT-solver oracle. *)
Parameter t : Type.


(** Creates a new SAT-solver.

    Even though the solver appears immutable, it is better to still make
    this a function instead of a constant or else this is a reference to
    an always-invalid solver that slowly holds more and more clauses
    unnecessarily. *)
Parameter make : unit -> t.


(** Add a clause to the solver, returning the new solver. *)
Parameter add_clause : t -> CplClause.t -> t.


(** Determines the satisfiability of the provided solver state under a set of
    unit assumptions.

    The solver state is unchanged by this function call. *)
Parameter solve_with_assumptions : t -> Assumptions.t -> Solution.t.


(** Create a new solver with the provided CNF clauses.

    This must be a [fold_right] instead of [fold_left] (though the latter
    would be better due to being tail recursive) because of some proofs
    of [Solver.Search] requiring that the cpls of [w0] are exactly the
    clauses of the cpl solver [s0]. But the conflict sets are [cons]ed
    on to the head of the cpls of [w0] _and_ [cons]ed to the clauses
    of [s0], so only [fold_right] is the correct definition here.

    FIXME: If the above is a performance issue, fix up the proofs and 
    switch this to a [fold_left] instead. *)
Definition make_with_clauses (clauses : Cnf.t) : t :=
  List.fold_right (flip add_clause) (make tt) clauses.


(** * Axioms *)

(** All clauses which have been added to this solver.

    This parameter is not (and should not) be used by the algorithm
    implementation. It is only used to describe the axioms of the solver. *)
Parameter clauses_of : t -> Cnf.t.


(** The assumptions and clauses of the solver combined.

    Returns the equivalent CNF formula that the solver is determining the
    satisfiability for (including the unit assumptions). *)
Definition solved_clauses (s : t) (A : Assumptions.t) : Cnf.t :=
  Cnf.from_assumptions A ++ clauses_of s.


(** Set of atoms that are in the solver or assumptions. *)
Definition atms_of (s : t) (A : Assumptions.t) : list nat :=
  Cnf.atms_of (solved_clauses s A).


(** Returns every possible valuation that can be created by the atoms of the
    solver and assumptions. *)
Definition every_valuation (s : t) (A : Assumptions.t) : list Valuation.t :=
  Valuation.every_valuation_of_atms (atms_of s A).


Definition every_sat_valuation (s : t) (A : Assumptions.t) : list Valuation.t :=
  List.filter (fun val => Cnf.cpl_forceb val (solved_clauses s A)) (every_valuation s A).


Definition atm_in (p : nat) (s : t) (A : Assumptions.t) : Prop :=
  Cnf.atm_in p (solved_clauses s A).


(** Whether a clause does not introduce new atoms to the solver. *)
Definition clause_atms_incl (clause : CplClause.t) (s : t) (A : Assumptions.t) : Prop :=
  forall p, CplClause.atm_in p clause -> atm_in p s A.

Arguments clause_atms_incl clause s A /.


(** The valuation returned by a satisfiable result is [clash_free]. *)
Axiom valuation_clash_free : forall s A V,
  Solution.Sat V = solve_with_assumptions s A ->
  Valuation.clash_free V.

(** Every atom in the valuation is an atom in the solver or assumptions. *)
Axiom valuation_in_clauses : forall s A V,
  Solution.Sat V = solve_with_assumptions s A ->
  forall p, List.In p V -> atm_in p s A.

(** The unsatisfiable core is a subset of the unit assumptions. *)
Axiom core_subset_assumptions : forall s A core,
  Solution.Unsat core = solve_with_assumptions s A ->
  List.incl core A.

(** The solver + unsatisfiable core is still unsatisfiable. *)
Axiom solution_soundness : forall s A core,
  Solution.Unsat core = solve_with_assumptions s A ->
  Cnf.unsatisfiable (solved_clauses s core).

(** The valuation satisfies the solver clauses. *)
Axiom solution_completeness : forall s A V,
  Solution.Sat V = solve_with_assumptions s A ->
  Cnf.cpl_forceb V (solved_clauses s A) = true.

(** The empty SAT-solver contains no clauses. *)
Axiom make_is_empty : clauses_of (make tt) = [].
Global Hint Rewrite make_is_empty : ct.

(** [add_clause solver clause] correctly adds [clause] to the
    clauses of [solver]. *)
Axiom add_clause_cons : forall s (clause : CplClause.t),
  clauses_of (add_clause s clause) = clause :: clauses_of s.
Global Hint Rewrite add_clause_cons : ct.

(** The clauses that the solver will hold from a [List.fold_right] of clauses. *)
Lemma clauses_of_fold_right : forall s (clauses : list CplClause.t),
  clauses_of (List.fold_right (flip add_clause) s clauses) = clauses ++ clauses_of s.
Proof with try easy.
  intros s clauses. revert s.
  induction clauses as [|h t IH]; intros s.
  - reflexivity.
  - cbn. unfold flip in *. rewrite add_clause_cons. congruence.
Qed. Global Hint Rewrite clauses_of_fold_right : ct.


Lemma clauses_of_make_with_clauses : forall (phi : Cnf.t),
  clauses_of (make_with_clauses phi) = phi.
Proof.
  intros phi. unfold make_with_clauses.
  rewrite clauses_of_fold_right, make_is_empty.
  now rewrite List.app_nil_r.
Qed. Global Hint Resolve clauses_of_make_with_clauses : ct.


Lemma add_clause_incl : forall s clause,
  List.incl (clauses_of s) (clauses_of (add_clause s clause)).
Proof.
  intros s cl cl' Hcl_in.
  rewrite add_clause_cons. now right.
Qed. Global Hint Resolve add_clause_incl : ct.


Corollary add_clause_incl_A : forall s A cl,
  List.incl (solved_clauses s A) (solved_clauses (add_clause s cl) A).
Proof.
  intros s A cl cl' Hcl_in.
  unfold solved_clauses in *.
  rewrite List.in_app_iff in *. destruct Hcl_in as [Hcl_in_A | Hcl_in_c].
  - now left.
  - right. now apply add_clause_incl.
Qed. Global Hint Resolve add_clause_incl_A : ct.


Lemma atms_of_nodup : forall s A, List.NoDup (atms_of s A).
Proof.
  intros. unfold atms_of, Cnf.atms_of. apply List.NoDup_nodup.
Qed. Global Hint Resolve atms_of_nodup : ct.


Lemma every_valuation_nodup : forall s A, NoDupA Valuation.eq (every_valuation s A).
Proof.
  intros. apply Valuation.every_valuation_unique, atms_of_nodup.
Qed. Global Hint Resolve every_valuation_nodup : ct.


Corollary every_sat_valuation_nodup : forall s A, NoDupA Valuation.eq (every_sat_valuation s A).
Proof.
  intros. apply NoDupA_filter; auto with typeclass_instances.
  apply every_valuation_nodup.
Qed. Global Hint Resolve every_sat_valuation_nodup : ct.


(** A satisfiable valuation is in [every_valuation] of the solver. *)
Lemma valuation_in_every_valuation_of :
  forall (s : t) (A : Assumptions.t) (V : Valuation.t),
  Solution.Sat V = solve_with_assumptions s A ->
  Valuation.val_in_vals V (every_valuation s A).
Proof with auto.
  intros s A V Hsat.
  unfold every_valuation, atms_of.
  set (atms := Cnf.atms_of _).
  pose proof (valuation_clash_free _ _ _ Hsat) as Hcf.
  apply Valuation.val_with_atms_in_every_val...
  intros p Hp_in. apply Cnf.in_atms_of.
  apply valuation_in_clauses with (V := V)...
Qed.


Lemma valuation_in_every_sat_valuation :
  forall s A V,
  Solution.Sat V = solve_with_assumptions s A ->
  Valuation.val_in_vals V (every_sat_valuation s A).
Proof with auto.
  intros solver assumptions val Hsat.
  unfold every_sat_valuation, Valuation.val_in_vals.
  apply filter_InA; try apply Cnf.proper_cpl_forceb. split.
  - now apply valuation_in_every_valuation_of.
  - now apply solution_completeness.
Qed.


(** A solver with an added clause that contains no new atoms has the same set of atoms *)
Lemma add_no_new_atms :
  forall (s : t) (A : Assumptions.t) (clause : CplClause.t),
  clause_atms_incl clause s A ->
  Permutation (atms_of s A) (atms_of (add_clause s clause) A).
Proof with auto.
  intros s A clause Hclause_incl.

  unfold atms_of, solved_clauses in *.
  rewrite add_clause_cons.

  apply NoDup_Permutation.
  - apply List.NoDup_nodup.
  - apply List.NoDup_nodup.
  - intro p. split.
    (* in assumptions ++ clauses -> in assumptions ++ new_clause :: clauses *)
    + intro Hp_in_solver.
      (* simplify nodup and flatmap *)
      apply List.nodup_In. apply List.nodup_In in Hp_in_solver.
      apply List.in_flat_map. apply List.in_flat_map in Hp_in_solver.
      destruct Hp_in_solver as [clause' [Hclause_in_clauses Hx_in_clause]].
      exists clause'. split...

      (* in a ++ b -> in a ++ c :: b *)
      rewrite List.in_app_iff in Hclause_in_clauses.
      destruct Hclause_in_clauses as [Hclause_in_assumps | Hclause_in_solver].
      * apply List.in_app_iff. now left.
      * apply List.in_app_iff. right. now apply List.in_cons.
    (* in assumptions ++ clauses <- in assumptions ++ new_clause :: clauses *)
    + intro Hp_in_solver'.
      (* simplify nodup and flatmap *)
      apply List.nodup_In in Hp_in_solver'.
      apply List.in_flat_map in Hp_in_solver'.
      destruct Hp_in_solver' as [clause' [Hclause_in_clauses Hx_in_clause]].

      (* split into 3 cases, two are almost identical, so reorder to simplify *)
      rewrite List.in_app_iff in Hclause_in_clauses. cbn in Hclause_in_clauses.
      apply or_comm, or_assoc in Hclause_in_clauses.
      destruct Hclause_in_clauses as [Heq_new | Hin_existing].
      (* p in new clause *)
      * subst clause'. unfold In in Hclause_incl.
        apply Cnf.in_atms_of. apply Hclause_incl.
        cbn. assumption.
      (* p in solver or assumptions *)
      * apply List.nodup_In. apply List.in_flat_map.
        exists clause'. split... apply List.in_app_iff.
        intuition.
Qed. Global Hint Resolve add_no_new_atms : ct.


(** Adds a list of literals interpreted as a conflict set.

    [cs] should be a subset of a previous valuation.
    [add_conflict_set] will add a clause requiring that at least one of these
    literals must be different if the next solution is also satisfiable. *)
Definition add_conflict_set s cs := add_clause s (List.map Lit.Neg cs).


(** If [V] = solution of [s] and [s'] contains the conflict set
    as one of it's clauses, [V] cannot be one of the possible valuations. *)
Lemma refined_solver_diff_val : forall s A V cs s',
  Solution.Sat V = solve_with_assumptions s A ->
  List.incl cs V ->
  cs <> [] ->
  List.In (List.map Lit.Neg cs) (clauses_of s') ->
  ~ Valuation.val_in_vals V (every_sat_valuation s' A).
Proof with auto with typeclass_instances; try easy.
  (* TODO: this is very forward proof-y, can probably simplify *)
  intros s A V cs s' HV Hcs_incl Hcs_ne Hcs_in_s' HV_in.
  unfold Valuation.val_in_vals, every_sat_valuation in HV_in.
  apply filter_InA in HV_in...
  destruct HV_in as [HV_in HV_force].
  unfold Cnf.cpl_forceb, solved_clauses in HV_force.
  rewrite List.forallb_forall in HV_force.
  specialize (HV_force (List.map Lit.Neg cs)).
  forward HV_force. { apply List.in_app_iff. now right. }

  unfold CplClause.cpl_forceb in HV_force.
  rewrite List.existsb_exists in HV_force.
  destruct HV_force as [l [Hl_in HV_force_l]].
  apply List.in_map_iff in Hl_in. destruct Hl_in as [p [Hpl Hp_in]]. subst.
  cbn in HV_force_l. rewrite negb_exb_forallb in HV_force_l.
  rewrite List.forallb_forall in HV_force_l.
  specialize (HV_force_l p).
  forward HV_force_l by now apply Hcs_incl.
  rewrite Nat.eqb_refl in HV_force_l.
  now apply Bool.no_fixpoint_negb in HV_force_l.
Qed.


(** If two solvers have the same set of atoms, they must have the same set
    of possible valuations. *)
Lemma same_atms_valuation_set :
  forall (s s' : t) (A : Assumptions.t),
  Permutation (atms_of s A) (atms_of s' A) ->
  PermutationA Valuation.eq (every_valuation s A) (every_valuation s' A).
Proof.
  intros s s' A Hatms_perm.
  unfold every_valuation. now apply Valuation.every_valuation_perm.
Qed.


(** Adding an extra clause only restricts the possible sat valuations. *)
Lemma refined_solver_sat_vals_subset : forall s A clause s',
  clause_atms_incl clause s A ->
  s' = add_clause s clause ->
  inclA Valuation.eq (every_sat_valuation s' A) (every_sat_valuation s A).
Proof with auto using Valuation.eq_equivalence.
  intros s A clause s' Hclause Hs' V HV_in_s'.
  unfold every_sat_valuation in *.

  rewrite filter_InA in *; try apply Cnf.proper_cpl_forceb.
  split.
  - apply PermutationA_inA with (l := (every_valuation s' A))...
    + apply same_atms_valuation_set.
      symmetry. subst s'. now apply add_no_new_atms.
    + exact (proj1 (HV_in_s')).
  - destruct HV_in_s' as [HV_in_s' HV_force_s'].
    unfold Cnf.cpl_forceb in *. rewrite List.forallb_forall in *.
    intros cl Hcl. apply HV_force_s'.
    subst s'. now apply add_clause_incl_A.
Qed.
