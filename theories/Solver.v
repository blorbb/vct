From CegarTableaux.Solver Require Spec TailRec NoModel Cached Derivation Soundness Completeness.
From CegarTableaux.Solver Require Import McnfExt.
From CegarTableaux Require Import ImportStd.

Include Soundness.
Include Completeness.


Theorem solve_fml_sound_complete : forall phi,
  Spec.Solution.is_sat (Spec.solve_fml phi) <-> Fml.satisfiable phi.
Proof with try easy; auto.
  intros mc0. split.
  - apply solve_fml_complete_sat.
  - apply solve_fml_sound_contrapos.
Qed.


Theorem tailrec_solve_fml_sound_complete : forall phi,
  TailRec.Solution.is_sat (TailRec.solve_fml phi) <-> Fml.satisfiable phi.
Proof.
  unfold TailRec.solve_fml, TailRec.solve_mcnf.
  setoid_rewrite <- TailRec.tableau_spec.
  apply solve_fml_sound_complete.
Qed.


Theorem nomodel_solve_fml_sound_complete : forall phi,
  NoModel.Solution.is_sat (NoModel.solve_fml phi) <-> Fml.satisfiable phi.
Proof.
  setoid_rewrite NoModel.is_sat_spec. exact solve_fml_sound_complete.
Qed.


Theorem cached_solve_fml_sound_complete : forall phi,
  Cached.Solution.is_sat (Cached.solve_fml phi) <-> Fml.satisfiable phi.
Proof.
  intros phi.
  unfold Cached.solve_fml, Cached.solve_mcnf.
  setoid_rewrite Cached.tableau_sound_complete; auto with ct.
  rewrite sat_add_no_assumptions.
  rewrite Nnf.equisat_fml, Mcnf.equisat_nnf. reflexivity.
Qed.



(** Running [Print Assumptions solve_fml_sound_complete.]
    prints the following (slightly reformatted):

    [[
      Axioms:

      Classical_Prop.classic : forall P : Prop, P \/ ~ P
      FunctionalExtensionality.functional_extensionality_dep :
        forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
        (forall x : A, f x = g x) -> f = g

      CplSolver.t : Type
      CplSolver.make : unit -> CplSolver.t
      CplSolver.add_clause : CplSolver.t -> CplClause.t -> CplSolver.t
      CplSolver.solve_with_assumptions : CplSolver.t -> Assumptions.t -> CplSolution.t
      CplSolver.clauses_of : CplSolver.t -> Cnf.t

      CplSolver.make_is_empty : CplSolver.clauses_of (CplSolver.make tt) = nil
      CplSolver.add_clause_cons :
        forall (s : CplSolver.t) (clause : CplClause.t),
        CplSolver.clauses_of (CplSolver.add_clause s clause) = clause :: CplSolver.clauses_of s
      CplSolver.valuation_in_clauses :
        forall (s : CplSolver.t) (A : Assumptions.t) (V : Valuation.t),
        CplSolution.Sat V = CplSolver.solve_with_assumptions s A ->
        forall p : nat, List.In p V -> CplSolver.atm_in p s A
      CplSolver.valuation_clash_free :
        forall (s : CplSolver.t) (A : Assumptions.t) (V : Valuation.t),
        CplSolution.Sat V = CplSolver.solve_with_assumptions s A ->
        Valuation.clash_free V
      CplSolver.solution_soundness :
        forall (s : CplSolver.t) (A core : Assumptions.t),
        CplSolution.Unsat core = CplSolver.solve_with_assumptions s A ->
        Cnf.unsatisfiable (CplSolver.solved_clauses s core)
      CplSolver.solution_completeness :
        forall (s : CplSolver.t) (A : Assumptions.t) (V : Valuation.t),
        CplSolution.Sat V = CplSolver.solve_with_assumptions s A ->
        Cnf.cpl_forceb V (CplSolver.solved_clauses s A)
      CplSolver.core_subset_assumptions :
        forall (s : CplSolver.t) (A core : Assumptions.t),
        CplSolution.Unsat core = CplSolver.solve_with_assumptions s A ->
        List.incl core A
    ]] *)
