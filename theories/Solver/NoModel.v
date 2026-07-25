(** Does not construct a model/derivation. *)

From Vct.Solver Require Import SearchBasics.
From Vct.Solver Require Spec Soundness Completeness.


Module JumpSolution.
  Inductive t :=
    | Sat
    | Unsat (c : Atom.t) (core : Assumptions.t).


  Definition from_spec (s : Spec.JumpSolution.t) : t :=
    match s with
    | Spec.JumpSolution.Sat _ => Sat
    | Spec.JumpSolution.Unsat failed_dia core _ => Unsat (fst failed_dia) core
    end.
End JumpSolution.

Module Solution.
  Inductive t :=
    | Sat
    | Unsat (core : Assumptions.t).

  Definition is_sat t : bool :=
    match t with
    | Sat => true
    | Unsat _ => false
    end.

  Lemma is_sat_eq : forall (s : t), is_sat s <-> s = Sat.
  Proof. intro s. destruct s; easy. Qed.
  Global Hint Resolve is_sat_eq : ct.

  Definition from_spec (s : Spec.Solution.t) : t :=
    match s with
    | Spec.Solution.Sat _ => Sat
    | Spec.Solution.Unsat core _ => Unsat core
    end.
End Solution.

(** Tail recursive [tableau_jumps]. *)
Equations tableau_jumps
  (* Actual arguments. *)
  (V : Valuation.t)
  (l0 : Lclauses.t)
  (mc1 : Mcnf.t)
  (* The [tableau] function below with [mc1] and
    [s1 := CplSolver.make_with_clauses (first_cpls mc1)]. *)
  (next_tableau : Assumptions.t -> Solution.t)
  : JumpSolution.t
  by wf (List.length (Lclauses.dias l0)) lt
:=
(* Every fired child satisfied. *)
tableau_jumps V (Lclauses.make _ _ []) mc1 next_tableau :=
  JumpSolution.Sat;
tableau_jumps V (Lclauses.make cpls boxes ((c, d) :: dias')) mc1 next_tableau
with Valuation.forces_atm V c =>
  | false => tableau_jumps V (Lclauses.make cpls boxes dias') mc1 next_tableau
  | true with let fired_boxes :=
      boxes
      |> List.filter (fun '(a, b) => Valuation.forces_atm V a)
      |> List.map snd
    in next_tableau (d::fired_boxes) =>
      | Solution.Unsat core =>
        JumpSolution.Unsat c core
      | Solution.Sat =>
        tableau_jumps V (Lclauses.make cpls boxes dias') mc1 next_tableau
.
Fail Next Obligation.



(** Reproving this is much easier than proving the equivalence of tableau_jumps to the spec for now. *)
Lemma jump_c_forced : forall V l0 mc1 next_tableau c core,
  tableau_jumps V l0 mc1 next_tableau = JumpSolution.Unsat c core ->
  Valuation.forces_atm V c.
Proof with auto.
  intros * Hunsat. funelim (tableau_jumps V l0 mc1 next_tableau); rewrite <- Heqcall in Hunsat.
  - discriminate.
  - eapply H. exact Hunsat.
  - eapply H. exact Hunsat.
  - inversion Hunsat; subst. assumption.
Qed.


Equations tableau
  (mc0 : Mcnf.t)
  (s0 : CplSolver.t)
  (A : Assumptions.t)
  : Solution.t
  by wf (
    List.length mc0,
    List.length (CplSolver.every_sat_valuation s0 A)
  ) lexnat2_lt
:=
tableau mc0 s0 A
with inspect (CplSolver.solve_with_assumptions s0 A) := {
  | CplSolution.Unsat A' eqn:Hcsol_eq => Solution.Unsat A'
  | CplSolution.Sat V eqn:Hcsol_eq with mc0 =>
    | [] => Solution.Sat
    | (l0 :: mc1) with inspect (tableau_jumps V l0 mc1 (fun A' => tableau mc1 (cplsolver_mcnf mc1) A')) := {
      | JumpSolution.Sat eqn:Hj_eq => Solution.Sat
      | JumpSolution.Unsat c jump_core eqn:Hj_eq =>
        let conflict_set := conflict_set_of (l0::mc1) V c jump_core in
        let s0' := CplSolver.add_conflict_set s0 conflict_set in
        let mc0' := add_conflict_set (l0::mc1) conflict_set in
        tableau mc0' s0' A
    }
}.
Next Obligation.
  (* JUMP call measure decreasing. *)
  cbn in *.
  left. subst. cbn. auto.
Qed.
Next Obligation.
  (* RESTART call measure decreasing. *)
  destruct l0. right.
  apply decreasing_sat_vals; try easy.
  eapply jump_c_forced. exact Hj_eq.
Qed.
Fail Next Obligation.


(** Solve a formula by applying [tableau] with the correct arguments. *)
Definition solve_mcnf (mc0 : Mcnf.t) : Solution.t :=
  tableau mc0 (cplsolver_mcnf mc0) [].


(** Solve a [Fml.t] formula by converting first. *)
Definition solve_fml (phi : Fml.t) : Solution.t :=
  phi |> Nnf.from_fml |> Mcnf.from_nnf |> solve_mcnf.


Lemma tableau_jumps_spec_ind : forall V l0 mc1,
  (forall A, Solution.from_spec (Spec.tableau $mc1 A) = tableau $mc1 A) ->
  JumpSolution.from_spec (Spec.tableau_jumps V l0 mc1 (Spec.tableau $mc1)) = tableau_jumps V l0 mc1 (tableau $mc1).
Proof with try solve [ cbn in *; try easy; auto with ct datatypes ].
  intros * Hsol_match.
  funelim (Spec.tableau_jumps V l0 mc1 (Spec.tableau $mc1)).
  - cbn. now simp tableau_jumps.
  - simp tableau_jumps. unfold tableau_jumps_unfold_clause_2.
    rewrite Heq.
    apply H. apply Hsol_match.
  - simp tableau_jumps. unfold tableau_jumps_unfold_clause_2.
    rewrite Heq0. unfold tableau_jumps_unfold_clause_2_clause_2.

    set (fired_boxes := d::boxes |> List.filter (fun '(a, _) => Valuation.forces_atm V a) |> map snd) in *.
    specialize (Hsol_match fired_boxes).
    rewrite Heq in Hsol_match. cbn in Hsol_match.
    rewrite <- Hsol_match. reflexivity.

  (* TODO: both cases below are identical. *)
  - simp tableau_jumps. unfold tableau_jumps_unfold_clause_2.
    rewrite Heq1. unfold tableau_jumps_unfold_clause_2_clause_2.

    specialize (Hind Hsol_match).

    set (fired_boxes := d::boxes |> List.filter (fun '(a, _) => Valuation.forces_atm V a) |> map snd) in *.
    specialize (Hsol_match fired_boxes).
    rewrite Heq0 in Hsol_match. cbn in Hsol_match.
    rewrite <- Hsol_match.
    rewrite <- Hind. rewrite Heq. reflexivity.
  - simp tableau_jumps. unfold tableau_jumps_unfold_clause_2.
    rewrite Heq1. unfold tableau_jumps_unfold_clause_2_clause_2.

    specialize (Hind Hsol_match).

    set (fired_boxes := d::boxes |> List.filter (fun '(a, _) => Valuation.forces_atm V a) |> map snd) in *.
    specialize (Hsol_match fired_boxes).
    rewrite Heq0 in Hsol_match. cbn in Hsol_match.
    rewrite <- Hsol_match.
    rewrite <- Hind. rewrite Heq. reflexivity.
Qed.


Lemma tableau_spec : forall mc0 s0 A,
  Solution.from_spec (Spec.tableau mc0 s0 A) = tableau mc0 s0 A.
Proof with try easy; try congruence; auto.
  intros *.
  funelim (Spec.tableau mc0 s0 A).
  - clear H. simp tableau. unfold tableau_unfold_clause_1. cbn.
    dep_destruct (CplSolver.solve_with_assumptions s0 A) as Hs_eq...

  - clear H. simp tableau. unfold tableau_unfold_clause_1. cbn.
    dep_destruct (CplSolver.solve_with_assumptions s0 A) as Hs_eq...

  - clear H H0. simp tableau. unfold tableau_unfold_clause_1. cbn.

    dep_destruct (CplSolver.solve_with_assumptions s0 A) as Hs_eq...
    rewrite Hs_eq in Hcsol_eq. inv_clear Hcsol_eq.

    (* contradiction between Hj_eq and Hj_unsat *)
    eta.
    pose proof (tableau_jumps_spec_ind V l0 mc1 Hind) as Hj_matches.

    destruct (tableau_jumps V l0 mc1 _) eqn:Hj_unsat...
    rewrite Hj_eq in Hj_matches...

  - clear H0 H1.

    set (spec_call := Spec.tableau _ _ _) in *.
    simp tableau. cbn.
    dep_destruct (CplSolver.solve_with_assumptions s0 A) as Hs_eq...
    cbn -[add_conflict_set]. rewrite Hs_eq in Hcsol_eq. inversion_clear Hcsol_eq.
    eta.
    pose proof (tableau_jumps_spec_ind V l0 mc1 Hind) as Hj_matches.

    destruct (tableau_jumps V l0 mc1 _).
    + rewrite Hj_eq in Hj_matches...
    + rewrite Hj_eq in Hj_matches.
      cbn in Hj_matches. inv_clear Hj_matches.
      destruct spec_call...
Qed.


Lemma tableau_jumps_spec : forall V l0 mc1,
  JumpSolution.from_spec (Spec.tableau_jumps V l0 mc1 (Spec.tableau $mc1)) = tableau_jumps V l0 mc1 (tableau $mc1).
Proof with try easy.
  intros *.
  apply tableau_jumps_spec_ind.
  intro A. apply tableau_spec.
Qed.


Corollary is_sat_spec : forall mc0 s0 A,
  Solution.is_sat (tableau mc0 s0 A) = Spec.Solution.is_sat (Spec.tableau mc0 s0 A).
Proof.
  intros mc0 s0 A.
  rewrite <- (tableau_spec mc0 s0 A).
  destruct (Spec.tableau mc0 s0 A); easy.
Qed.


Theorem tableau_sound_complete : forall mc0 A,
  Solution.is_sat (tableau mc0 (cplsolver_mcnf mc0) A) <->
  Mcnf.satisfiable (add_assumptions mc0 A).
Proof.
  intros mc0 A. split.
  - intro Hsat. apply Completeness.tableau_completeness_sat.
    now rewrite <- is_sat_spec.
  - intro Hsat. rewrite is_sat_spec. now apply Soundness.tableau_sound_contrapos.
Qed.
