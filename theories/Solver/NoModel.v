(** Does not construct a model/derivation. *)

From CegarTableaux.Solver Require Import SearchBasics.
From CegarTableaux.Solver Require Spec Soundness Completeness.


Module JumpSolution.
  Inductive t :=
    | Sat
    | Unsat (c : nat) (core : Assumptions.t).


  Definition matches_spec (t : t) (spec : Spec.JumpSolution.t) :=
    match t, spec with
    | Sat, Spec.JumpSolution.Sat _ => True
    | Unsat c core, Spec.JumpSolution.Unsat (c',_) core' _ => c = c' /\ core = core'
    | _, _ => False
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

  Definition matches_spec (t : t) (spec : Spec.Solution.t) :=
    match t, spec with
    | Sat, Spec.Solution.Sat _ => True
    | Unsat core, Spec.Solution.Unsat core' _ => core = core'
    | _, _ => False
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
  Valuation.forces_atm V c = true.
Proof with auto.
  intros * Hunsat. funelim (tableau_jumps V l0 mc1 next_tableau); rewrite <- Heqcall in Hunsat.
  - discriminate.
  - eapply H. exact Hunsat.
  - eapply H. exact Hunsat.
  - inversion Hunsat; subst. assumption.
Qed.


Equations tableau
  (A : Assumptions.t)
  (s0 : CplSolver.t)
  (mc0 : Mcnf.t)
  : Solution.t
  by wf (
    List.length mc0,
    List.length (CplSolver.every_sat_valuation s0 A)
  ) lexnat2_lt
:=
tableau A s0 mc0
with inspect (CplSolver.solve_with_assumptions s0 A) := {
  | CplSolution.Unsat A' eqn:Hcsol_eq => Solution.Unsat A'
  | CplSolution.Sat V eqn:Hcsol_eq with mc0 =>
    | [] => Solution.Sat
    | (l0 :: mc1) with inspect (tableau_jumps V l0 mc1 (fun A' => tableau A' (CplSolver.make_with_clauses (first_cpls mc1)) mc1)) := {
      | JumpSolution.Sat eqn:Hj_eq => Solution.Sat
      | JumpSolution.Unsat c jump_core eqn:Hj_eq =>
        let conflict_set := conflict_set_of (l0::mc1) V c jump_core in
        let s0' := CplSolver.add_conflict_set s0 conflict_set in
        let mc0' := add_conflict_set (l0::mc1) conflict_set in
        tableau A s0' mc0'
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
  let cpls := first_cpls mc0 in
  let s0 := (CplSolver.make_with_clauses cpls) in
  tableau [] s0 mc0.


(** Solve a [Fml.t] formula by converting first. *)
Definition solve_fml (phi : Fml.t) : Solution.t :=
  phi |> Nnf.from_fml |> Mcnf.from_nnf |> solve_mcnf.


Definition next_tableau mc1 := fun A' =>
  tableau A' (CplSolver.make_with_clauses (first_cpls mc1)) mc1.


Lemma tableau_jumps_spec : forall V l0 mc1 next_tableau next_tableau',
  (forall A, Solution.matches_spec (next_tableau A) (next_tableau' A)) ->
  JumpSolution.matches_spec (tableau_jumps V l0 mc1 next_tableau) (Spec.tableau_jumps V l0 mc1 next_tableau').
Proof with try solve [ cbn in *; try easy; auto with ct datatypes ].
  intros * Hsol_match.
  funelim (Spec.tableau_jumps V l0 mc1 next_tableau').
  - unfold JumpSolution.matches_spec. destruct matches.
    simp tableau_jumps in Heqt. discriminate.
  - simp tableau_jumps. unfold tableau_jumps_unfold_clause_2.
    rewrite Heq.
    apply H. apply Hsol_match.
  - simp tableau_jumps. unfold tableau_jumps_unfold_clause_2.
    rewrite Heq0. unfold tableau_jumps_unfold_clause_2_clause_2.

    set (fired_boxes := d::boxes |> List.filter (fun '(a, _) => Valuation.forces_atm V a) |> map snd) in *.
    specialize (Hsol_match fired_boxes).
    unfold Solution.matches_spec in Hsol_match.
    rewrite Heq in Hsol_match.
    destruct (next_tableau1 fired_boxes)...

  (* TODO: both cases below are identical. *)
  - simp tableau_jumps. unfold tableau_jumps_unfold_clause_2.
    rewrite Heq1. unfold tableau_jumps_unfold_clause_2_clause_2.

    specialize (Hind next_tableau1 Hsol_match).

    set (fired_boxes := d::boxes |> List.filter (fun '(a, _) => Valuation.forces_atm V a) |> map snd) in *.
    specialize (Hsol_match fired_boxes).
    unfold Solution.matches_spec in Hsol_match.
    rewrite Heq0 in Hsol_match.
    destruct (next_tableau1 fired_boxes)...

    unfold JumpSolution.matches_spec in *. destruct matches.
  - simp tableau_jumps. unfold tableau_jumps_unfold_clause_2.
    rewrite Heq1. unfold tableau_jumps_unfold_clause_2_clause_2.

    specialize (Hind next_tableau1 Hsol_match).

    set (fired_boxes := d::boxes |> List.filter (fun '(a, _) => Valuation.forces_atm V a) |> map snd) in *.
    specialize (Hsol_match fired_boxes).
    unfold Solution.matches_spec in Hsol_match.
    rewrite Heq0 in Hsol_match.
    destruct (next_tableau1 fired_boxes)...

    unfold JumpSolution.matches_spec in *. destruct matches.
Qed.


Lemma tableau_spec : forall A s0 mc0,
  Solution.matches_spec (tableau A s0 mc0) (Spec.tableau A s0 mc0).
Proof with try solve [ cbn in *; try easy; auto with ct datatypes ].
  intros *.
  funelim (Spec.tableau A s0 mc0).
  - clear H. simp tableau. unfold tableau_unfold_clause_1. cbn.
    dep_destruct (CplSolver.solve_with_assumptions s0 A) as Hs_eq.
    + rewrite Hs_eq in Hcsol_eq. discriminate.
    + rewrite Hs_eq in Hcsol_eq. now inversion_clear Hcsol_eq.

  - clear H. simp tableau. unfold tableau_unfold_clause_1. cbn.
    dep_destruct (CplSolver.solve_with_assumptions s0 A) as Hs_eq.
    + now cbn.
    + rewrite Hs_eq in Hcsol_eq. discriminate.

  - clear H H0. simp tableau. unfold tableau_unfold_clause_1. cbn.

    dep_destruct (CplSolver.solve_with_assumptions s0 A) as Hs_eq.
    + cbn -[add_conflict_set].
      rewrite Hs_eq in Hcsol_eq. inversion Hcsol_eq; subst; clear Hcsol_eq.

      (* contradiction between Hj_eq and Hj_unsat *)
      fold (next_tableau mc1) in *.
      fold (Spec.next_tableau mc1) in *.
      pose proof (tableau_jumps_spec V l0 mc1
        (next_tableau mc1)
        (Spec.next_tableau mc1)
        Hind
      ) as Hj_matches.

      destruct (tableau_jumps _ _ _ _) eqn:Hj_unsat...
      cbn in Hj_matches. rewrite Hj_eq in Hj_matches. contradiction.

    + rewrite Hs_eq in Hcsol_eq. discriminate.

  - clear H0 H1.

    set (spec_call := Spec.tableau _ _ _) in *.
    simp tableau. cbn. dep_destruct (CplSolver.solve_with_assumptions s0 A) as Hs_eq.
    + cbn -[add_conflict_set]. rewrite Hs_eq in Hcsol_eq. inversion_clear Hcsol_eq.
      fold (next_tableau mc1) in *.
      fold (Spec.next_tableau mc1) in *.
      pose proof (tableau_jumps_spec V l0 mc1
        (next_tableau mc1)
        (Spec.next_tableau mc1)
        Hind
      ) as Hj_matches.

      destruct (tableau_jumps _ _ _ _).
      * cbn in Hj_matches. rewrite Hj_eq in Hj_matches. contradiction.
      * cbn in Hj_matches. rewrite Hj_eq in Hj_matches. destruct Hj_matches as [Hc Hcore]. subst.
        destruct spec_call...
    + rewrite Hs_eq in Hcsol_eq. discriminate.
Qed.


Corollary is_sat_spec : forall A s0 mc0,
  Solution.is_sat (tableau A s0 mc0) = Spec.Solution.is_sat (Spec.tableau A s0 mc0).
Proof.
  intros A s0 mc0.
  pose proof (tableau_spec A s0 mc0).
  unfold Solution.matches_spec in H.
  destruct matches in *; tauto.
Qed.
