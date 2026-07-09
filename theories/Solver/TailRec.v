(** Tail recursive [tableau_jumps]. *)

From CegarTableaux.Solver Require Import SearchBasics.
From CegarTableaux.Solver Require Spec.


Module Solution := Spec.Solution.
Module JumpSolution := Spec.JumpSolution.


Equations tableau_jumps
  (* Actual arguments. *)
  (V : Valuation.t)
  (l0 : Lclauses.t)
  (mc1 : Mcnf.t)
  (* Previous sibling satisfying models. *)
  (T1s : list Tree.t)
  (* The [tableau] function below with [mc1] and
    [s1 := CplSolver.make_with_clauses (first_cpls mc1)]. *)
  (next_tableau : Assumptions.t -> Solution.t)
  : JumpSolution.t
  by wf (List.length (Lclauses.dias l0)) lt
:=
(* Every fired child satisfied. *)
tableau_jumps V (Lclauses.make _ _ []) mc1 T1s next_tableau :=
  JumpSolution.Sat T1s;
tableau_jumps V (Lclauses.make cpls boxes ((c, d) :: dias')) mc1 T1s next_tableau
with Valuation.forces_atm V c =>
  | false => tableau_jumps V (Lclauses.make cpls boxes dias') mc1 T1s next_tableau
  | true =>
    let fired_boxes :=
      boxes
      |> List.filter (fun '(a, b) => Valuation.forces_atm V a)
      |> List.map snd
    in
    match next_tableau (d::fired_boxes) with
    | Solution.Unsat core deriv =>
      JumpSolution.Unsat (c,d) core deriv
    | Solution.Sat T1 =>
      tableau_jumps V (Lclauses.make cpls boxes dias') mc1 (T1 :: T1s) next_tableau
    end
.
Fail Next Obligation.


Lemma tableau_jumps_spec : forall V l0 mc1 acc next_tableau,
  tableau_jumps V l0 mc1 acc next_tableau =
  match Spec.tableau_jumps V l0 mc1 next_tableau with
  | JumpSolution.Sat T1s => JumpSolution.Sat (T1s ++ acc)
  | JumpSolution.Unsat failed_dia core closedtab => JumpSolution.Unsat failed_dia core closedtab  end.
Proof with try solve [ cbn in *; try easy; auto with ct datatypes ].
  intros *.
  funelim (Spec.tableau_jumps V l0 mc1 next_tableau);
    simp tableau_jumps; try unfold tableau_jumps_unfold_clause_2; try destruct (Valuation.forces_atm V c); try easy.
  - destruct (next_tableau _)...
    now inversion_clear Heq.
  - destruct (next_tableau _)...
    rewrite Hind... destruct (Spec.tableau_jumps V _ mc1 next_tableau)...
    rewrite <- List.app_assoc.
    inversion_clear Heq. inversion_clear Heq0. reflexivity.
  - destruct (next_tableau _)...
    rewrite Hind... destruct (Spec.tableau_jumps V _ mc1 next_tableau)...
Qed.

Corollary tableau_jumps_spec_init : forall V l0 mc1 next_tableau,
  Spec.tableau_jumps V l0 mc1 next_tableau =  tableau_jumps V l0 mc1 [] next_tableau.
Proof.
  intros *. rewrite tableau_jumps_spec.
  destruct (Spec.tableau_jumps _ _ _ _); try easy.
  f_equal. now rewrite app_nil_r.
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
with inspect (CplSolver.solve_with_assumptions s0 A) =>
  | CplSolution.Unsat A' eqn:Hcsol_eq => Solution.Unsat A' (Derivation.Id A')
  | CplSolution.Sat V eqn:Hcsol_eq with mc0 =>
    | [] => Solution.Sat (Tree.make V [])
    | (l0 :: mc1) with inspect (tableau_jumps V l0 mc1 [] (fun A' => tableau A' (CplSolver.make_with_clauses (first_cpls mc1)) mc1)) =>
      | JumpSolution.Sat T1s eqn:Hj_eq => Solution.Sat (Tree.make V T1s)
      | JumpSolution.Unsat (c,d) jump_core jump_deriv eqn:Hj_eq =>
        let conflict_set := conflict_set_of (l0::mc1) V c jump_core in
        let s0' := CplSolver.add_conflict_set s0 conflict_set in
        let mc0' := add_conflict_set (l0::mc1) conflict_set in
        match tableau A s0' mc0' with
        | Solution.Sat T0 => Solution.Sat T0
        | Solution.Unsat rs_core rs_deriv =>
          Solution.Unsat rs_core
            (Derivation.JumpRestart V (c,d) jump_deriv rs_deriv)
        end
.
Next Obligation.
  (* JUMP call measure decreasing. *)
  cbn in *.
  left. subst. cbn. auto.
Qed.
Next Obligation.
  (* RESTART call measure decreasing. *)
  destruct l0. right.
  apply decreasing_sat_vals; try easy.
  eapply Spec.jump_c_forced.
  rewrite tableau_jumps_spec_init. exact Hj_eq.
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


Lemma tableau_spec : forall A s0 mc0,
  Spec.tableau A s0 mc0 = tableau A s0 mc0.
Proof with try solve [ cbn in *; try easy; auto with ct datatypes ].
  intros *.
  funelim (Spec.tableau A s0 mc0).
  - clear H. simp tableau. unfold tableau_unfold_clause_1. cbn.
    dep_destruct (CplSolver.solve_with_assumptions s0 A) as Hs_eq.
    + rewrite Hs_eq in Hcsol_eq. discriminate.
    + rewrite Hs_eq in Hcsol_eq. now inversion_clear Hcsol_eq.

  - clear H. simp tableau. unfold tableau_unfold_clause_1. cbn.
    dep_destruct (CplSolver.solve_with_assumptions s0 A) as Hs_eq.
    + cbn. rewrite Hs_eq in Hcsol_eq. now inversion_clear Hcsol_eq.
    + rewrite Hs_eq in Hcsol_eq. discriminate.

  - clear H H0. simp tableau. unfold tableau_unfold_clause_1. cbn.

    rewrite tableau_jumps_spec_init in Hj_eq.
    replace (fun A' : Assumptions.t => Spec.tableau A' (CplSolver.make_with_clauses (first_cpls mc1)) mc1)
      with (fun A' : Assumptions.t => tableau A' (CplSolver.make_with_clauses (first_cpls mc1)) mc1) in Hj_eq.
    2: { apply functional_extensionality. intro A'. now rewrite Hind. }

    dep_destruct (CplSolver.solve_with_assumptions s0 A) as Hs_eq.
    + rewrite Hs_eq in Hcsol_eq. inversion Hcsol_eq; subst; clear Hcsol_eq.
      cbn. destruct (tableau_jumps V l0 mc1 []).
      * now inversion_clear Hj_eq.
      * discriminate.
    + rewrite Hs_eq in Hcsol_eq. discriminate.

  - clear H0 H1.

    rewrite tableau_jumps_spec_init in Hj_eq.
    replace (fun A' : Assumptions.t => Spec.tableau A' (CplSolver.make_with_clauses (first_cpls mc1)) mc1)
      with (fun A' : Assumptions.t => tableau A' (CplSolver.make_with_clauses (first_cpls mc1)) mc1) in Hj_eq.
    2: { apply functional_extensionality. intro A'. now rewrite Hind. }

    set (spec_call := Spec.tableau _ _ _).
    simp tableau. cbn. dep_destruct (CplSolver.solve_with_assumptions s0 A) as Hs_eq.
    + cbn -[add_conflict_set]. rewrite Hs_eq in Hcsol_eq. inversion_clear Hcsol_eq.
      rewrite Hj_eq. now rewrite <- H.
    + rewrite Hs_eq in Hcsol_eq. discriminate.
Qed.
