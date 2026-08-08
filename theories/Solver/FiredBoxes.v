(** Extension of [Cached] with [fired_boxes] only calculated once per set of jumps. *)

From Vct Require Import ImportStd.
From Vct.Solver Require Cached.
From Vct.Solver Require Import SearchBasics.

Module Cache := Cached.Cache.
Module Caches := Cached.Caches.
Module JumpSolution := Cached.JumpSolution.
Module Solution := Cached.Solution.


Definition get_fired_boxes V l0 :=
  l0
  |> Lclauses.boxes
  |> List.filter (fun '(a, b) => Valuation.forces_atm V a)
  |> List.map snd.

Equations tableau_jumps
  (V : Valuation.t)
  (l0 : Lclauses.t)
  (mc1 : Mcnf.t)
  (next_tableau : Assumptions.t -> Caches.t -> Solution.t)
  (fired_boxes : list Lit.t)
  (caches1 : Caches.t)
  : JumpSolution.t
  by wf (List.length (Lclauses.dias l0)) lt
:=
(* Every fired child satisfied. *)
tableau_jumps V (Lclauses.make _ _ []) mc1 next_tableau fired_boxes caches1 :=
  JumpSolution.Sat caches1;
tableau_jumps V (Lclauses.make cpls boxes ((c, d) :: dias')) mc1 next_tableau fired_boxes caches1
with Valuation.forces_atm V c =>
  | false => tableau_jumps V (Lclauses.make cpls boxes dias') mc1 next_tableau fired_boxes caches1
  | true with next_tableau (d::fired_boxes) caches1 =>
      | Solution.Unsat core caches1' =>
        JumpSolution.Unsat c core caches1'
      | Solution.Sat caches1' =>
        tableau_jumps V (Lclauses.make cpls boxes dias') mc1 next_tableau fired_boxes caches1'
.
Fail Next Obligation.


Lemma tableau_jumps_cached : forall V l0 mc1 next_tableau caches1,
  Cached.tableau_jumps V l0 mc1 next_tableau caches1 = tableau_jumps V l0 mc1 next_tableau (get_fired_boxes V l0) caches1.
Proof with try easy.
  intros *.
  funelim (Cached.tableau_jumps V l0 mc1 next_tableau caches1).
  - now simp tableau_jumps.
  - simp tableau_jumps. unfold tableau_jumps_unfold_clause_2.
    rewrite Heq. cbn. exact H.
  - simp tableau_jumps. unfold tableau_jumps_unfold_clause_2.
    rewrite Heq0. unfold tableau_jumps_unfold_clause_2_clause_2.
    destruct (next_tableau _)...
    cbn in *. inv_clear Heq. exact H.
  - simp tableau_jumps. unfold tableau_jumps_unfold_clause_2.
    rewrite Heq0. unfold tableau_jumps_unfold_clause_2_clause_2.
    cbn. now rewrite Heq.
Qed.


Equations tableau
  (mc0 : Mcnf.t)
  (s0 : CplSolver.t)
  (A : Assumptions.t)
  (caches : Caches.t)
  : Solution.t
  by wf (
    List.length mc0,
    List.length (CplSolver.every_sat_valuation s0 A)
  ) lexnat2_lt
:=
tableau mc0 s0 A caches
with Caches.contains caches A =>
  | true => Solution.Sat caches
  | false with inspect (CplSolver.solve_with_assumptions s0 A) =>
    | CplSolution.Unsat A' eqn:Hcsol_eq => Solution.Unsat A' caches
    | CplSolution.Sat V eqn:Hcsol_eq with mc0 =>
      | [] => Solution.Sat (Caches.add caches A)
      | (l0 :: mc1) with Caches.destruct caches =>
        | (cache0, caches1) with
          let s1 := cplsolver_mcnf mc1 in
          let fired_boxes := get_fired_boxes V l0 in
          inspect (
            tableau_jumps
              V l0 mc1
              (fun A' caches1' => tableau mc1 s1 A' caches1')
              fired_boxes
              caches1
          ) =>
          | JumpSolution.Sat caches1' eqn:Hj_eq => Solution.Sat (Cache.add cache0 A :: caches1')
          | JumpSolution.Unsat c jump_core caches1' eqn:Hj_eq =>
            let conflict_set := conflict_set_of (l0::mc1) V c jump_core in
            let s0' := CplSolver.add_conflict_set s0 conflict_set in
            let mc0' := Mcnf.add_cs (l0::mc1) conflict_set in
            tableau mc0' s0' A (cache0::caches1')
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
  eapply Cached.jump_c_forced.
  rewrite tableau_jumps_cached. exact Hj_eq.
Qed.
Fail Next Obligation.


Definition solve_mcnf (mc0 : Mcnf.t) : Solution.t :=
  tableau mc0 (cplsolver_mcnf mc0) [] [].


(** Solve a [Fml.t] formula by converting first. *)
Definition solve_fml (phi : Fml.t) : Solution.t :=
  phi |> Nnf.from_fml |> Mcnf.from_nnf |> solve_mcnf.



Lemma tableau_cached : forall A s0 mc0 caches,
  Cached.tableau A s0 mc0 caches = tableau A s0 mc0 caches.
Proof with try easy; try congruence; auto.
  intros *.
  funelim (Cached.tableau A s0 mc0 caches).
  - simp tableau. unfold tableau_unfold_clause_1. now rewrite Heq.
  - clear H.
    simp tableau. unfold tableau_unfold_clause_1. rewrite Heq.
    unfold tableau_unfold_clause_1_clause_2. cbn.
    dep_destruct (CplSolver.solve_with_assumptions s0 A) as Hs...
  - clear H.
    simp tableau. unfold tableau_unfold_clause_1. rewrite Heq.
    unfold tableau_unfold_clause_1_clause_2. cbn.
    dep_destruct (CplSolver.solve_with_assumptions s0 A) as Hs...
  - clear H H0.
    simp tableau. unfold tableau_unfold_clause_1. rewrite Heq0.
    unfold tableau_unfold_clause_1_clause_2. cbn.
    dep_destruct (CplSolver.solve_with_assumptions s0 A) as Hs...
    unfold tableau_unfold_clause_1_clause_2_clause_2_clause_2.
    rewrite Heq. cbn. eta.

    rewrite tableau_jumps_cached in Hj_eq.
    replace (Cached.tableau $ mc1) with (tableau $ mc1) in Hj_eq.
    2: {
      apply functional_extensionality. intro A'.
      apply functional_extensionality. intro caches'.
      now rewrite Hind.
    }

    rewrite Hs in Hcsol_eq. inv_clear Hcsol_eq.
    now rewrite Hj_eq.
  - clear H0 H1.

    set (cached_call := Cached.tableau _ _ _ _).

    simp tableau. unfold tableau_unfold_clause_1. rewrite Heq0.
    unfold tableau_unfold_clause_1_clause_2. cbn.
    dep_destruct (CplSolver.solve_with_assumptions s0 A) as Hs...
    unfold tableau_unfold_clause_1_clause_2_clause_2_clause_2.
    rewrite Heq. cbn. eta.

    rewrite tableau_jumps_cached in Hj_eq.
    replace (Cached.tableau $ mc1) with (tableau $ mc1) in Hj_eq.
    2: {
      apply functional_extensionality. intro A'.
      apply functional_extensionality. intro caches'.
      now rewrite Hind.
    }

    rewrite Hs in Hcsol_eq. inv_clear Hcsol_eq.
    now rewrite Hj_eq.
Qed.


