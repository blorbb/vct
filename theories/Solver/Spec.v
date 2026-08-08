(** Simple, unoptimised implementation that is easier to prove correctness of. *)

From Vct.Solver Require Import SearchBasics.


Module JumpSolution.
  (** An unsat core can technically be retrieved from the dereivation, but
      that might involve a deep recursion, so having it immediately accessible
      is a bit faster and makes it easier to omit the dereivation from the
      procedure if we want to remove it. *)
  Inductive t :=
  (* Assumptions need to be a set of literals because atoms not in there are treated as unset. *)
  | Sat (T1s : list Tree.t)
  | Unsat (failed_dia : DiaClause.t) (core : Assumptions.t) (deriv : Derivation.t).
End JumpSolution.

(** A tableau sat/unsat solution. *)
Module Solution.
  Inductive t :=
    | Sat (T0 : Tree.t)
    | Unsat (core : Assumptions.t) (deriv : Derivation.t).

  Definition is_sat t : bool :=
    match t with
    | Sat _ => true
    | Unsat _ _ => false
    end.
End Solution.


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
  JumpSolution.Sat [];
tableau_jumps V (Lclauses.make cpls boxes ((c, d) :: dias')) mc1 next_tableau
with Valuation.forces_atm V c =>
  (* Skip unfired dia clause. *)
  | false => tableau_jumps V (Lclauses.make cpls boxes dias') mc1 next_tableau
  (* (jump) rule. *)
  | true with let fired_boxes :=
      boxes
      |> List.filter (fun '(a, b) => Valuation.forces_atm V a)
      |> List.map snd
    in next_tableau (d::fired_boxes) =>
      (* unsat jump, will restart. *)
      | Solution.Unsat core deriv =>
        JumpSolution.Unsat (c,d) core deriv
      (* sat jump, next child. *)
      | Solution.Sat T1 with tableau_jumps V (Lclauses.make cpls boxes dias') mc1 next_tableau =>
        (* T1 is added on the 'opposite' end to match the behaviour of the 
          accumulator in [TailRec.tableau_jumps]. *)
        | JumpSolution.Sat T1s =>
          JumpSolution.Sat (T1s++[T1])
        | JumpSolution.Unsat failed_dia core deriv =>
          JumpSolution.Unsat failed_dia core deriv
.
Fail Next Obligation.


Lemma jump_c_forced : forall V l0 mc1 next_tableau c d core deriv,
  tableau_jumps V l0 mc1 next_tableau = JumpSolution.Unsat (c,d) core deriv ->
  Valuation.forces_atm V c.
Proof.
  intros * Hunsat. funelim (tableau_jumps V l0 mc1 next_tableau); rewrite <- Heqcall in Hunsat.
  - discriminate.
  - eapply H. exact Hunsat.
  - inversion Hunsat; subst. assumption.
  - discriminate.
  - inversion Hunsat; subst. eapply Hind. exact Heq.
Qed.


Equations tableau
  (mc0 : Mcnf.t)
  (* The CPL clauses of the current world and maybe extra conflict sets. *)
  (s0 : CplSolver.t)
  (* Extra assumptions brought by boxes/dias from the previous world *)
  (A : Assumptions.t)
  : Solution.t
  by wf (
    List.length mc0,
    (* remaining number of possible valuations *)
    List.length (CplSolver.every_sat_valuation s0 A)
  ) lexnat2_lt
:=
tableau mc0 s0 A
with inspect (CplSolver.solve_with_assumptions s0 A) =>
  | CplSolution.Unsat A' eqn:Hcsol_eq => Solution.Unsat A' (Derivation.Local A')
  | CplSolution.Sat V eqn:Hcsol_eq with mc0 =>
    | [] => Solution.Sat (Tree.make V [])
    | (l0 :: mc1) with inspect (tableau_jumps V l0 mc1 (fun A' => tableau mc1 (cplsolver_mcnf mc1) A')) =>
      (* Every child was sat -> done! *)
      | JumpSolution.Sat T1s eqn:Hj_eq => Solution.Sat (Tree.make V T1s)
      | JumpSolution.Unsat (c,d) jump_core jump_deriv eqn:Hj_eq =>
        (* all names that fired some literal in the core + the antecedent of the unsat dia clause *)
        let conflict_set := conflict_set_of (l0::mc1) V c jump_core in
        (* conflict_set is interpreted as a conjunction *)
        (* negate the whole thing to become a cpl clause, interpreted as a disjunction *)
        let s0' := CplSolver.add_conflict_set s0 conflict_set in
        (* Add conflict set to mc0 to get the restarted mc0'.
          This is needed for the closed tableau types to work out.
          The cpls of l0 aren't used anyways. The SAT solver state stays incremental. *)
        let mc0' := Mcnf.add_cs (l0::mc1) conflict_set in
        match tableau mc0' s0' A with (* recursion: RESTART *)
        | Solution.Sat T0 => Solution.Sat T0
        | Solution.Unsat rs_core rs_deriv =>
          Solution.Unsat rs_core
            (Derivation.JumpRestart V (c,d) jump_deriv rs_deriv)
        end
.
Next Obligation.
  (* JUMP call measure decreasing. *)
  cbn in *. left. auto.
Qed.
Next Obligation.
  cbn in *. right. apply decreasing_sat_vals; try easy.
  eapply jump_c_forced. exact Hj_eq.
Qed.
Fail Next Obligation.


(** Solve a formula by applying [tableau] with the correct arguments. *)
Definition solve_mcnf (mc0 : Mcnf.t) : Solution.t :=
  tableau mc0 (cplsolver_mcnf mc0) [].


(** Solve a [Fml.t] formula by converting first. *)
Definition solve_fml (phi : Fml.t) : Solution.t :=
  phi |> Nnf.from_fml |> Mcnf.from_nnf |> solve_mcnf.
