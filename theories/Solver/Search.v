(** CEGARBox decision procedure.

    We make heavy use of Program Fixpoint/Definition.

    Program Fixpoint allows us to prove that a fixpoint terminates with a custom
    well-founded measurement, and generates obligations to show that every
    recursive call is indeed a strict decrease of the measurement.

    Program also allows us to leave 'holes' in places where propositions are expected.
    We can then fill in these holes as obligations, so that we can actually
    use the proof language rather than trying to do some stuff with function application. *)


From CegarTableaux Require CplSolver Lit Mchain Assumptions Valuation Tree.
From CegarTableaux Require Import ImportStd Utils ListExt.
From CegarTableaux.Solver Require Import MchainExt.
From CegarTableaux.Solver Require Derivation.



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


(** Default auto-solver simplifies a bit too much. *)
Local Obligation Tactic := intros; try solve [ cbn; auto ].


(** * CEGARBox implementation and proof *)

(** An unsat core can technically be retrieved from the dereivation, but
    that might involve a deep recursion, so having it immediately accessible
    is a bit faster and makes it easier to omit the dereivation from the
    procedure if we want to remove it. *)
Module JumpSolution.
  Inductive t :=
  (* Assumptions need to be a set of literals because atoms not in there are treated as unset. *)
  | Sat (T1s : list Tree.t)
  | Unsat (failed_dia : DiaClause.t) (core : Assumptions.t) (deriv : Derivation.t).
End JumpSolution.

(** A CEGARBox sat/unsat solution. *)
Module Solution.
  Inductive t :=
    | Sat (T0 : Tree.t)
    | Unsat (core : Assumptions.t) (deriv : Derivation.t).

  Definition is_sat t : Prop :=
    match t with
    | Sat _ => True
    | Unsat _ _ => False
    end.

  Definition is_unsat t : Prop :=
    match t with
    | Sat _ => False
    | Unsat _ _ => True
    end.
End Solution.


(* CONVENTIONS: l<n> means the local clauses at world n,
  mc<n> means the whole modal context chain starting from n onwards. *)

(** When proving termination / obligations, Equations doesn't keep all
    information about which specific branch is being taken. The [inspect]
    function and [eqn:Heqn] adds hypotheses to the context about which
    context was taken. This is only necessary for hypotheses needed
    for the obligations, as using [funelim] correctly keeps information
    about the branches taken. *)
Notation "x 'eqn' ':' p" := (exist _ x p) (only parsing, at level 20).

Equations tableau_jumps_non_tailrec
  (* Actual arguments. *)
  (V : Valuation.t)
  (l0 : Lclauses.t)
  (mc1 : Mchain.t)
  (* The [tableau] function below with [mc1] and
    [s1 := CplSolver.make_with_clauses (first_cpls mc1)]. *)
  (next_tableau : Assumptions.t -> Solution.t)
  : JumpSolution.t
  by wf (List.length (Lclauses.dias l0)) lt
:=
(* Every fired child satisfied. *)
tableau_jumps_non_tailrec V (Lclauses.make _ _ []) mc1 next_tableau :=
  JumpSolution.Sat [];
tableau_jumps_non_tailrec V (Lclauses.make cpls boxes ((c, d) :: dias')) mc1 next_tableau
with Valuation.forces_atm V c := {
  (* Skip unfired dia clause. *)
  | false => tableau_jumps_non_tailrec V (Lclauses.make cpls boxes dias') mc1 next_tableau
  (* (jump) rule. *)
  | true =>
    let fired_boxes :=
      boxes
      |> List.filter (fun '(a, b) => Valuation.forces_atm V a)
      |> List.map snd
    in
    match next_tableau (d::fired_boxes) with
    (* unsat jump, will restart. *)
    | Solution.Unsat core deriv =>
      JumpSolution.Unsat (c,d) core deriv
    (* sat jump, next child. *)
    | Solution.Sat T1 =>
      match tableau_jumps_non_tailrec V (Lclauses.make cpls boxes dias') mc1 next_tableau with
      (* T1 is added on the 'opposite' end to match the behaviour of the accumulator in [tableau_jumps]. *)
      | JumpSolution.Sat T1s =>
        JumpSolution.Sat (T1s++[T1])
      | JumpSolution.Unsat failed_dia core deriv =>
        JumpSolution.Unsat failed_dia core deriv
      end
    end
}.
Fail Next Obligation.

Equations tableau_jumps
  (* Actual arguments. *)
  (V : Valuation.t)
  (l0 : Lclauses.t)
  (mc1 : Mchain.t)
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
with Valuation.forces_atm V c := {
  (* Skip unfired dia clause. *)
  | false => tableau_jumps V (Lclauses.make cpls boxes dias') mc1 T1s next_tableau
  (* (jump) rule. *)
  | true =>
    let fired_boxes :=
      boxes
      |> List.filter (fun '(a, b) => Valuation.forces_atm V a)
      |> List.map snd
    in
    match next_tableau (d::fired_boxes) with
    (* unsat jump, will restart. *)
    | Solution.Unsat core deriv =>
      JumpSolution.Unsat (c,d) core deriv
    (* sat jump, next child. *)
    | Solution.Sat T1 =>
      tableau_jumps V (Lclauses.make cpls boxes dias') mc1 (T1 :: T1s) next_tableau
    end
}.
Fail Next Obligation.


Lemma jump_c_forced : forall V l0 mc1 T1s next_tableau c d core deriv,
  JumpSolution.Unsat (c,d) core deriv = tableau_jumps V l0 mc1 T1s next_tableau ->
  Valuation.forces_atm V c = true.
Proof.
  intros. funelim (tableau_jumps V l0 mc1 T1s next_tableau).
  - discriminate.
  - cbn in Heqcall. destruct (next_tableau _).
    + eapply H.
      rewrite Heqcall. exact H0.
    + rewrite <- Heqcall in H0. injection H0; intros; subst. exact Heq.
  - rewrite <- Heqcall in H0. eapply H. exact H0.
Qed.


Equations tableau
  (* Extra assumptions brought by boxes/dias from the previous world *)
  (A : Assumptions.t)
  (* The CPL clauses of the current world and maybe extra conflict sets. *)
  (s0 : CplSolver.t)
  (mc0 : Mchain.t)
  : Solution.t
  by wf (
    List.length mc0,
    (* remaining number of possible valuations *)
    List.length (CplSolver.every_sat_valuation s0 A)
  ) lexnat2_lt
:=
tableau A s0 mc0
with inspect (CplSolver.solve_with_assumptions s0 A) := {
  | CplSolver.Solution.Unsat A' eqn:Hcsol_eq => Solution.Unsat A' (Derivation.Id A')
  | CplSolver.Solution.Sat V eqn:Hcsol_eq with mc0 =>
    | [] => Solution.Sat (Tree.make V [])
    | (l0 :: mc1) with inspect (tableau_jumps V l0 mc1 [] (fun A' => tableau A' (CplSolver.make_with_clauses (first_cpls mc1)) mc1)) := {
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
        let mc0' := add_conflict_set (l0::mc1) conflict_set in
        match tableau A s0' mc0' with (* recursion: RESTART *)
        | Solution.Sat T0 => Solution.Sat T0
        | Solution.Unsat rs_core rs_deriv =>
          Solution.Unsat rs_core
            (Derivation.JumpRestart V (c,d) jump_deriv rs_deriv)
        end
    }
}.
Next Obligation.
  (* JUMP call measure decreasing. *)
  cbn in *.
  left. subst. cbn. auto.
Qed.
Next Obligation with auto with typeclass_instances datatypes ct; try lia.
  (* RESTART call measure decreasing. *)
  destruct l0. cbn in *. subst. right.

  set (s0'_sats := CplSolver.every_sat_valuation s0' A) in *.
  set (s0_sats := CplSolver.every_sat_valuation s0 A) in *.

  assert (inclA Valuation.eq s0'_sats s0_sats) as Hincl. {
    apply CplSolver.refined_solver_sat_vals_subset with (clause := List.map Lit.Neg conflict_set).
    - apply val_subset_no_new_atms with (V := V)...
      apply conflict_set_incl_val with (s := s0) (A := A)...
      cbn in Hcsol_eq. eapply jump_c_forced. now rewrite Hj_eq.
    - subst s0'. reflexivity.
  }

  apply Nat.le_neq. split.
  - apply NoDupA_incl_length with (eqA := Valuation.eq)...
    apply CplSolver.every_sat_valuation_nodup.
  - intro Hlen.

    apply CplSolver.refined_solver_diff_val with s0 A V conflict_set s0'.
    + symmetry. exact Hcsol_eq.
    + apply conflict_set_incl_val with s0 A...
      eapply jump_c_forced. now rewrite Hj_eq.
    + subst conflict_set. unfold conflict_set_of, "|>".
      discriminate.
    + subst s0'. unfold CplSolver.add_conflict_set. rewrite CplSolver.add_clause_cons.
      now left.
    + apply PermutationA_inA with (l := s0_sats)...
      2: { now apply CplSolver.valuation_in_every_sat_valuation. }
      subst s0_sats s0'_sats. apply NoDup_PermutationA_bis...
      apply NoDupA_length_incl...
Qed.
Fail Next Obligation.


(** Solve a formula by applying [cegar_box] with the correct arguments. *)
Definition solve_mchain (mc0 : Mchain.t) : Solution.t :=
  let cpls := first_cpls mc0 in
  let s0 := (CplSolver.make_with_clauses cpls) in
  tableau [] s0 mc0.


(** Solve a [Fml.t] formula by converting first. *)
Definition solve_fml (phi : Fml.t) : Solution.t :=
  phi |> Nnf.from_fml |> Mcnf.from_nnf |> Mchain.from_mcnf |> solve_mchain.



(** The tableau function passed in to [tableau_jumps]. *)
Definition next_tableau mc1 := fun A' =>
  Search.tableau A' (CplSolver.make_with_clauses (first_cpls mc1)) mc1.
