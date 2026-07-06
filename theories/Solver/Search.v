(** CEGARBox decision procedure.

    We make heavy use of Program Fixpoint/Definition.

    Program Fixpoint allows us to prove that a fixpoint terminates with a custom
    well-founded measurement, and generates obligations to show that every
    recursive call is indeed a strict decrease of the measurement.

    Program also allows us to leave 'holes' in places where propositions are expected.
    We can then fill in these holes as obligations, so that we can actually
    use the proof language rather than trying to do some stuff with function application. *)


From CegarTableaux Require CplSolver Lit Mcnf Assumptions Valuation Tree.
From CegarTableaux Require Import ImportStd.
From CegarTableaux.Solver Require Import McnfExt.
From CegarTableaux.Solver Require Derivation.
From stdpp Require Import gmap.


(** Default auto-solver simplifies a bit too much. *)
Local Obligation Tactic := intros; try solve [ cbn; auto ].


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
  Valuation.forces_atm V c = true ->
  let cs := conflict_set_of mc0 V c jump_core in
  let s0' := CplSolver.add_conflict_set s0 cs in
  List.length (CplSolver.every_sat_valuation s0' A) <
  List.length (CplSolver.every_sat_valuation s0 A).
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

    apply CplSolver.refined_solver_diff_val with s0 A V cs s0'.
    + symmetry. exact HV_sat.
    + apply conflict_set_incl_val with s0 A...
    + subst cs. unfold conflict_set_of, "|>".
      discriminate.
    + subst s0'. unfold CplSolver.add_conflict_set. rewrite CplSolver.add_clause_cons.
      now left.
    + apply PermutationA_inA with (l := s0_sats)...
      2: { now apply CplSolver.valuation_in_every_sat_valuation. }
      subst s0_sats s0'_sats. apply NoDup_PermutationA_bis...
      apply NoDupA_length_incl...
Qed.


(** * CEGAR-Tableaux implementations *)

Module Spec.
  (** Simple, unoptimised implementation that is easier to prove correctness of. *)

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
    Valuation.forces_atm V c = true.
  Proof with auto.
    intros * Hunsat. funelim (tableau_jumps V l0 mc1 next_tableau); rewrite <- Heqcall in Hunsat.
    - discriminate.
    - eapply H. exact Hunsat.
    - inversion Hunsat; subst. assumption.
    - discriminate.
    - inversion Hunsat; subst. eapply Hind. exact Heq.
  Qed.


  Equations tableau
    (* Extra assumptions brought by boxes/dias from the previous world *)
    (A : Assumptions.t)
    (* The CPL clauses of the current world and maybe extra conflict sets. *)
    (s0 : CplSolver.t)
    (mc0 : Mcnf.t)
    : Solution.t
    by wf (
      List.length mc0,
      (* remaining number of possible valuations *)
      List.length (CplSolver.every_sat_valuation s0 A)
    ) lexnat2_lt
  :=
  tableau A s0 mc0
  with inspect (CplSolver.solve_with_assumptions s0 A) =>
    | CplSolution.Unsat A' eqn:Hcsol_eq => Solution.Unsat A' (Derivation.Id A')
    | CplSolution.Sat V eqn:Hcsol_eq with mc0 =>
      | [] => Solution.Sat (Tree.make V [])
      | (l0 :: mc1) with inspect (tableau_jumps V l0 mc1 (fun A' => tableau A' (CplSolver.make_with_clauses (first_cpls mc1)) mc1)) =>
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


  (** The tableau function passed in to [tableau_jumps]. *)
  Definition next_tableau mc1 := fun A' =>
    tableau A' (CplSolver.make_with_clauses (first_cpls mc1)) mc1.


  (** Solve a formula by applying [tableau] with the correct arguments. *)
  Definition solve_mcnf (mc0 : Mcnf.t) : Solution.t :=
    let cpls := first_cpls mc0 in
    let s0 := (CplSolver.make_with_clauses cpls) in
    tableau [] s0 mc0.


  (** Solve a [Fml.t] formula by converting first. *)
  Definition solve_fml (phi : Fml.t) : Solution.t :=
    phi |> Nnf.from_fml |> Mcnf.from_nnf |> solve_mcnf.
End Spec.


Module TailRec.
  Module Solution := Spec.Solution.
  Module JumpSolution := Spec.JumpSolution.

  (** Tail recursive [tableau_jumps]. *)
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
End TailRec.


Module NoModel.
  (** Does not construct a model/derivation. *)

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
    Solution.is_sat (tableau A s0 mc0) = true <-> Spec.Solution.is_sat (Spec.tableau A s0 mc0) = true.
  Proof.
    intros A s0 mc0.
    pose proof (tableau_spec A s0 mc0).
    unfold Solution.matches_spec in H.
    destruct matches in *; tauto.
  Qed.
End NoModel.



Module Cached.
  (** With a satisfiability cache. *)
  Module Cache.
    (** Cache of satisfiable assumptions at the current modal level. *)
    Definition t := gset Assumptions.t.

    Definition empty : t := empty.

    Definition singleton (A : Assumptions.t) : t := singleton A.

    Definition contains (cache : t) (A : Assumptions.t) :=
      bool_decide (elem_of A cache).

    Definition add (cache : t) (A : Assumptions.t) :=
      union (singleton A) cache.
  End Cache.

  Module Caches.
    (** Caches for every modal level from the current one onwards. *)
    Definition t := list Cache.t.

    Definition contains (caches : t) (A : Assumptions.t) : bool :=
      match caches with
      | [] => false
      | c :: _ => Cache.contains c A
      end.

    Definition destruct (caches : t) : Cache.t * t :=
      match caches with
      | [] => (Cache.empty, [])
      | c :: rest => (c, rest)
      end.

    Definition add (caches : t) (A : Assumptions.t) : Caches.t :=
      match caches with
      | [] => [Cache.singleton A]
      | c :: rest => Cache.add c A :: rest
      end.
  End Caches.


  (** NOTE: I could make these [NoModel.Solution.t * Caches.t], but putting the
      cache within the variants make the function calls easier to [destruct]. *)
  Module JumpSolution.
    Inductive t :=
      | Sat (caches : Caches.t)
      | Unsat (c : nat) (core : Assumptions.t) (caches : Caches.t).


    Definition get_caches (s : t) : Caches.t :=
      match s with
      | Sat caches => caches
      | Unsat _ _ caches => caches
      end.

    (* Definition matches_spec (t : t) (spec : Spec.JumpSolution.t) :=
      match t, spec with
      | Sat _, Spec.JumpSolution.Sat _ => True
      | Unsat c core _, Spec.JumpSolution.Unsat (c',_) core' _ => c = c' /\ core = core'
      | _, _ => False
      end. *)
  End JumpSolution.


  Module Solution.
    Inductive t :=
      | Sat (caches : Caches.t)
      | Unsat (core : Assumptions.t) (caches : Caches.t).


    Definition is_sat t : bool :=
      match t with
      | Sat _ => true
      | Unsat _ _ => false
      end.


    Definition get_caches (s : t) : Caches.t :=
      match s with
      | Sat caches => caches
      | Unsat _ caches => caches
      end.

    (* Definition matches_spec (t : t) (spec : Spec.Solution.t) :=
      match t, spec with
      | Sat, Spec.Solution.Sat _ => True
      | Unsat core, Spec.Solution.Unsat core' _ => core = core'
      | _, _ => False
      end. *)
  End Solution.


  Equations tableau_jumps
    (* Actual arguments. *)
    (V : Valuation.t)
    (l0 : Lclauses.t)
    (mc1 : Mcnf.t)
    (* The [tableau] function below with [mc1] and
      [s1 := CplSolver.make_with_clauses (first_cpls mc1)]. *)
    (next_tableau : Assumptions.t -> Caches.t -> Solution.t)
    (** Cache from [mc1], not [l0]. *)
    (caches1 : Caches.t)
    : JumpSolution.t
    by wf (List.length (Lclauses.dias l0)) lt
  :=
  (* Every fired child satisfied. *)
  tableau_jumps V (Lclauses.make _ _ []) mc1 next_tableau caches1 :=
    JumpSolution.Sat caches1;
  tableau_jumps V (Lclauses.make cpls boxes ((c, d) :: dias')) mc1 next_tableau caches1
  with Valuation.forces_atm V c =>
    | false => tableau_jumps V (Lclauses.make cpls boxes dias') mc1 next_tableau caches1
    | true with let fired_boxes :=
        boxes
        |> List.filter (fun '(a, b) => Valuation.forces_atm V a)
        |> List.map snd
      in next_tableau (d::fired_boxes) caches1 =>
        | Solution.Unsat core caches1' =>
          JumpSolution.Unsat c core caches1'
        | Solution.Sat caches1' =>
          tableau_jumps V (Lclauses.make cpls boxes dias') mc1 next_tableau caches1'
  .
  Fail Next Obligation.



  (** Reproving this is much easier than proving the equivalence of tableau_jumps to the spec for now. *)
  Lemma jump_c_forced : forall V l0 mc1 next_tableau c core cache cache',
    tableau_jumps V l0 mc1 next_tableau cache = JumpSolution.Unsat c core cache' ->
    Valuation.forces_atm V c = true.
  Proof with auto.
    intros * Hunsat. funelim (tableau_jumps V l0 mc1 next_tableau cache); rewrite <- Heqcall in Hunsat.
    - discriminate.
    - eapply H. exact Hunsat.
    - eapply H. exact Hunsat.
    - inversion Hunsat; subst. assumption.
  Qed.


  Equations tableau
    (A : Assumptions.t)
    (s0 : CplSolver.t)
    (mc0 : Mcnf.t)
    (caches : Caches.t)
    : Solution.t
    by wf (
      List.length mc0,
      List.length (CplSolver.every_sat_valuation s0 A)
    ) lexnat2_lt
  :=
  tableau A s0 mc0 caches
  with Caches.contains caches A =>
    | true => Solution.Sat caches
    | false with inspect (CplSolver.solve_with_assumptions s0 A) =>
      | CplSolution.Unsat A' eqn:Hcsol_eq => Solution.Unsat A' caches
      | CplSolution.Sat V eqn:Hcsol_eq with mc0 =>
        | [] => Solution.Sat (Caches.add caches A)
        | (l0 :: mc1) with Caches.destruct caches =>
          | (cache0, caches1) with
            inspect (
              tableau_jumps
                V l0 mc1
                (fun A' caches1' => tableau A' (CplSolver.make_with_clauses (first_cpls mc1)) mc1 caches1')
                caches1
            ) =>
            | JumpSolution.Sat caches1' eqn:Hj_eq => Solution.Sat (Cache.add cache0 A :: caches1')
            | JumpSolution.Unsat c jump_core caches1' eqn:Hj_eq =>
              let conflict_set := conflict_set_of (l0::mc1) V c jump_core in
              let s0' := CplSolver.add_conflict_set s0 conflict_set in
              let mc0' := add_conflict_set (l0::mc1) conflict_set in
              tableau A s0' mc0' caches1'
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
    eapply jump_c_forced. exact Hj_eq.
  Qed.
  Fail Next Obligation.

  (** Solve a formula by applying [tableau] with the correct arguments. *)
  Definition solve_mcnf (mc0 : Mcnf.t) : Solution.t :=
    let cpls := first_cpls mc0 in
    let s0 := (CplSolver.make_with_clauses cpls) in
    tableau [] s0 mc0 [].


  (** Solve a [Fml.t] formula by converting first. *)
  Definition solve_fml (phi : Fml.t) : Solution.t :=
    phi |> Nnf.from_fml |> Mcnf.from_nnf |> solve_mcnf.
End Cached.
