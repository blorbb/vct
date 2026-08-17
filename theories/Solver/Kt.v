(** Simple, unoptimised implementation that is easier to prove correctness of. *)

From Vct.Solver Require Import SearchBasics.
From Vct.Solver Require Spec Completeness Soundness.

Open Scope bool_scope.


Module JumpSolution := Spec.JumpSolution.
Module Solution := Spec.Solution.


Equations tableau_jumps
  (V : Valuation.t)
  (l0 : Lclauses.t)
  (mc1 : Mcnf.t)
  (next_tableau : Assumptions.t -> Solution.t)
  : JumpSolution.t
  by wf (List.length (Lclauses.dias l0)) lt
:=
tableau_jumps V (Lclauses.make _ _ []) mc1 next_tableau :=
  JumpSolution.Sat [];
tableau_jumps V (Lclauses.make cpls boxes ((c, d) :: dias')) mc1 next_tableau
with Valuation.forces_atm V c && negb (Lit.cpl_forceb V d) =>
  | false => tableau_jumps V (Lclauses.make cpls boxes dias') mc1 next_tableau
  | true with let fired_boxes :=
      boxes
      |> List.filter (fun '(a,b) => Valuation.forces_atm V a)
      |> List.map snd
    in next_tableau (d::fired_boxes) =>
      | Solution.Unsat core cct =>
        JumpSolution.Unsat (c,d) core cct
      | Solution.Sat T1 with tableau_jumps V (Lclauses.make cpls boxes dias') mc1 next_tableau =>
        (* NOTE: if making a tail-rec version of this, compose as T1s++[T1] instead. *)
        | JumpSolution.Sat T1s =>
          JumpSolution.Sat (T1::T1s)
        | JumpSolution.Unsat failed_dia core cct =>
          JumpSolution.Unsat failed_dia core cct
.
Fail Next Obligation.


Lemma jump_c_forced : forall V l0 mc1 next_tableau c d core cct,
  tableau_jumps V l0 mc1 next_tableau = JumpSolution.Unsat (c,d) core cct ->
  Valuation.forces_atm V c.
Proof.
  intros * Hunsat. funelim (tableau_jumps V l0 mc1 next_tableau); rewrite <- Heqcall in Hunsat.
  - discriminate.
  - eapply H. exact Hunsat.
  - inv_clear Hunsat. autorewrite with bool in Heq0. apply Heq0.
  - discriminate.
  - inv_clear Hunsat. eapply Hind. exact Heq.
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
with inspect (CplSolver.solve_with_assumptions s0 A) =>
  | CplSolution.Unsat A' eqn:Hcsol_eq => Solution.Unsat A' (Cct.Local A')
  | CplSolution.Sat V eqn:Hcsol_eq with mc0 =>
    | [] => Solution.Sat (Tree.make V [])
    | (l0 :: mc1) with inspect (tableau_jumps V l0 mc1 (fun A' => tableau mc1 (cplsolver_mcnf mc1) A')) =>
      | JumpSolution.Sat T1s eqn:Hj_eq => Solution.Sat (Tree.make V T1s)
      | JumpSolution.Unsat (c,d) jump_core jump_cct eqn:Hj_eq =>
        let conflict_set := c :: box_culprits (l0::mc1) V jump_core in
        let s0' := CplSolver.add_conflict_set s0 conflict_set in
        let mc0' := Mcnf.add_cs (l0::mc1) conflict_set in
        match tableau mc0' s0' A with
        | Solution.Sat T0 => Solution.Sat T0
        | Solution.Unsat rs_core rs_cct =>
          Solution.Unsat rs_core
            (Cct.JumpRestart V (c,d) jump_cct rs_cct)
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


Definition solve_mcnf (mc0 : Mcnf.t) : Solution.t :=
  let mc0_kt := Mcnf.build_kt mc0 in
  tableau mc0_kt (cplsolver_mcnf mc0_kt) [].


Definition solve_fml (phi : Fml.t) : Solution.t :=
  phi |> Nnf.from_fml |> Mcnf.from_nnf |> solve_mcnf.



(** [Mcnf.force] but a dia-clause may not be forced if [d] is forced at the current world. *)
Fixpoint weak_force {W} {R} (M : @Kripke.t W R) (w0 : W) (mc0 : Mcnf.t) :=
  match mc0 with
  | [] => True
  | Lclauses.make cpls boxes dias :: mc1 =>
    Cnf.force M w0 cpls /\
    List.Forall (BoxClause.force M w0) boxes /\
    List.Forall (fun '(c,d) => ~ (Lit.force M w0 d) -> DiaClause.force M w0 (c,d)) dias /\
    forall w1, R w0 w1 -> weak_force M w1 mc1
  end.


Lemma strong_force_weak : forall {W} {R} (M : @Kripke.t W R) (w0 : W) (mc0 : Mcnf.t),
  Mcnf.force M w0 mc0 -> weak_force M w0 mc0.
Proof with try easy; auto.
  intros *. revert w0.
  induction mc0 as [|l0 mc1 IH]...
  intros w0 Hf.
  destruct l0 as [cpls boxes dias].
  cbn in *. unfold Lclauses.force in Hf. cbn in *.
  intuition. rewrite List.Forall_forall in *.
  intros (c,d) Hcd_in H'. apply (H3 (c,d))...
Qed.


Lemma force_no_assumptions : forall {W} {R} {M : @Kripke.t W R} {w0} mc0 A,
  weak_force M w0 (Mcnf.add_A mc0 A) ->
  weak_force M w0 mc0.
Proof.
  intros * Hforce. destruct mc0 as [|[cpls boxes dias] mc1].
  - cbn. apply I.
  - cbn in *. autorewrite with ct in *. tauto.
Qed.


Lemma kt_forces_weak : forall {W} {R} (M : @Kripke.t W R) (w0 : W) (mc0 : Mcnf.t),
  weak_force M w0 (Mcnf.build_kt mc0) -> Mcnf.force (Kripke.to_kt M) w0 (Mcnf.build_kt mc0).
Proof with try easy; auto with datatypes ct.
  intros W R M w0 mc0. revert w0.
  induction mc0 as [|l0 mc1 IH]...
  intros w0 Hwf.

  assert (Lclauses.force (Kripke.to_kt M) w0 (Mcnf.fst_mc (Mcnf.build_kt (l0::mc1)))) as Hf_l0. {
    destruct l0 as [cpls boxes dias]. cbn in *. set (l0 := Lclauses.make cpls boxes dias).
    unfold Lclauses.merge, Lclauses.force in *. cbn in *.
    destruct Hwf as [Hwf_cpls [Hwf_boxes [Hwf_dias Hwf_w1]]].
    repeat rewrite List.Forall_forall in *.
    repeat split.
    - cbn. apply Hwf_cpls.
    - cbn. intros (a,b) Hab_in Hf_a w1 HR_w1. cbn in *.
      destruct HR_w1 as [HR_w1 | Hw0w1].
      + apply (Hwf_boxes (a,b))...
      + subst w1.
        rewrite Cnf.force_forall in Hwf_cpls.
        specialize (Hwf_cpls [Lit.Neg a; b]).
        forward Hwf_cpls. {
          repeat rewrite List.in_app_iff in *.
          destruct Hab_in.
          - left. right.
            rewrite List.in_map_iff.
            exists (a, b). split...
          - right. now apply Mcnf.build_kt_box_cl_in_cpls.
        }
        autorewrite with ct prop in Hwf_cpls. destruct Hwf_cpls...
    - cbn. intros (c,d) Hcd_in Hf_c.
      destruct (classic (Lit.force M w0 d)) as [Hf_d | Hnf_d].
      (* w0 already forces d *)
      + exists w0. split...
      (* w0 does not force d, so it is forced at some w1 *)
      + specialize (Hwf_dias (c,d) Hcd_in Hnf_d Hf_c).
        destruct Hwf_dias as [w1 [HR_w1 Hf_w1_d]].
        exists w1. split... now left.
  }

  destruct l0 as [cpls boxes dias]. set (l0 := Lclauses.make cpls boxes dias). cbn in *.
  unfold Lclauses.merge in *. cbn in *.
  split.
  - apply Hf_l0.
  - intros w1 HR_w1. destruct HR_w1 as [HR_w1 | HR_w1].
    + apply IH. apply Hwf. apply HR_w1.
    + subst w1.
      replace (Mcnf.build_kt mc1) with (Mcnf.next_mc (Mcnf.build_kt (l0::mc1))). 2: { apply Mcnf.next_mc_build_kt_comm. }
      apply Mcnf.force_kt_build_kt_next...
      intros w1 HR_w1.
      apply IH. apply Hwf. apply HR_w1.
Qed.



(** A copy of [Completeness.tableau_jumps_completeness] with minor modifications. *)
Lemma tableau_jumps_completeness_weak : forall A V l0 mc1 T1s,
  tableau_jumps V l0 mc1 (tableau $mc1) = JumpSolution.Sat T1s ->
  (forall A' T0,
    Solution.Sat T0 = tableau $mc1 A' ->
    weak_force Tree.as_k T0 (Mcnf.add_A mc1 A')) ->
  CplSolver.solve_with_assumptions (cpl_from_lclauses l0) A = CplSolution.Sat V ->
  weak_force Tree.as_k (Tree.make V T1s) (Mcnf.add_A (l0::mc1) A).
Proof with try easy; try congruence; try auto with ct datatypes.
  intros * Hsat IHnt Hcpl_sat.

  funelim (tableau_jumps V l0 mc1 (tableau $mc1)); rewrite <- Heqcall in Hsat; clear Heqcall.
  - inv_clear Hsat.
    apply strong_force_weak.
    eapply Completeness.singleton_tree_force... exact Hcpl_sat.
  (* Model forces [cpls,boxes,dias'::mc1]. [(c,d)::dias'] is also forced as c is unfired. *)
  - specialize (H A T1s Hsat IHnt Hcpl_sat).
    cbn in H |- *. autorewrite with ct in *.
    repeat split...
    apply List.Forall_cons...
    intros Hnf_d Hf_c.
    rewrite Lit.force_cpl_forceb with (V := V) in Hnf_d...
    autorewrite with bool in Heq.
    destruct Heq...
  - discriminate.
  (* Fired dia clause. *)
  - inversion Hsat as [HT1s]. rename T1s0 into T1s, T1s into T1s', T1 into T1d. clear Hsat.
    cbn -[Mcnf.force].

    unfold cpl_from_lclauses in Hcpl_sat. cbn [Lclauses.cpls] in Hcpl_sat.
    specialize (Hind A T1s').
    forward Hind by exact Heq.
    forward Hind by exact IHnt.
    forward Hind by exact Hcpl_sat.

    (* Hind and IHnt are useful both simplified and unsimplified. *)
    pose proof Hind as H'.
    cbn in H'.
    destruct H' as [Hforce_cpls [Hforce_boxes [Hforce_dias Hforce_mc1]]].

    specialize (IHnt (d::fired_boxes (Lclauses.make cpls boxes dias'::mc1) V) T1d).
    forward IHnt by symmetry; exact Heq0.
    pose proof IHnt as H'.
    cbn in H'.
    destruct H' as [HT1d_force_cpls [HT1d_force_boxes [HT1d_force_dias HT1d_force_mc2]]].

    cbn. repeat rewrite List.Forall_forall in *. rewrite Cnf.force_forall in *.
    repeat split.
    + tauto.
    + intros (a,b) Hab_in H0_force_a T1_b HR_T1. cbn [fst snd] in *.
      cbn in HR_T1.
      destruct HR_T1 as [HT1_eq_d | HT1_in_T1s'].
      * subst T1_b.
        specialize (HT1d_force_cpls [b]).
        forward HT1d_force_cpls. {
          right. rewrite List.in_app_iff. left.
          rewrite List.map_map. rewrite List.in_map_iff. exists (a, b). split...
          apply List.filter_In. split...
        }
        autorewrite with ct prop in HT1d_force_cpls.
        exact HT1d_force_cpls.
      * apply (Hforce_boxes (a,b))...
    + intros (a,b) Hab_in Hnf_b H0_force_a. cbn [fst snd] in *.
      destruct Hab_in as [Hab_cd | Hab_dias'].
      * inversion Hab_cd. subst a b. clear Hab_cd.
        exists T1d. split...
        specialize (HT1d_force_cpls [d]).
        forward HT1d_force_cpls by now left.
        autorewrite with ct prop in HT1d_force_cpls.
        exact HT1d_force_cpls.
      * specialize (Hforce_dias (a,b) Hab_dias' Hnf_b).
        cbn in Hforce_dias. forward Hforce_dias by exact H0_force_a.
        destruct Hforce_dias as [T1 [HT1_in HT1_force_b]].
        exists T1...
    + intros T1 [HT1_eq_T1d | HT1_in_T1s'].
      * subst T1.
        eapply force_no_assumptions. exact IHnt.
      * apply Hforce_mc1...
  - discriminate.
Qed.


(** A copy of [Completeness.tableau_completeness_force] with minor modifications. *)
Theorem tableau_completeness_force_weak : forall mc0 A T,
  tableau mc0 (cplsolver_mcnf mc0) A = Solution.Sat T ->
  weak_force Tree.as_k T (Mcnf.add_A mc0 A).
Proof with try easy; auto with datatypes ct.
  intros mc0 A T Hsat.

  funelim (tableau mc0 (cplsolver_mcnf mc0) A); rewrite <- Heqcall in Hsat.
  - discriminate.
  - clear H. inv_clear Hsat. cbn. split...
    autorewrite with ct prop.

    rewrite Cnf.force_cpl_forceb with (V:=V)...
    set (s0 := cplsolver_mcnf []) in *.
    replace (Cnf.from_assumptions A) with (CplSolver.solved_clauses s0 A).
    2: { cbn. unfold CplSolver.solved_clauses. now autorewrite with ct list. }
    apply CplSolver.solution_completeness...
  - clear H H0. inv_clear Hsat.
    eapply tableau_jumps_completeness_weak...
  - clear H0 H1.
    destruct (tableau _ _ _) eqn:Htab_cs... inv_clear Hsat.
    (* H assumes that T forces an over constrained formula. *)
    specialize (H _ _ T Htab_cs eq_refl (eq_sym Htab_cs)).
    cbn in H |- *.
    autorewrite with ct in *. split...
Qed.


Theorem tableau_completeness_force : forall mc0 A T,
  tableau $(Mcnf.build_kt mc0) A = Solution.Sat T ->
  Mcnf.force Tree.as_kt T (Mcnf.add_A (Mcnf.build_kt mc0) A).
Proof with try easy; auto with datatypes ct.
  intros * Hsat.

  unfold Tree.as_kt.
  rewrite Mcnf.add_A_build_kt_comm.
  apply kt_forces_weak.
  rewrite <- Mcnf.add_A_build_kt_comm.
  apply tableau_completeness_force_weak...
Qed.


Corollary solve_mcnf_complete_force : forall mc0 T,
  solve_mcnf mc0 = Solution.Sat T ->
  Mcnf.force Tree.as_kt T mc0.
Proof with try easy.
  intros mc0 T Hsat.
  unfold solve_mcnf in Hsat.
  apply tableau_completeness_force in Hsat.
  rewrite force_add_no_assumptions in Hsat.
  now apply Mcnf.build_kt_refl_iff.
Qed.

Corollary solve_fml_complete_sat : forall phi,
  Solution.is_sat (solve_fml phi) ->
  Fml.satisfiable_kt phi.
Proof with try easy.
  intros phi Hsat.
  destruct (solve_fml phi) eqn:Hsol_sat...
  unfold solve_fml in Hsol_sat.
  apply solve_mcnf_complete_force in Hsol_sat.
  apply Nnf.equisat_kt_fml.
  apply Mcnf.equisat_kt_nnf.

  exists _, _, _, Tree.as_kt, T0.
  exact Hsol_sat.
Qed.


(** * Soundness

    This is a copy-paste of the proofs in [Soundness.*]. *)


Lemma tableau_cct_core : forall A s0 mc0 core cct,
  tableau A s0 mc0 = Solution.Unsat core cct ->
  Cct.get_core cct = core.
Proof.
  intros *. intro Hunsat.
  funelim (tableau A s0 mc0); rewrite <- Heqcall in Hunsat.
  - inv_clear Hunsat. reflexivity.
  - discriminate.
  - discriminate.
  - destruct (tableau _ _ _).
    + discriminate.
    + inv_clear Hunsat. cbn. now apply H.
Qed.

Lemma jump_failed_dia : forall V l0 mc1 failed_dia core cct,
  tableau_jumps V l0 mc1 (tableau $mc1) = JumpSolution.Unsat failed_dia core cct ->
  List.In failed_dia (Lclauses.dias l0).
Proof.
  intros *. intro Hunsat.
  funelim (tableau_jumps V l0 mc1 (tableau $mc1));
    cbn in *; rewrite <- Heqcall in Hunsat.
  - discriminate.
  - right. eapply H. exact Hunsat.
  - left. now inv_clear Hunsat.
  - discriminate.
  - right. inv_clear Hunsat. eapply Hind. exact Heq.
Qed.

Lemma jump_cct_core : forall V l0 mc1 failed_dia core cct,
  tableau_jumps V l0 mc1 (tableau $mc1) = JumpSolution.Unsat failed_dia core cct ->
  Cct.get_core cct = core.
Proof.
  intros *. intros Hunsat.
  funelim (tableau_jumps V l0 mc1 (tableau $mc1));
    cbn in *; rewrite <- Heqcall in Hunsat.
  - discriminate.
  - eapply H. exact Hunsat.
  - inv_clear Hunsat.
    eapply tableau_cct_core. exact Heq.
  - discriminate.
  - inv_clear Hunsat. eapply Hind. exact Heq.
Qed.

Lemma tableau_jumps_cct_ind : forall V l0 mc1 failed_dia core cct,
  tableau_jumps V l0 mc1 (tableau $mc1) = JumpSolution.Unsat failed_dia core cct ->
  (forall A' core cct,
    tableau $mc1 A' = Solution.Unsat core cct ->
    Cct.wf cct mc1 A') ->
  Cct.wf cct mc1 (snd failed_dia :: fired_boxes (l0::mc1) V).
Proof.
  intros * Hunsat IHnt.
  funelim (tableau_jumps V l0 mc1 (tableau $mc1)); rewrite <- Heqcall in Hunsat.
  - discriminate.
  - eapply H.
    + exact Hunsat.
    + exact IHnt.
  - inv_clear Hunsat. cbn.
    eapply IHnt. exact Heq.
  - discriminate.
  - inv_clear Hunsat. eapply Hind.
    + exact Heq.
    + exact IHnt.
Qed.

Lemma tableau_cct : forall mc0 A core cct,
  tableau $mc0 A = Solution.Unsat core cct ->
  Cct.wf cct mc0 A.
Proof with auto.
  intros *. intros Hunsat. funelim (tableau $mc0 A).
  - rewrite <- Heqcall in Hunsat. injection Hunsat as _ Hcct. subst.
    apply Cct.LocalCond. now unfold cpl_solve.
  - cbn in *. rewrite <- Heqcall in Hunsat. discriminate.
  - cbn in *. rewrite <- Heqcall in Hunsat. discriminate.
  - clear H0 H1. rewrite <- Heqcall in Hunsat.
    destruct (tableau _ _ _) eqn:Htab_cs; try discriminate.
    inv_clear Hunsat.
    apply Cct.JumpRestartCond.
    + auto.
    + unfold Mcnf.fst_dias. cbn. eauto using jump_failed_dia.
    + cbn. eauto using jump_c_forced.
    + apply tableau_jumps_cct_ind with (core := jump_core).
      * apply Hj_eq.
      * apply Hind.
    + cbn [fst]. erewrite jump_cct_core.
      2: { exact Hj_eq. }
      apply H with (core := core)...
Qed.


Corollary tableau_jumps_cct : forall V l0 mc1 failed_dia core cct,
  tableau_jumps V l0 mc1 (tableau $mc1) = JumpSolution.Unsat failed_dia core cct ->
  Cct.wf cct mc1 (snd failed_dia :: fired_boxes (l0::mc1) V).
Proof with try easy.
  intros * Hunsat.
  apply tableau_jumps_cct_ind with (core := core)...
  intros A' core' cct' Hnext_tableau.
  apply tableau_cct with (core := core')...
Qed.

Corollary solve_mcnf_cct : forall phi core cct,
  solve_mcnf phi = Solution.Unsat core cct ->
  Cct.wf cct (Mcnf.build_kt phi) [].
Proof.
  intros * Hunsat. eapply tableau_cct. exact Hunsat.
Qed.

Corollary solve_fml_cct : forall phi core cct,
  solve_fml phi = Solution.Unsat core cct ->
  Cct.wf cct (phi |> Nnf.from_fml |> Mcnf.from_nnf |> Mcnf.build_kt) [].
Proof.
  intros. eapply solve_mcnf_cct. exact H.
Qed.



Corollary solve_mcnf_sound : forall mc0,
  negb (Solution.is_sat (solve_mcnf mc0)) ->
  Mcnf.unsatisfiable (Mcnf.build_kt mc0).
Proof with try easy.
  intros mc0 Hunsat. destruct (solve_mcnf mc0) eqn:Hsolve...
  clear Hunsat.
  pose proof (solve_mcnf_cct mc0 core cct Hsolve) as Hwf.
  pose proof (Soundness.cct_sound (Mcnf.build_kt mc0) [] cct Hwf) as Hunsat.
  assert (Cct.get_core cct = []) as Hcct. {
    apply incl_l_nil. apply Soundness.cct_core_incl_A with (mc0 := Mcnf.build_kt mc0)...
  }
  rewrite Hcct in Hunsat.
  unfold Mcnf.unsatisfiable in *.
  now rewrite <- sat_add_no_assumptions.
Qed.

Corollary solve_mcnf_sound_kt : forall mc0,
  negb (Solution.is_sat (solve_mcnf mc0)) ->
  Mcnf.unsatisfiable_kt mc0.
Proof with try easy.
  intros mc0 Hunsat. unfold Mcnf.unsatisfiable_kt.
  rewrite Mcnf.build_kt_sound_complete.
  apply solve_mcnf_sound...
Qed.

Corollary solve_fml_sound : forall phi,
  negb (Solution.is_sat (solve_fml phi)) ->
  Fml.unsatisfiable_kt phi.
Proof.
  intros phi Hunsat Hsat.
  rewrite Nnf.equisat_kt_fml in Hsat.
  rewrite Mcnf.equisat_kt_nnf in Hsat.
  eapply solve_mcnf_sound.
  - exact Hunsat.
  - rewrite <- Mcnf.build_kt_sound_complete. exact Hsat.
Qed.


Corollary solve_mcnf_sound_contrapos : forall mc0,
  Mcnf.satisfiable_kt mc0 ->
  Solution.is_sat (solve_mcnf mc0).
Proof with try easy.
  intros mc0 Hsat.
  destruct (solve_mcnf mc0) eqn:Hunsat...
  exfalso. apply (solve_mcnf_sound_kt mc0)...
  now rewrite Hunsat.
Qed.


Corollary solve_fml_sound_contrapos : forall phi,
  Fml.satisfiable_kt phi ->
  Solution.is_sat (solve_fml phi).
Proof with try easy.
  intros phi. unfold solve_fml.
  rewrite Nnf.equisat_kt_fml, Mcnf.equisat_kt_nnf.
  apply solve_mcnf_sound_contrapos.
Qed.
