From Vct Require Import ImportStd.
From Vct.Solver Require Import McnfExt SearchBasics.
From Vct.Solver Require Derivation Spec.

(** Completeness of the [Spec] implementation. *)

Lemma singleton_tree_force : forall s0 A V cpls boxes mc1,
  CplSolver.solve_with_assumptions s0 A = CplSolution.Sat V ->
  CplSolver.clauses_of s0 = cpls ->
  Mcnf.force Tree.as_kripke (Tree.make V [])
    (Mcnf.add_A (Lclauses.make cpls boxes [] :: mc1) A).
Proof with try easy; auto with datatypes ct.
  intros * Hsat Hcpls.
  cbn. rewrite Lclauses.force_destruct.
  autorewrite with ct list prop.
  pose proof (CplSolver.solution_completeness s0 A V Hsat) as Hforce.
  unfold CplSolver.solved_clauses in Hforce.
  apply Cnf.forceb_app in Hforce as [Hforce_A Hforce_cpls].
  rewrite Hcpls in Hforce_cpls.
  repeat split...
  - rewrite Cnf.force_cpl_forceb with (V := V)...
  - rewrite Cnf.force_cpl_forceb with (V := V)...
  - rewrite List.Forall_forall.
    intros (a,b) Hab_in Hval_a w1 HR_w1.
    cbn in HR_w1. contradiction.
Qed.


Lemma force_no_assumptions : forall {W} {R} {M : @Kripke.t W R} {w0} mc0 A,
  Mcnf.force M w0 (Mcnf.add_A mc0 A) ->
  Mcnf.force M w0 mc0.
Proof.
  intros * Hforce. destruct mc0 as [|l0 mc1].
  - cbn. apply I.
  - cbn in *. autorewrite with ct in *. tauto.
Qed.


Lemma tableau_jumps_completeness : forall A V l0 mc1 T1s,
  Spec.tableau_jumps V l0 mc1 (Spec.tableau $mc1) = Spec.JumpSolution.Sat T1s ->
  (forall A' T0,
    Spec.Solution.Sat T0 = Spec.tableau $mc1 A' ->
    Mcnf.force Tree.as_kripke T0 (Mcnf.add_A mc1 A')) ->
  CplSolver.solve_with_assumptions (cpl_from_lclauses l0) A = CplSolution.Sat V ->
  Mcnf.force Tree.as_kripke (Tree.make V T1s) (Mcnf.add_A (l0::mc1) A).
Proof with try solve [ cbn in *; try easy; auto with ct datatypes ].
  intros * Hsat IHnt Hcpl_sat.

  funelim (Spec.tableau_jumps V l0 mc1 (Spec.tableau $mc1)); rewrite <- Heqcall in Hsat; clear Heqcall.
  - inv_clear Hsat. eapply singleton_tree_force... exact Hcpl_sat.
  (* Model forces [cpls,boxes,dias'::mc1]. [(c,d)::dias'] is also forced as c is unfired. *)
  - specialize (H A T1s Hsat IHnt Hcpl_sat).
    cbn in H |- *. autorewrite with ct in *.
    rewrite Lclauses.force_destruct in *.
    repeat split...
    apply List.Forall_cons... cbn.
    intros Hforce_c. rewrite Heq in Hforce_c. discriminate.
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
    cbn in H'. rewrite Lclauses.force_destruct_forall in H'.
    destruct H' as [[Hforce_cpls [Hforce_boxes Hforce_dias]] Hforce_mc1].

    specialize (IHnt (d::fired_boxes (Lclauses.make cpls boxes dias'::mc1) V) T1d).
    forward IHnt by symmetry; exact Heq0.
    pose proof IHnt as H'.
    cbn in H'. rewrite Lclauses.force_destruct_forall in H'.
    destruct H' as [[HT1d_force_cpls [HT1d_force_boxes HT1d_force_dias]] HT1d_force_mc2].

    cbn. rewrite Lclauses.force_destruct_forall.
    repeat split.
    + tauto.
    + intros (a,b) Hab_in H0_force_a T1_b HR_T1. cbn [fst snd] in *.
      cbn in HR_T1. rewrite List.in_app_iff in HR_T1.
      destruct HR_T1 as [HT1_in_T1s' | HT1_eq_d ].
      * apply (Hforce_boxes (a,b))...
      * rewrite In_singleton in HT1_eq_d. subst T1_b.
        specialize (HT1d_force_cpls [b]).
        forward HT1d_force_cpls. {
          right. rewrite List.in_app_iff. left.
          rewrite List.map_map. rewrite List.in_map_iff. exists (a, b). split...
          apply List.filter_In. split...
        }
        autorewrite with ct prop in HT1d_force_cpls.
        exact HT1d_force_cpls.
    + intros (a,b) Hab_in H0_force_a. cbn [fst snd] in *.
      destruct Hab_in as [Hab_cd | Hab_dias'].
      * inversion Hab_cd. subst a b. clear Hab_cd.
        exists T1d. split...
        specialize (HT1d_force_cpls [d]).
        forward HT1d_force_cpls by now left.
        autorewrite with ct prop in HT1d_force_cpls.
        exact HT1d_force_cpls.
      * specialize (Hforce_dias (a,b) Hab_dias').
        cbn in Hforce_dias. forward Hforce_dias by exact H0_force_a.
        destruct Hforce_dias as [T1 [HT1_in HT1_force_b]].
        exists T1...
    + setoid_rewrite List.in_app_iff. intros T1 [HT1_in_T1s' | HT1_eq_T1d].
      * apply Hforce_mc1...
      * rewrite In_singleton in HT1_eq_T1d. subst T1. eapply force_no_assumptions. exact IHnt.
  - discriminate.
Qed.


Theorem tableau_completeness_force : forall mc0 A T,
  Spec.tableau mc0 (cplsolver_mcnf mc0) A = Spec.Solution.Sat T ->
  Mcnf.force Tree.as_kripke T (Mcnf.add_A mc0 A).
Proof with try easy; auto with datatypes ct.
  intros mc0 A T Hsat.

  funelim (Spec.tableau mc0 (cplsolver_mcnf mc0) A); rewrite <- Heqcall in Hsat.
  - discriminate.
  - clear H. inversion_clear Hsat. cbn. split...
    rewrite Lclauses.force_destruct_forall.
    setoid_rewrite In_nil_iff. intuition.
    rename H into Hclause_in.

    rewrite CplClause.force_cpl_forceb with (V:=V)...
    set (s0 := CplSolver.make_with_clauses (first_cpls [])) in *.
    pose proof (CplSolver.solution_completeness s0 A V Hcsol_eq) as Hforce.
    unfold Cnf.cpl_forceb, CplSolver.solved_clauses in Hforce. =rewrite forallb_forall in Hforce.
    apply Hforce. rewrite List.in_app_iff. left.
    rewrite <- app_nil_r. exact Hclause_in.
  - clear H H0. inversion_clear Hsat.
    eapply tableau_jumps_completeness...
  - clear H0 H1.
    destruct (Spec.tableau _ _ _) eqn:Htab_cs... inv_clear Hsat.
    (* H assumes that T forces an over constrained formula. *)
    specialize (H _ _ T Htab_cs eq_refl (eq_sym Htab_cs)).
    cbn in H |- *.
    autorewrite with ct in *. split...
Qed.


Corollary solve_mcnf_complete_force : forall mc0 T,
  Spec.solve_mcnf mc0 = Spec.Solution.Sat T ->
  Mcnf.force Tree.as_kripke T mc0.
Proof.
  intros mc0 T Hsat.
  unfold Spec.solve_mcnf in Hsat.
  apply tableau_completeness_force in Hsat; auto.
  now apply force_add_no_assumptions.
Qed.


(** The model will have valuations for more atoms than in [phi] due to the
    fresh atoms introduced by [Mcnf.from_nnf], but it is still a satisfying model. *)
Corollary solve_fml_complete_force : forall phi T,
  Spec.solve_fml phi = Spec.Solution.Sat T ->
  Fml.force Tree.as_kripke T phi.
Proof.
  intros phi T Hsat.
  apply solve_mcnf_complete_force in Hsat.
  apply Nnf.equiv_fml.
  eapply Mcnf.mcnf_to_nnf_forces.
  2: { exact Hsat. }
  cbn. lia.
Qed.


Corollary tableau_completeness_sat : forall mc0 A,
  Spec.Solution.is_sat (Spec.tableau mc0 (cplsolver_mcnf mc0) A) ->
  Mcnf.satisfiable (Mcnf.add_A mc0 A).
Proof with try easy.
  intros mc0 A Hsat.
  destruct (Spec.tableau _ _ _) eqn:H...
  apply tableau_completeness_force in H...
  exists _, _, Tree.as_kripke, T0. exact H.
Qed.


Corollary solve_mcnf_complete_sat : forall mc0,
  Spec.Solution.is_sat (Spec.solve_mcnf mc0) ->
  Mcnf.satisfiable mc0.
Proof with try easy.
  intros mc0 Hsat.
  unfold Spec.Solution.is_sat in Hsat.
  destruct (Spec.solve_mcnf mc0) eqn:Hsol_sat...
  apply solve_mcnf_complete_force in Hsol_sat.
  exists _, _, Tree.as_kripke, T0. exact Hsol_sat.
Qed.


Corollary solve_fml_complete_sat : forall phi,
  Spec.Solution.is_sat (Spec.solve_fml phi) ->
  Fml.satisfiable phi.
Proof with try easy.
  intros phi Hsat.
  unfold Spec.Solution.is_sat in Hsat.
  destruct (Spec.solve_fml phi) eqn:Hsol_sat...
  apply solve_fml_complete_force in Hsol_sat.
  exists _, _, Tree.as_kripke, T0. exact Hsol_sat.
Qed.
