From CegarTableaux Require Import ImportStd Utils ListExt.
From CegarTableaux.Solver Require Import Search MchainExt.
From CegarTableaux.Solver Require Derivation.


Lemma singleton_tree_force : forall s0 A V cpls boxes mc1,
  CplSolver.Solution.Sat V = CplSolver.solve_with_assumptions s0 A ->
  cpls = CplSolver.clauses_of s0 ->
  Mchain.force Tree.as_kripke (Tree.make V [])
    (add_assumptions (Lclauses.make cpls boxes [] :: mc1) A).
Proof with try easy; auto with datatypes ct.
  intros * Hsat Hcpls. cbn. repeat rewrite List.Forall_forall. repeat split...
  intros clause Hclause_in.
  rewrite CplClause.force_cpl_forceb with (V := V)...
  pose proof (CplSolver.solution_completeness s0 A V Hsat) as Hforce.
  unfold Cnf.cpl_forceb, CplSolver.solved_clauses in Hforce. rewrite forallb_forall in Hforce.
  apply Hforce. subst cpls. exact Hclause_in.
Qed.


Lemma force_no_assumptions : forall {W} {R} {M : @Kripke.t W R} {w0} mc0 A,
  Mchain.force M w0 (add_assumptions mc0 A) ->
  Mchain.force M w0 mc0.
Proof.
  intros * Hforce. destruct mc0 as [|l0 mc1].
  - cbn. apply I.
  - cbn in *. intuition. rewrite List.Forall_app in H1. apply (proj2 H1).
Qed.

Lemma tableau_jumps_non_tailrec_completeness : forall s0 A V l0 mc1 T1s,
  JumpSolution.Sat T1s = tableau_jumps_non_tailrec V l0 mc1 (next_tableau mc1) ->
  (forall A' T0,
    Solution.Sat T0 = next_tableau mc1 A' ->
    Mchain.force Tree.as_kripke T0 (add_assumptions mc1 A')) ->
  s0 = CplSolver.make_with_clauses (Lclauses.cpls l0) ->
  CplSolver.Solution.Sat V = CplSolver.solve_with_assumptions s0 A ->
  Mchain.force Tree.as_kripke (Tree.make V T1s) (add_assumptions (l0::mc1) A).
Proof with try solve [ cbn in *; try easy; auto with ct datatypes ].
  intros * Hsat IHnt Hs0 Hcpl_sat.

  funelim (tableau_jumps_non_tailrec V l0 mc1 (next_tableau mc1)); rewrite <- Heqcall in Hsat; clear Heqcall.
  - inversion Hsat. subst T1s. clear Hsat.
    cbn [Lclauses.cpls] in Hcpl_sat. eapply singleton_tree_force... exact Hcpl_sat.

  - destruct (next_tableau _ _) eqn:Hnt_eq... rename T0 into T1d.
    cbn -[Mchain.force].
    destruct (tableau_jumps_non_tailrec _ _ _ _) eqn:Hcall in Hsat... rename T1s0 into T1s'.
    (* can get T1s = T1s' ++ [T1_d] if needed. *)
    inversion Hsat as [HT1s].

    cbn [Lclauses.cpls] in Hcpl_sat.
    specialize (H T1d (CplSolver.make_with_clauses cpls) A T1s').
    forward H by symmetry; exact Hcall.
    forward H by exact IHnt.
    forward H by reflexivity.
    forward H by exact Hcpl_sat.

    (* H and IHnt are useful both simplified and unsimplified. *)
    pose proof H as H'.
    cbn in H'. repeat rewrite List.Forall_forall in H'.
    destruct H' as [[Hforce_cpls [Hforce_boxes Hforce_dias]] Hforce_mc1].

    specialize (IHnt (d::fired_boxes (Lclauses.make cpls boxes dias'::mc1) V) T1d).
    forward IHnt by symmetry; exact Hnt_eq.
    pose proof IHnt as H'.
    cbn in H'. repeat rewrite List.Forall_forall in H'.
    destruct H' as [[HT1d_force_cpls [HT1d_force_boxes HT1d_force_dias]] HT1d_force_mc2].

    cbn. repeat rewrite List.Forall_forall. repeat split.
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
        cbn in HT1d_force_cpls.
        destruct HT1d_force_cpls as [b' [Hb'_eq_b Hforce_b]].
        destruct Hb'_eq_b... subst b'. exact Hforce_b.
    + intros (a,b) Hab_in H0_force_a. cbn [fst snd] in *.
      destruct Hab_in as [Hab_cd | Hab_dias'].
      * inversion Hab_cd. subst a b. clear Hab_cd.
        exists T1d. split...
        specialize (HT1d_force_cpls [d]).
        forward HT1d_force_cpls by now left.
        cbn in HT1d_force_cpls.
        destruct HT1d_force_cpls as [d' [Hd'_eq_d Hforce_d]].
        destruct Hd'_eq_d... subst d'. exact Hforce_d.
      * specialize (Hforce_dias (a,b) Hab_dias').
        cbn in Hforce_dias. forward Hforce_dias by exact H0_force_a.
        destruct Hforce_dias as [T1 [HT1_in HT1_force_b]].
        exists T1...
    + setoid_rewrite List.in_app_iff. intros T1 [HT1_in_T1s' | HT1_eq_T1d].
      * apply Hforce_mc1...
      * rewrite In_singleton in HT1_eq_T1d. subst T1. eapply force_no_assumptions. exact IHnt.

  (* unfired dia-clause. Everything is assumed via H. *)
  - specialize (H (CplSolver.make_with_clauses cpls) A T1s Hsat IHnt eq_refl Hcpl_sat).
    cbn in H |- *. repeat split...
    apply List.Forall_cons... cbn.
    intros Hforce_c. rewrite Heq in Hforce_c. discriminate.
Qed.

Lemma tableau_jumps_tailrec : forall V l0 mc1 acc next_tableau,
  tableau_jumps V l0 mc1 acc next_tableau =
  match tableau_jumps_non_tailrec V l0 mc1 next_tableau with
  | JumpSolution.Sat T1s => JumpSolution.Sat (T1s ++ acc)
  | JumpSolution.Unsat failed_dia core closedtab => JumpSolution.Unsat failed_dia core closedtab  end.
Proof with try solve [ cbn in *; try easy; auto with ct datatypes ].
  intros *.
  funelim (tableau_jumps_non_tailrec V l0 mc1 next_tableau).
  - simp tableau_jumps. reflexivity.
  - simp tableau_jumps. unfold tableau_jumps_unfold_clause_2.
    destruct (Valuation.forces_atm V c) eqn:Hatm...
    destruct (next_tableau _)...
    rewrite H... destruct (tableau_jumps_non_tailrec V _ mc1 next_tableau)...
    now rewrite <- List.app_assoc.
  - simp tableau_jumps. unfold tableau_jumps_unfold_clause_2.
    destruct (Valuation.forces_atm V c) eqn:Hatm...
Qed.


Lemma tableau_jumps_completeness : forall s0 A V l0 mc1 T1s,
  JumpSolution.Sat T1s = tableau_jumps V l0 mc1 [] (next_tableau mc1) ->
  (forall A' T0,
    Solution.Sat T0 = next_tableau mc1 A' ->
    Mchain.force Tree.as_kripke T0 (add_assumptions mc1 A')) ->
  s0 = CplSolver.make_with_clauses (Lclauses.cpls l0) ->
  CplSolver.Solution.Sat V = CplSolver.solve_with_assumptions s0 A ->
  Mchain.force Tree.as_kripke (Tree.make V T1s) (add_assumptions (l0::mc1) A).
Proof with try easy; auto with ct datatypes.
  intros * Hsat IHnt Hs0 Hcpl_sat.
  rewrite tableau_jumps_tailrec in Hsat.
  apply (tableau_jumps_non_tailrec_completeness s0).
  - destruct (tableau_jumps_non_tailrec _ _ _ _)...
    inversion_clear Hsat. f_equal...
  - exact IHnt.
  - exact Hs0.
  - exact Hcpl_sat.
Qed.


Theorem tableau_completeness : forall A s0 mc0 T,
  Solution.Sat T = tableau A s0 mc0 ->
  s0 = CplSolver.make_with_clauses (first_cpls mc0) ->
  Mchain.force Tree.as_kripke T (add_assumptions mc0 A).
Proof with try easy; auto with datatypes ct.
  intros A s0 mc0 T Hsat Hs0.

  funelim (tableau A s0 mc0); rewrite <- Heqcall in Hsat.
  - discriminate.
  - clear H. inversion_clear Hsat. cbn. intuition.
    rewrite List.Forall_forall. intros clause Hclause_in.
    rewrite CplClause.force_cpl_forceb with (V:=V)...
    set (s0 := CplSolver.make_with_clauses (first_cpls [])) in *.
    pose proof (CplSolver.solution_completeness s0 A V (eq_sym Hcsol_eq)) as Hforce.
    unfold Cnf.cpl_forceb, CplSolver.solved_clauses in Hforce. rewrite forallb_forall in Hforce.
    apply Hforce. rewrite List.in_app_iff. left.
    rewrite <- app_nil_r. exact Hclause_in.
  - clear H H0. inversion_clear Hsat.
    eapply tableau_jumps_completeness...
  - clear H0 H1.
    destruct (tableau _ _ _)... inversion Hsat. subst T. clear Hsat.
    (* H assumes that T forces an over constrained formula. *)
    specialize (H T0 eq_refl).
    cbn in H |- *. intuition.
    eapply incl_Forall. 2: { exact H0. }
    apply List.incl_app.
    + apply List.incl_appl...
    + apply List.incl_appr. apply List.incl_tl...
Qed.


Corollary solve_mchain_complete_force : forall mc0 T,
  Solution.Sat T = solve_mchain mc0 ->
  Mchain.force Tree.as_kripke T mc0.
Proof.
  intros mc0 T Hsat.
  unfold solve_mchain in Hsat.
  apply tableau_completeness in Hsat; auto.
  destruct mc0.
  - cbn. apply I.
  - cbn in *. exact Hsat.
Qed.


(** The model will have valuations for more atoms than in [phi] due to the
    fresh atoms introduced by [Mcnf.from_nnf], but it is still a satisfying model. *)
Corollary solve_fml_complete_force : forall phi T,
  Solution.Sat T = solve_fml phi ->
  Fml.force Tree.as_kripke T phi.
Proof.
  intros phi T Hsat.
  apply solve_mchain_complete_force in Hsat.
  apply Nnf.equiv_fml.
  eapply Mcnf.mcnf_to_nnf_forces.
  2: { rewrite Mchain.equiv_mcnf. exact Hsat. }
  cbn. lia.
Qed.


Corollary solve_mchain_complete : forall mc0,
  Solution.is_sat (solve_mchain mc0) ->
  Mchain.satisfiable mc0.
Proof with try easy.
  intros mc0 Hsat.
  unfold Solution.is_sat in Hsat.
  destruct (solve_mchain mc0) eqn:Hsol_sat...
  symmetry in Hsol_sat.
  apply solve_mchain_complete_force in Hsol_sat.
  exists _, _, Tree.as_kripke, T0. exact Hsol_sat.
Qed.


Corollary solve_fml_complete : forall phi,
  Solution.is_sat (solve_fml phi) ->
  Fml.satisfiable phi.
Proof with try easy.
  intros phi Hsat.
  unfold Solution.is_sat in Hsat.
  destruct (solve_fml phi) eqn:Hsol_sat...
  symmetry in Hsol_sat.
  apply solve_fml_complete_force in Hsol_sat.
  exists _, _, Tree.as_kripke, T0. exact Hsol_sat.
Qed.
