From CegarTableaux Require Import ImportStd.
From CegarTableaux.Solver Require Import Search MchainExt.
From CegarTableaux.Solver Require Derivation.

(** Completeness of the [Spec] implementation. *)

Lemma singleton_tree_force : forall s0 A V cpls boxes mc1,
  CplSolution.Sat V = CplSolver.solve_with_assumptions s0 A ->
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


Lemma tableau_jumps_completeness : forall s0 A V l0 mc1 T1s,
  Spec.JumpSolution.Sat T1s = Spec.tableau_jumps V l0 mc1 (Spec.next_tableau mc1) ->
  (forall A' T0,
    Spec.Solution.Sat T0 = Spec.next_tableau mc1 A' ->
    Mchain.force Tree.as_kripke T0 (add_assumptions mc1 A')) ->
  s0 = CplSolver.make_with_clauses (Lclauses.cpls l0) ->
  CplSolution.Sat V = CplSolver.solve_with_assumptions s0 A ->
  Mchain.force Tree.as_kripke (Tree.make V T1s) (add_assumptions (l0::mc1) A).
Proof with try solve [ cbn in *; try easy; auto with ct datatypes ].
  intros * Hsat IHnt Hs0 Hcpl_sat.

  funelim (Spec.tableau_jumps V l0 mc1 (Spec.next_tableau mc1)); rewrite <- Heqcall in Hsat; clear Heqcall.
  - inversion Hsat. subst T1s. clear Hsat.
    cbn [Lclauses.cpls] in Hcpl_sat. eapply singleton_tree_force... exact Hcpl_sat.
  (* Model forces [cpls,boxes,dias'::mc1]. [(c,d)::dias'] is also forced as c is unfired. *)
  - specialize (H (CplSolver.make_with_clauses cpls) A T1s Hsat IHnt eq_refl Hcpl_sat).
    cbn in H |- *. repeat split...
    apply List.Forall_cons... cbn.
    intros Hforce_c. rewrite Heq in Hforce_c. discriminate.
  - discriminate.
  (* Fired dia clause. *)
  - inversion Hsat as [HT1s]. rename T1s0 into T1s, T1s into T1s', T1 into T1d. clear Hsat.
    cbn -[Mchain.force].

    cbn [Lclauses.cpls] in Hcpl_sat.
    specialize (Hind (CplSolver.make_with_clauses cpls) A T1s').
    forward Hind by symmetry; exact Heq.
    forward Hind by exact IHnt.
    forward Hind by reflexivity.
    forward Hind by exact Hcpl_sat.

    (* Hind and IHnt are useful both simplified and unsimplified. *)
    pose proof Hind as H'.
    cbn in H'. repeat rewrite List.Forall_forall in H'.
    destruct H' as [[Hforce_cpls [Hforce_boxes Hforce_dias]] Hforce_mc1].

    specialize (IHnt (d::fired_boxes (Lclauses.make cpls boxes dias'::mc1) V) T1d).
    forward IHnt by symmetry; exact Heq0.
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
  - discriminate.
Qed.


Theorem tableau_completeness : forall A s0 mc0 T,
  Spec.Solution.Sat T = Spec.tableau A s0 mc0 ->
  s0 = CplSolver.make_with_clauses (first_cpls mc0) ->
  Mchain.force Tree.as_kripke T (add_assumptions mc0 A).
Proof with try easy; auto with datatypes ct.
  intros A s0 mc0 T Hsat Hs0.

  funelim (Spec.tableau A s0 mc0); rewrite <- Heqcall in Hsat.
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
    destruct (Spec.tableau _ _ _)... inversion Hsat. subst T. clear Hsat.
    (* H assumes that T forces an over constrained formula. *)
    specialize (H T0 eq_refl).
    cbn in H |- *. intuition.
    eapply incl_Forall. 2: { exact H0. }
    apply List.incl_app.
    + apply List.incl_appl...
    + apply List.incl_appr. apply List.incl_tl...
Qed.


Corollary solve_mchain_complete_force : forall mc0 T,
  Spec.Solution.Sat T = Spec.solve_mchain mc0 ->
  Mchain.force Tree.as_kripke T mc0.
Proof.
  intros mc0 T Hsat.
  unfold Spec.solve_mchain in Hsat.
  apply tableau_completeness in Hsat; auto.
  destruct mc0.
  - cbn. apply I.
  - cbn in *. exact Hsat.
Qed.


(** The model will have valuations for more atoms than in [phi] due to the
    fresh atoms introduced by [Mcnf.from_nnf], but it is still a satisfying model. *)
Corollary solve_fml_complete_force : forall phi T,
  Spec.Solution.Sat T = Spec.solve_fml phi ->
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
  Spec.Solution.is_sat (Spec.solve_mchain mc0) = true ->
  Mchain.satisfiable mc0.
Proof with try easy.
  intros mc0 Hsat.
  unfold Spec.Solution.is_sat in Hsat.
  destruct (Spec.solve_mchain mc0) eqn:Hsol_sat...
  symmetry in Hsol_sat.
  apply solve_mchain_complete_force in Hsol_sat.
  exists _, _, Tree.as_kripke, T0. exact Hsol_sat.
Qed.


Corollary solve_fml_complete : forall phi,
  Spec.Solution.is_sat (Spec.solve_fml phi) = true ->
  Fml.satisfiable phi.
Proof with try easy.
  intros phi Hsat.
  unfold Spec.Solution.is_sat in Hsat.
  destruct (Spec.solve_fml phi) eqn:Hsol_sat...
  symmetry in Hsol_sat.
  apply solve_fml_complete_force in Hsol_sat.
  exists _, _, Tree.as_kripke, T0. exact Hsol_sat.
Qed.
