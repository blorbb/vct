From Vct Require Import ImportStd.
From Vct.Solver Require Import McnfExt SearchBasics.
From Vct.Solver Require Cct Spec.
From Vct Require Cnf.

(** Some basic properties about the solutions returned by [tableau] and [tableau_jumps].  *)

Lemma tableau_cct_core : forall A s0 mc0 core cct,
  Spec.tableau A s0 mc0 = Spec.Solution.Unsat core cct ->
  Cct.get_core cct = core.
Proof.
  intros *. intro Hunsat.
  funelim (Spec.tableau A s0 mc0); rewrite <- Heqcall in Hunsat.
  - inv_clear Hunsat. reflexivity.
  - discriminate.
  - discriminate.
  - destruct (Spec.tableau _ _ _).
    + discriminate.
    + inv_clear Hunsat. cbn. now apply H.
Qed.

Lemma jump_failed_dia : forall V l0 mc1 failed_dia core cct,
  Spec.tableau_jumps V l0 mc1 (Spec.tableau $mc1) = Spec.JumpSolution.Unsat failed_dia core cct ->
  List.In failed_dia (Lclauses.dias l0).
Proof.
  intros *. intro Hunsat.
  funelim (Spec.tableau_jumps V l0 mc1 (Spec.tableau $mc1));
    cbn in *; rewrite <- Heqcall in Hunsat.
  - discriminate.
  - right. eapply H. exact Hunsat.
  - left. now inv_clear Hunsat.
  - discriminate.
  - right. inv_clear Hunsat. eapply Hind. exact Heq.
Qed.

Lemma jump_cct_core : forall V l0 mc1 failed_dia core cct,
  Spec.tableau_jumps V l0 mc1 (Spec.tableau $mc1) = Spec.JumpSolution.Unsat failed_dia core cct ->
  Cct.get_core cct = core.
Proof.
  intros *. intros Hunsat.
  funelim (Spec.tableau_jumps V l0 mc1 (Spec.tableau $mc1));
    cbn in *; rewrite <- Heqcall in Hunsat.
  - discriminate.
  - eapply H. exact Hunsat.
  - inv_clear Hunsat.
    eapply tableau_cct_core. exact Heq.
  - discriminate.
  - inv_clear Hunsat. eapply Hind. exact Heq.
Qed.

(** * [Cct.wf] proofs *)

Lemma tableau_jumps_cct_ind : forall V l0 mc1 failed_dia core cct,
  Spec.tableau_jumps V l0 mc1 (Spec.tableau $mc1) = Spec.JumpSolution.Unsat failed_dia core cct ->
  (forall A' core cct,
    Spec.tableau $mc1 A' = Spec.Solution.Unsat core cct ->
    Cct.wf cct mc1 A') ->
  Cct.wf cct mc1 (snd failed_dia :: fired_boxes (l0::mc1) V).
Proof.
  intros * Hunsat IHnt.
  funelim (Spec.tableau_jumps V l0 mc1 (Spec.tableau $mc1)); rewrite <- Heqcall in Hunsat.
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
  Spec.tableau $mc0 A = Spec.Solution.Unsat core cct ->
  Cct.wf cct mc0 A.
Proof with auto.
  intros *. intros Hunsat. funelim (Spec.tableau $mc0 A).
  - rewrite <- Heqcall in Hunsat. injection Hunsat as _ Hcct. subst.
    apply Cct.LocalCond. now unfold cpl_solve.
  - cbn in *. rewrite <- Heqcall in Hunsat. discriminate.
  - cbn in *. rewrite <- Heqcall in Hunsat. discriminate.
  - clear H0 H1. rewrite <- Heqcall in Hunsat.
    destruct (Spec.tableau _ _ _) eqn:Htab_cs; try discriminate.
    inv_clear Hunsat.
    apply Cct.JumpRestartCond.
    + auto.
    + unfold Mcnf.fst_dias. cbn. eauto using jump_failed_dia.
    + cbn. eauto using Spec.jump_c_forced.
    + apply tableau_jumps_cct_ind with (core := jump_core).
      * apply Hj_eq.
      * apply Hind.
    + cbn [fst]. erewrite jump_cct_core.
      2: { exact Hj_eq. }
      apply H with (core := core)...
Qed.


Corollary tableau_jumps_cct : forall V l0 mc1 failed_dia core cct,
  Spec.tableau_jumps V l0 mc1 (Spec.tableau $mc1) = Spec.JumpSolution.Unsat failed_dia core cct ->
  Cct.wf cct mc1 (snd failed_dia :: fired_boxes (l0::mc1) V).
Proof with try easy.
  intros * Hunsat.
  apply tableau_jumps_cct_ind with (core := core)...
  intros A' core' cct' Hnext_tableau.
  apply tableau_cct with (core := core')...
Qed.



(** The cctation conditions are held for the [solve_*] functions. *)
Corollary solve_mcnf_cct : forall phi core cct,
  Spec.solve_mcnf phi = Spec.Solution.Unsat core cct ->
  Cct.wf cct phi [].
Proof.
  intros * Hunsat. eapply tableau_cct. exact Hunsat.
Qed.

Corollary solve_fml_cct : forall phi core cct,
  Spec.solve_fml phi = Spec.Solution.Unsat core cct ->
  Cct.wf cct (phi |> Nnf.from_fml |> Mcnf.from_nnf) [].
Proof.
  intros. eapply solve_mcnf_cct. exact H.
Qed.


(** * Soundness *)

(** A cctation that satisfies [Cct.wf] is sound. *)

(** Some helpers to simplify unsat goals. *)

Lemma cnf_unsat_subset : forall phi, Cnf.unsatisfiable (Mcnf.fst_cpls phi) -> Mcnf.unsatisfiable phi.
Proof.
  intros phi. induction phi as [|l0 mc1].
  - cbn. intros Hcnf_unsat Hm_sat.
    unfold Cnf.unsatisfiable, Cnf.satisfiable in Hcnf_unsat.
    unfold Mcnf.satisfiable in Hm_sat.
    destruct Hm_sat as [W [R [M [mc0 _]]]].
    apply Hcnf_unsat.
    exists W, R, M, mc0. cbn.
    now apply List.Forall_nil_iff.
  - cbn. intros Hcnf_unsat Hm_sat.
    unfold Cnf.unsatisfiable, Cnf.satisfiable in Hcnf_unsat.
    unfold Mcnf.satisfiable in Hm_sat.
    destruct Hm_sat as [W [R [M [mc0 Hforce]]]].
    apply Hcnf_unsat.
    exists W, R, M, mc0.
    cbn in Hforce.
    do 2 apply proj1 in Hforce. exact Hforce.
Qed.


Lemma mcnf_cpls : forall {cpls cpls' boxes dias mc1},
  Mcnf.unsatisfiable (Lclauses.make cpls boxes dias :: mc1) ->
  (forall W R (M : @Kripke.t W R) mc0, Cnf.force M mc0 cpls' -> Cnf.force M mc0 cpls) ->
  Mcnf.unsatisfiable (Lclauses.make cpls' boxes dias :: mc1).
Proof with try easy.
  intros * Hunsat Himpl [W [R [M [mc0 Hforce]]]]. apply Hunsat.
  exists W, R, M, mc0. cbn in Hforce |- *. split...
  rewrite Lclauses.force_destruct in *. split...
  apply Himpl...
Qed.

(** ** Resolution *)

(** Lemmas to prove that [phi /\ x] and [phi /\ ~x] being unsatisfiable implies
    that [phi] is unsatisfiable. *)

Lemma not_all_some_true : forall {W} {R} (M : @Kripke.t W R) mc0 A,
  ~ Cnf.force M mc0 (Cnf.from_assumptions A) ->
  CplClause.force M mc0 (List.map Lit.negate A).
Proof with try easy; auto.
  intros * Hforce_A.
  rewrite Cnf.force_from_assumptions in Hforce_A.
  unfold Cnf.force, CplClause.force in *.
  rewrite <- Exists_Forall_neg in Hforce_A. 2: { intro; apply classic. }
  rewrite List.Exists_map.
  rewrite List.Exists_exists in *.
  setoid_rewrite Lit.not_force_negate. exact Hforce_A.
Qed.

(** Weird definition to fit the contexts this is used in. *)
Lemma force_fst_cpls : forall {W} {R} {M : @Kripke.t W R} {w0} mc0 cpls boxes dias,
  Mcnf.force M w0 mc0 ->
  Mcnf.fst_mc mc0 = Lclauses.make cpls boxes dias ->
  Cnf.force M w0 cpls.
Proof.
  intros * Hforce Hl0. destruct mc0 as [|l0 mc1]; cbn in *.
  - inv_clear Hl0. now unfold Cnf.force.
  - subst l0. unfold Lclauses.force in Hforce. apply Hforce.
Qed.

Lemma force_new_cpls : forall {W} {R} {M : @Kripke.t W R} {w0} mc0 cpls' cpls boxes dias,
  Mcnf.fst_mc mc0 = Lclauses.make cpls boxes dias ->
  Mcnf.force M w0 mc0 ->
  Cnf.force M w0 cpls' ->
  Mcnf.force M w0 ((Lclauses.make (cpls' ++ cpls) boxes dias) :: Mcnf.next_mc mc0).
Proof with try easy.
  intros * Hl0_eq Hforce_w0 Hforce_cpls'. destruct mc0 as [|l0 mc1].
  - cbn in *. inv_clear Hl0_eq. split...
    autorewrite with ct...
  - cbn in *; subst. autorewrite with ct...
Qed.

Lemma fst_mc_destruct : forall mc0,
  Mcnf.fst_mc mc0 = Lclauses.make (Lclauses.cpls (Mcnf.fst_mc mc0)) (Lclauses.boxes (Mcnf.fst_mc mc0)) (Lclauses.dias (Mcnf.fst_mc mc0)).
Proof. intros [|[cpls boxes dias] mc1]; reflexivity. Qed.
Global Hint Resolve fst_mc_destruct : ct.

Lemma mcnf_resolution : forall mc0 (A : list Lit.t),
  Mcnf.unsatisfiable (Mcnf.add_A mc0 A) ->
  Mcnf.unsatisfiable (Mcnf.add_nA mc0 A) ->
  Mcnf.unsatisfiable mc0.
Proof with try easy; auto with ct.
  intros mc0 cs Hcs Hncs [W [R [M [w Hforce]]]].
  apply Hncs. exists W, R, M, w.
  cbn.
  autorewrite with ct. split; [split|].
  - apply not_all_some_true. intro Hf_cnf.
    apply Hcs. exists W,R,M,w. apply force_new_cpls...
  - rewrite <- fst_mc_destruct.
    now apply Mcnf.force_fst_mc.
  - destruct mc0... cbn in Hforce |- *...
Qed.

Corollary mcnf_resolution_cs : forall mc0 (cs : list Atom.t),
  Mcnf.unsatisfiable (Mcnf.add_cs mc0 cs) ->
  Mcnf.unsatisfiable (Mcnf.add_A mc0 (List.map Lit.Pos cs)) ->
  Mcnf.unsatisfiable mc0.
Proof.
  intros * Hcs HA. apply mcnf_resolution with (A := (List.map Lit.Pos cs)).
  - easy.
  - cbn in *. rewrite List.map_map. cbn. apply Hcs.
Qed.


Corollary force_not_A_neg_A : forall {W} {R} (M : @Kripke.t W R) (w0 : W) mc0 A,
  Mcnf.force M w0 mc0 ->
  ~ Mcnf.force M w0 (Mcnf.add_A mc0 A) ->
  Mcnf.force M w0 (Mcnf.add_nA mc0 A).
Proof with try easy; auto.
  intros * Hforce_mc0 Hnforce_A.
  unfold Mcnf.add_nA, Mcnf.with_fst_cpls.
  destruct (Mcnf.fst_mc mc0) as [cpls boxes dias] eqn:Hl0.
  apply (force_new_cpls mc0 [List.map Lit.negate A])...
  apply Cnf.force_singleton.
  apply not_all_some_true. intros Hforce_A. apply Hnforce_A.
  apply force_app_and. split...
Qed.



Corollary sat_not_A_neg_A : forall mc0 A,
  Mcnf.satisfiable mc0 ->
  Mcnf.unsatisfiable (Mcnf.add_A mc0 A) ->
  Mcnf.satisfiable (Mcnf.add_nA mc0 A).
Proof with try easy.
  intros * Hsat_mc0 Hunsat_mc0A.
  unfold Mcnf.satisfiable in *. deex. exists W,R,M,w0.
  apply force_not_A_neg_A...
  intro Hforce_mc0A. apply Hunsat_mc0A. now exists W,R,M,w0.
Qed.


(** ** Soundness of cctation *)

Lemma cpls_of_add_assumptions : forall mc0 A,
  Mcnf.fst_cpls (Mcnf.add_A mc0 A) = Cnf.from_assumptions A ++ Mcnf.fst_cpls mc0.
Proof.
  intros. destruct mc0.
  - cbn. now rewrite List.app_nil_r.
  - destruct t; cbn. reflexivity.
Qed.

Lemma cct_core_incl_A : forall mc0 A cct,
  Cct.wf cct mc0 A ->
  List.incl (Cct.get_core cct) A.
Proof.
  intros * Hwf.
  induction Hwf as
    [mc0 A core Hunsat
    | mc0 A V failed_dia jump_cct rs_cct Hsat Hdia_in Hforce_c Hjump IHjump Hrs IHrs].
  - cbn. eapply CplSolver.core_subset_assumptions. exact Hunsat.
  - cbn. exact IHrs.
Qed.



Lemma force_pos_cs_jump : forall l0 mc1 V c d child_A {W} {R} (M : @Kripke.t W R) w0,
  let cs := c :: box_culprits (l0::mc1) V child_A in
  List.In (c,d) (Lclauses.dias l0) ->
  List.incl child_A (d :: fired_boxes (l0::mc1) V) ->
  Mcnf.force M w0 (Mcnf.add_A (l0::mc1) (List.map Lit.Pos cs)) ->
  exists w1, (*R w0 w1 /\*) Mcnf.force M w1 (Mcnf.add_A mc1 child_A).
Proof with try easy; auto with datatypes.
  intros * Hdia_in Hchild_A_incl Hparent_force.
  set (mc0 := l0::mc1) in *.
  destruct l0 as [cpls boxes dias] eqn:Hl0.
  cbn in *.
  autorewrite with ct prop in *.
  destruct Hparent_force as [[Hf_cs [Hf_culprits [Hf_cpls0 [Hf_boxes0 Hf_dias0]]]] Hf_w1].
  cbn in Hf_cs.

  (* get the world where the dia clause must be forced *)
  rewrite List.Forall_forall, Cnf.force_forall in *.
  specialize (Hf_dias0 (c,d) Hdia_in).
  unfold DiaClause.force in Hf_dias0.
  forward Hf_dias0 by exact Hf_cs.
  destruct Hf_dias0 as [w1d [HR_w1d Hw1d_force_d]]. cbn in Hw1d_force_d.

  (* w1d must be the satisfying world *)
  exists w1d. (* split... *)

  destruct (Mcnf.fst_mc mc1) as [cpls1 boxes1 dias1] eqn:Hl1. cbn.
  apply force_new_cpls...

  rewrite Cnf.force_from_assumptions, List.Forall_forall.
  intros l Hl_in_child_A.
  (* d is forced from above *)
  pose proof (Hchild_A_incl _ Hl_in_child_A) as [Hl_d | Hl_boxes]. { now subst l. }

  (* force the boxes too *)
  rewrite List.in_map_iff in Hl_boxes.
  destruct Hl_boxes as [(a,b) [Hab Hab_in]]. cbn in Hab. subst l.
  apply List.filter_In in Hab_in as [Hab_in Hforce_a].
  apply (Hf_boxes0 (a,b))... cbn.

  (* a must also be forced *)
  specialize (Hf_culprits (CplClause.from_lit (Lit.Pos a))).
  rewrite CplClause.force_singleton in Hf_culprits.
  apply Hf_culprits.

  repeat apply List.in_map.

  apply List.in_map_iff. exists (a, b). split...
  repeat rewrite List.filter_In. repeat split...
  cbn. rewrite List.existsb_exists. exists b. split... apply Lit.eqb_equiv.
Qed.


Lemma sat_pos_cs_jump : forall l0 mc1 V c d child_A,
  let cs := c :: box_culprits (l0::mc1) V child_A in
  List.In (c,d) (Lclauses.dias l0) ->
  List.incl child_A (d :: fired_boxes (l0::mc1) V) ->
  Mcnf.satisfiable (Mcnf.add_A (l0::mc1) (List.map Lit.Pos cs)) ->
  Mcnf.satisfiable (Mcnf.add_A mc1 child_A).
Proof with try easy; auto with datatypes.
Proof.
  intros * Hdia_in Hchild_A_incl Hsat.
  unfold Mcnf.satisfiable in Hsat. deex.
  exists W, R, M.
  eapply force_pos_cs_jump.
  - exact Hdia_in.
  - exact Hchild_A_incl.
  - exact Hsat.
Qed.


(** Has an extra [A] that is basically unused as this pattern appears several times. *)
Lemma unsat_pos_cs_jump : forall l0 mc1 V c d child_A A,
  let cs := c :: box_culprits (l0::mc1) V child_A in
  List.In (c,d) (Lclauses.dias l0) ->
  List.incl child_A (d :: fired_boxes (l0::mc1) V) ->
  Mcnf.unsatisfiable (Mcnf.add_A mc1 child_A) ->
  Mcnf.unsatisfiable (Mcnf.add_A (Mcnf.add_A (l0::mc1) A) (List.map Lit.Pos cs)).
Proof with try easy; auto with datatypes.
Proof.
  intros * Hdia_in Hchild_A_incl Hunsat Hsat. apply Hunsat.
  eapply sat_pos_cs_jump.
  - exact Hdia_in.
  - exact Hchild_A_incl.
  - fold cs. unfold Mcnf.satisfiable in *. deex. exists W,R,M,w0.
    apply force_assumptions_comm in Hsat.
    apply force_rm_assumptions in Hsat.
    exact Hsat.
Qed.


Theorem cct_sound : forall mc0 A cct,
  Cct.wf cct mc0 A ->
  Mcnf.unsatisfiable (Mcnf.add_A mc0 (Cct.get_core cct)).
Proof with cbn in *; try easy; auto with datatypes ct typeclass_instances.
  intros mc0 A cct Hwf.
  induction Hwf as
    [mc0 A core Hunsat
    | mc0 A V failed_dia jump_cct rs_cct Hsat Hdia_in Hforce_c Hjump IHjump Hrs IHrs].
  (* CNF subset is unsatisfiable. *)
  - apply cnf_unsat_subset.

    rewrite cpls_of_add_assumptions.
    rewrite <- (CplSolver.clauses_of_make_with_clauses (Mcnf.fst_cpls mc0)).
    unfold cpl_solve in Hunsat. set (s0 := CplSolver.make_with_clauses (Mcnf.fst_cpls mc0)) in *.
    apply (CplSolver.solution_soundness s0 A core)...

  (* mc0 /\ cs and mc0 /\ ~cs are both unsatisfiable.
     mc0 /\ cs is from IHjump, but need to go up a modal context.
     mc0 /\ ~cs is from IHrs. *)
  - destruct failed_dia as [c d]; cbn [fst snd] in *.
    cbn [Cct.get_core].
    set (cs := c :: box_culprits mc0 V (Cct.get_core jump_cct)) in *.
    apply mcnf_resolution_cs with (cs := cs).
    (* mc0 /\ ~cs *)
    + clear -IHrs.
      destruct (Mcnf.fst_mc mc0) as [cpls boxes dias] eqn:Hl0_eq.
      apply (mcnf_cpls IHrs).
      intros W R M w0 Hforce.
      rewrite Cnf.permutation_force. { exact Hforce. }
      symmetry. cbn. apply Permutation_middle.
    (* mc0 /\ cs *)
    + clear IHrs.
      destruct (Mcnf.fst_mc mc0) as [cpls boxes dias] eqn:Hl0.
      set (mc1 := Mcnf.next_mc mc0) in *.
      pose proof (cct_core_incl_A mc1 (d::fired_boxes mc0 V) jump_cct Hjump) as Hcore_incl.

      apply unsat_pos_cs_jump with (d := d)...
Qed.


(** ** Soundness of tableau *)

Lemma tableau_sound : forall mc0 A,
  negb (Spec.Solution.is_sat (Spec.tableau $mc0 A)) ->
  Mcnf.unsatisfiable (Mcnf.add_A mc0 A).
Proof with try easy.
  intros mc0 A Hunsat.
  destruct (Spec.tableau $mc0 A) eqn:Hsolve... clear Hunsat.
  pose proof (tableau_cct mc0 A core cct Hsolve) as Hwf.
  pose proof (cct_sound mc0 A cct Hwf) as Hunsat.
  pose proof (cct_core_incl_A mc0 A cct Hwf) as Hincl.
  intros Hsat. apply Hunsat. apply incl_A_sat with (A' := A)...
Qed.


Corollary tableau_sound_contrapos : forall mc0 A,
  Mcnf.satisfiable (Mcnf.add_A mc0 A) ->
  Spec.Solution.is_sat (Spec.tableau $mc0 A).
Proof with try easy.
  intros mc0 A Hsat.
  destruct (Spec.tableau $mc0 A) eqn:Hunsat...
  exfalso. apply (tableau_sound mc0 A)...
  now rewrite Hunsat.
Qed.


Corollary solve_mcnf_sound : forall mc0,
  negb (Spec.Solution.is_sat (Spec.solve_mcnf mc0)) ->
  Mcnf.unsatisfiable mc0.
Proof with try easy.
  intros mc0 Hunsat. destruct (Spec.solve_mcnf mc0) eqn:Hsolve...
  clear Hunsat.
  pose proof (solve_mcnf_cct mc0 core cct Hsolve) as Hwf.
  pose proof (cct_sound mc0 [] cct Hwf) as Hunsat.
  assert (Cct.get_core cct = []) as Hcct. {
    apply incl_l_nil. apply cct_core_incl_A with (mc0 := mc0)...
  }
  rewrite Hcct in Hunsat.
  unfold Mcnf.unsatisfiable in *.
  now rewrite <- sat_add_no_assumptions.
Qed.


Corollary solve_fml_sound : forall phi,
  negb (Spec.Solution.is_sat (Spec.solve_fml phi)) ->
  Fml.unsatisfiable phi.
Proof.
  intros phi Hunsat Hsat.
  rewrite Nnf.equisat_fml in Hsat.
  rewrite Mcnf.equisat_nnf in Hsat.
  eapply solve_mcnf_sound.
  - exact Hunsat.
  - exact Hsat.
Qed.


Corollary solve_mcnf_sound_contrapos : forall mc0,
  Mcnf.satisfiable mc0 ->
  Spec.Solution.is_sat (Spec.solve_mcnf mc0).
Proof with try easy.
  intros mc0 Hsat. unfold Spec.Solution.is_sat.
  destruct (Spec.solve_mcnf mc0) eqn:Hunsat...
  exfalso. apply (solve_mcnf_sound mc0)...
  now rewrite Hunsat.
Qed.


Corollary solve_fml_sound_contrapos : forall phi,
  Fml.satisfiable phi ->
  Spec.Solution.is_sat (Spec.solve_fml phi).
Proof with try easy.
  intros phi. unfold Spec.solve_fml.
  rewrite Nnf.equisat_fml, Mcnf.equisat_nnf.
  apply solve_mcnf_sound_contrapos.
Qed.
