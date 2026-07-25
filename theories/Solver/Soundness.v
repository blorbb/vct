From Vct Require Import ImportStd.
From Vct.Solver Require Import McnfExt SearchBasics.
From Vct.Solver Require Derivation Spec.
From Vct Require Cnf.

(** Some basic properties about the solutions returned by [tableau] and [tableau_jumps].  *)

Lemma tableau_deriv_core : forall A s0 mc0 core deriv,
  Spec.tableau A s0 mc0 = Spec.Solution.Unsat core deriv ->
  Derivation.get_core deriv = core.
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

Lemma jump_failed_dia : forall V l0 mc1 failed_dia core deriv,
  Spec.tableau_jumps V l0 mc1 (Spec.tableau $mc1) = Spec.JumpSolution.Unsat failed_dia core deriv ->
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

Lemma jump_deriv_core : forall V l0 mc1 failed_dia core deriv,
  Spec.tableau_jumps V l0 mc1 (Spec.tableau $mc1) = Spec.JumpSolution.Unsat failed_dia core deriv ->
  Derivation.get_core deriv = core.
Proof.
  intros *. intros Hunsat.
  funelim (Spec.tableau_jumps V l0 mc1 (Spec.tableau $mc1));
    cbn in *; rewrite <- Heqcall in Hunsat.
  - discriminate.
  - eapply H. exact Hunsat.
  - inv_clear Hunsat.
    eapply tableau_deriv_core. exact Heq.
  - discriminate.
  - inv_clear Hunsat. eapply Hind. exact Heq.
Qed.

(** * [Derivation.conds] proofs *)

Lemma tableau_jumps_deriv_ind : forall V l0 mc1 failed_dia core deriv,
  Spec.tableau_jumps V l0 mc1 (Spec.tableau $mc1) = Spec.JumpSolution.Unsat failed_dia core deriv ->
  (forall A' core deriv,
    Spec.tableau $mc1 A' = Spec.Solution.Unsat core deriv ->
    Derivation.conds mc1 A' deriv) ->
  Derivation.conds mc1 (snd failed_dia :: fired_boxes (l0::mc1) V) deriv.
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

Lemma tableau_deriv : forall mc0 A core deriv,
  Spec.tableau mc0 (cplsolver_mcnf mc0) A = Spec.Solution.Unsat core deriv ->
  Derivation.conds mc0 A deriv.
Proof with auto.
  intros *. intros Hunsat. funelim (Spec.tableau mc0 (cplsolver_mcnf mc0) A).
  - rewrite <- Heqcall in Hunsat. injection Hunsat as _ Hderiv. subst.
    apply Derivation.IdCond. now unfold cpl_solve.
  - cbn in *. rewrite <- Heqcall in Hunsat. discriminate.
  - cbn in *. rewrite <- Heqcall in Hunsat. discriminate.
  - clear H0 H1. rewrite <- Heqcall in Hunsat.
    destruct (Spec.tableau _ _ _) eqn:Htab_cs; try discriminate.
    inv_clear Hunsat.
    apply Derivation.JumpRestartCond.
    + auto.
    + unfold first_dias. cbn. eauto using jump_failed_dia.
    + cbn. eauto using Spec.jump_c_forced.
    + apply tableau_jumps_deriv_ind with (core := jump_core).
      * apply Hj_eq.
      * apply Hind.
    + cbn [fst]. erewrite jump_deriv_core.
      2: { exact Hj_eq. }
      apply H with (core := core)...
Qed.


Corollary tableau_jumps_deriv : forall V l0 mc1 failed_dia core deriv,
  Spec.tableau_jumps V l0 mc1 (Spec.tableau $mc1) = Spec.JumpSolution.Unsat failed_dia core deriv ->
  Derivation.conds mc1 (snd failed_dia :: fired_boxes (l0::mc1) V) deriv.
Proof with try easy.
  intros * Hunsat.
  apply tableau_jumps_deriv_ind with (core := core)...
  intros A' core' deriv' Hnext_tableau.
  apply tableau_deriv with (core := core')...
Qed.



(** The derivation conditions are held for the [solve_*] functions. *)
Corollary solve_mcnf_deriv : forall phi core deriv,
  Spec.solve_mcnf phi = Spec.Solution.Unsat core deriv ->
  Derivation.conds phi [] deriv.
Proof.
  intros * Hunsat. eapply tableau_deriv. exact Hunsat.
Qed.

Corollary solve_fml_deriv : forall phi core deriv,
  Spec.solve_fml phi = Spec.Solution.Unsat core deriv ->
  Derivation.conds (phi |> Nnf.from_fml |> Mcnf.from_nnf) [] deriv.
Proof.
  intros. eapply solve_mcnf_deriv. exact H.
Qed.


(** * Soundness *)

(** A derivation that satisfies [Derivation.conds] is sound. *)

(** Some helpers to simplify unsat goals. *)

Lemma cnf_unsat_subset : forall phi, Cnf.unsatisfiable (first_cpls phi) -> Mcnf.unsatisfiable phi.
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
Lemma force_first_cpls : forall {W} {R} {M : @Kripke.t W R} {w0} mc0 cpls boxes dias,
  Mcnf.force M w0 mc0 ->
  first_ctx mc0 = Lclauses.make cpls boxes dias ->
  Cnf.force M w0 cpls.
Proof.
  intros * Hforce Hl0. destruct mc0 as [|l0 mc1]; cbn in *.
  - inv_clear Hl0. now unfold Cnf.force.
  - subst l0. unfold Lclauses.force in Hforce. apply Hforce.
Qed.

Lemma force_new_cpls : forall {W} {R} {M : @Kripke.t W R} {w0} mc0 cpls' cpls boxes dias,
  first_ctx mc0 = Lclauses.make cpls boxes dias ->
  Mcnf.force M w0 mc0 ->
  Cnf.force M w0 cpls' ->
  Mcnf.force M w0 ((Lclauses.make (cpls' ++ cpls) boxes dias) :: next_ctx mc0).
Proof with try easy.
  intros * Hl0_eq Hforce_w0 Hforce_cpls'. destruct mc0 as [|l0 mc1].
  - cbn in *. inv_clear Hl0_eq. split...
    autorewrite with ct...
  - cbn in *; subst. autorewrite with ct...
Qed.

Lemma first_ctx_destruct : forall mc0,
  first_ctx mc0 = Lclauses.make (Lclauses.cpls (first_ctx mc0)) (Lclauses.boxes (first_ctx mc0)) (Lclauses.dias (first_ctx mc0)).
Proof. intros [|[cpls boxes dias] mc1]; reflexivity. Qed.
Global Hint Resolve first_ctx_destruct : ct.

Lemma mcnf_resolution : forall mc0 (A : list Lit.t),
  Mcnf.unsatisfiable (add_assumptions mc0 A) ->
  Mcnf.unsatisfiable (add_neg_assumptions mc0 A) ->
  Mcnf.unsatisfiable mc0.
Proof with try easy; auto with ct.
  intros mc0 cs Hcs Hncs [W [R [M [w Hforce]]]].
  apply Hncs. exists W, R, M, w.
  cbn.
  autorewrite with ct. split; [split|].
  - apply not_all_some_true. intro Hf_cnf.
    apply Hcs. exists W,R,M,w. apply force_new_cpls...
  - rewrite <- first_ctx_destruct.
    now apply Mcnf.force_first_ctx.
  - destruct mc0... cbn in Hforce |- *...
Qed.

Corollary mcnf_resolution_cs : forall mc0 (cs : list Atom.t),
  Mcnf.unsatisfiable (add_conflict_set mc0 cs) ->
  Mcnf.unsatisfiable (add_assumptions mc0 (List.map Lit.Pos cs)) ->
  Mcnf.unsatisfiable mc0.
Proof.
  intros * Hcs HA. apply mcnf_resolution with (A := (List.map Lit.Pos cs)).
  - easy.
  - cbn in *. rewrite List.map_map. cbn. apply Hcs.
Qed.


Corollary force_not_A_neg_A : forall {W} {R} (M : @Kripke.t W R) (w0 : W) mc0 A,
  Mcnf.force M w0 mc0 ->
  ~ Mcnf.force M w0 (add_assumptions mc0 A) ->
  Mcnf.force M w0 (add_neg_assumptions mc0 A).
Proof with try easy; auto.
  intros * Hforce_mc0 Hnforce_A.
  unfold add_neg_assumptions, with_first_cpls.
  destruct (first_ctx mc0) as [cpls boxes dias] eqn:Hl0.
  apply (force_new_cpls mc0 [List.map Lit.negate A])...
  apply Cnf.force_singleton.
  apply not_all_some_true. intros Hforce_A. apply Hnforce_A.
  apply force_app_and. split...
Qed.



Corollary sat_not_A_neg_A : forall mc0 A,
  Mcnf.satisfiable mc0 ->
  Mcnf.unsatisfiable (add_assumptions mc0 A) ->
  Mcnf.satisfiable (add_neg_assumptions mc0 A).
Proof with try easy.
  intros * Hsat_mc0 Hunsat_mc0A.
  unfold Mcnf.satisfiable in *. deex. exists W,R,M,w0.
  apply force_not_A_neg_A...
  intro Hforce_mc0A. apply Hunsat_mc0A. now exists W,R,M,w0.
Qed.


(** ** Soundness of derivation *)

Lemma cpls_of_add_assumptions : forall mc0 A,
  first_cpls (add_assumptions mc0 A) = Cnf.from_assumptions A ++ first_cpls mc0.
Proof.
  intros. destruct mc0.
  - cbn. now rewrite List.app_nil_r.
  - destruct t; cbn. reflexivity.
Qed.

Lemma deriv_core_incl_A : forall mc0 A deriv,
  Derivation.conds mc0 A deriv ->
  List.incl (Derivation.get_core deriv) A.
Proof.
  intros * Hconds.
  induction Hconds as
    [mc0 A core Hunsat
    | mc0 A V failed_dia jump_deriv rs_deriv Hsat Hdia_in Hforce_c Hjump IHjump Hrs IHrs].
  - cbn. eapply CplSolver.core_subset_assumptions. exact Hunsat.
  - cbn. exact IHrs.
Qed.



Lemma force_pos_cs_jump : forall l0 mc1 V c d child_A {W} {R} (M : @Kripke.t W R) w0,
  let cs := conflict_set_of (l0::mc1) V c child_A in
  List.In (c,d) (Lclauses.dias l0) ->
  List.incl child_A (d :: fired_boxes (l0::mc1) V) ->
  Mcnf.force M w0 (add_assumptions (l0::mc1) (List.map Lit.Pos cs)) ->
  exists w1, (*R w0 w1 /\*) Mcnf.force M w1 (add_assumptions mc1 child_A).
Proof with try easy; auto with datatypes.
  intros * Hdia_in Hchild_A_incl Hparent_force.
  set (mc0 := l0::mc1) in *.
  destruct l0 as [cpls boxes dias] eqn:Hl0.
  cbn in *.
  autorewrite with ct in *.
  destruct Hparent_force as [[Hf_cs [Hf_cpls0 [Hf_boxes0 Hf_dias0]]] Hf_w1].

  (* get the world where the dia clause must be forced *)
  rewrite List.Forall_forall, Cnf.force_forall in *.
  specialize (Hf_dias0 (c,d) Hdia_in).
  unfold DiaClause.force in Hf_dias0.
  forward Hf_dias0. {
    cbn.
    fold (Lit.force M w0 (Lit.Pos c)).
    rewrite <- CplClause.force_singleton.
    apply Hf_cs.
    unfold cs, conflict_set_of. cbn. now left.
  }
  destruct Hf_dias0 as [w1d [HR_w1d Hw1d_force_d]]. cbn in Hw1d_force_d.

  (* w1d must be the satisfying world *)
  exists w1d. (* split... *)

  destruct (first_ctx mc1) as [cpls1 boxes1 dias1] eqn:Hl1. cbn.
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
  specialize (Hf_cs (CplClause.from_lit (Lit.Pos a))).
  rewrite CplClause.force_singleton in Hf_cs.
  apply Hf_cs.

  cbn.
  unfold Cnf.from_assumptions. apply List.in_map_iff. exists (Lit.Pos a). split...
  apply List.in_map_iff. exists a. split...

  subst cs. unfold conflict_set_of. cbn. right.
  apply List.in_map_iff. exists (a, b). split...
  repeat rewrite List.filter_In. repeat split...
  cbn. rewrite List.existsb_exists. exists b. split... apply Lit.eqb_equiv.
Qed.


Lemma sat_pos_cs_jump : forall l0 mc1 V c d child_A,
  let cs := conflict_set_of (l0::mc1) V c child_A in
  List.In (c,d) (Lclauses.dias l0) ->
  List.incl child_A (d :: fired_boxes (l0::mc1) V) ->
  Mcnf.satisfiable (add_assumptions (l0::mc1) (List.map Lit.Pos cs)) ->
  Mcnf.satisfiable (add_assumptions mc1 child_A).
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
  let cs := conflict_set_of (l0::mc1) V c child_A in
  List.In (c,d) (Lclauses.dias l0) ->
  List.incl child_A (d :: fired_boxes (l0::mc1) V) ->
  Mcnf.unsatisfiable (add_assumptions mc1 child_A) ->
  Mcnf.unsatisfiable (add_assumptions (add_assumptions (l0::mc1) A) (List.map Lit.Pos cs)).
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


Theorem deriv_sound : forall mc0 A deriv,
  Derivation.conds mc0 A deriv ->
  Mcnf.unsatisfiable (add_assumptions mc0 (Derivation.get_core deriv)).
Proof with cbn in *; try easy; auto with datatypes ct typeclass_instances.
  intros mc0 A deriv Hconds.
  induction Hconds as
    [mc0 A core Hunsat
    | mc0 A V failed_dia jump_deriv rs_deriv Hsat Hdia_in Hforce_c Hjump IHjump Hrs IHrs].
  (* CNF subset is unsatisfiable. *)
  - apply cnf_unsat_subset.

    rewrite cpls_of_add_assumptions.
    rewrite <- (CplSolver.clauses_of_make_with_clauses (first_cpls mc0)).
    unfold cpl_solve in Hunsat. set (s0 := CplSolver.make_with_clauses (first_cpls mc0)) in *.
    apply (CplSolver.solution_soundness s0 A core)...

  (* mc0 /\ cs and mc0 /\ ~cs are both unsatisfiable.
     mc0 /\ cs is from IHjump, but need to go up a modal context.
     mc0 /\ ~cs is from IHrs. *)
  - destruct failed_dia as [c d]; cbn [fst snd] in *.
    cbn [Derivation.get_core].
    set (cs := conflict_set_of mc0 V c (Derivation.get_core jump_deriv)) in *.
    apply mcnf_resolution_cs with (cs := cs).
    (* mc0 /\ ~cs *)
    + clear -IHrs.
      destruct (first_ctx mc0) as [cpls boxes dias] eqn:Hl0_eq.
      apply (mcnf_cpls IHrs).
      intros W R M w0 Hforce.
      rewrite Cnf.permutation_force. { exact Hforce. }
      symmetry. cbn. apply Permutation_middle.
    (* mc0 /\ cs *)
    + clear IHrs.
      destruct (first_ctx mc0) as [cpls boxes dias] eqn:Hl0.
      set (mc1 := next_ctx mc0) in *.
      pose proof (deriv_core_incl_A mc1 (d::fired_boxes mc0 V) jump_deriv Hjump) as Hcore_incl.

      apply unsat_pos_cs_jump with (d := d)...
Qed.


(** ** Soundness of tableau *)

Lemma tableau_sound : forall mc0 A,
  negb (Spec.Solution.is_sat (Spec.tableau mc0 (cplsolver_mcnf mc0) A)) ->
  Mcnf.unsatisfiable (add_assumptions mc0 A).
Proof with try easy.
  intros mc0 A Hunsat.
  destruct (Spec.tableau mc0 (cplsolver_mcnf mc0) A) eqn:Hsolve... clear Hunsat.
  pose proof (tableau_deriv mc0 A core deriv Hsolve) as Hconds.
  pose proof (deriv_sound mc0 A deriv Hconds) as Hunsat.
  pose proof (deriv_core_incl_A mc0 A deriv Hconds) as Hincl.
  intros Hsat. apply Hunsat. apply incl_sat with (A' := A)...
Qed.


Corollary tableau_sound_contrapos : forall mc0 A,
  Mcnf.satisfiable (add_assumptions mc0 A) ->
  Spec.Solution.is_sat (Spec.tableau mc0 (cplsolver_mcnf mc0) A).
Proof with try easy.
  intros mc0 A Hsat.
  destruct (Spec.tableau mc0 (cplsolver_mcnf mc0) A) eqn:Hunsat...
  exfalso. apply (tableau_sound mc0 A)...
  now rewrite Hunsat.
Qed.


Corollary solve_mcnf_sound : forall mc0,
  negb (Spec.Solution.is_sat (Spec.solve_mcnf mc0)) ->
  Mcnf.unsatisfiable mc0.
Proof with try easy.
  intros mc0 Hunsat. destruct (Spec.solve_mcnf mc0) eqn:Hsolve...
  clear Hunsat.
  pose proof (solve_mcnf_deriv mc0 core deriv Hsolve) as Hconds.
  pose proof (deriv_sound mc0 [] deriv Hconds) as Hunsat.
  assert (Derivation.get_core deriv = []) as Hderiv. {
    apply incl_l_nil. apply deriv_core_incl_A with (mc0 := mc0)...
  }
  rewrite Hderiv in Hunsat.
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
