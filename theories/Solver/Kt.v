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
      | Solution.Unsat core deriv =>
        JumpSolution.Unsat (c,d) core deriv
      | Solution.Sat T1 with tableau_jumps V (Lclauses.make cpls boxes dias') mc1 next_tableau =>
        (* NOTE: if making a tail-rec version of this, compose as T1s++[T1] instead. *)
        | JumpSolution.Sat T1s =>
          JumpSolution.Sat (T1::T1s)
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
  | CplSolution.Unsat A' eqn:Hcsol_eq => Solution.Unsat A' (Derivation.Local A')
  | CplSolution.Sat V eqn:Hcsol_eq with mc0 =>
    | [] => Solution.Sat (Tree.make V [])
    | (l0 :: mc1) with inspect (tableau_jumps V l0 mc1 (fun A' => tableau mc1 (cplsolver_mcnf mc1) A')) =>
      | JumpSolution.Sat T1s eqn:Hj_eq => Solution.Sat (Tree.make V T1s)
      | JumpSolution.Unsat (c,d) jump_core jump_deriv eqn:Hj_eq =>
        let conflict_set := conflict_set_of (l0::mc1) V c jump_core in
        let s0' := CplSolver.add_conflict_set s0 conflict_set in
        let mc0' := Mcnf.add_cs (l0::mc1) conflict_set in
        match tableau mc0' s0' A with
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


Definition solve_mcnf (mc0 : Mcnf.t) : Solution.t :=
  let mc0_kt := Mcnf.add_kt mc0 in
  tableau mc0_kt (cplsolver_mcnf mc0_kt) [].


Definition solve_fml (phi : Fml.t) : Solution.t :=
  phi |> Nnf.from_fml |> Mcnf.from_nnf |> solve_mcnf.


(** NOTE: the conclusion cannot be the same as usual,
    [Mcnf.force Tree.as_refl (Tree.make V T1s) (Mcnf.add_A (l0::mc1) A)].

    With the usual conclusion, the inductive step fails. We are given
    [Tree.relation_refl (Tree.make V T1s') T1] but need to prove that
    [Tree.relation_refl (Tree.make V (T1d::T1s') T1)]. The reflexive [w0 = w1]
    case is unprovable. *)
Lemma tableau_jumps_completeness_ind : forall A V l0 mc1 T1s,
  tableau_jumps V l0 mc1 (tableau $mc1) = JumpSolution.Sat T1s ->
  (forall A' T0,
    Solution.Sat T0 = tableau $mc1 A' ->
    Mcnf.force Tree.as_refl T0 (Mcnf.add_A mc1 A')) ->
  CplSolver.solve_with_assumptions (cpl_from_lclauses l0) A = CplSolution.Sat V ->
  (* Force fired boxes *)
  (forall T1 b, List.In T1 T1s -> List.In b (fired_boxes (l0::mc1) V) -> Lit.force Tree.as_refl T1 b)
  /\
  (* Exists fired dia (if d also not forced) *)
  (forall c d, List.In (c,d) (Lclauses.dias l0) ->
    Valuation.forces_atm V c ->
    Lit.cpl_forceb V d = false ->
    exists T1, List.In T1 T1s /\ Lit.force Tree.as_refl T1 d)
  /\
  (forall T1, List.In T1 T1s -> Mcnf.force Tree.as_refl T1 mc1).
Proof with try easy; try congruence; auto with ct datatypes solve_subterm.
  intros * Hsat IHnt Hcpl_sat.

  funelim (tableau_jumps V l0 mc1 (tableau $mc1)); rewrite <- Heqcall in Hsat.
  - inv_clear Hsat. cbn. tauto.
  - specialize (H A T1s Hsat IHnt Hcpl_sat).
    cbn in H |- *. repeat split...

    intros c' d' [Hcd | Hc'd'_in] Hf_c' Hnf_d'.
    { inv_clear Hcd. autorewrite with bool in Heq. destruct Heq... }
    destruct H as [_ Hdias].
    apply Hdias with (c := c')...

  - discriminate.

  (* Fired dia clause. *)
  - inv_clear Hsat. rename T1s into T1s', T1 into T1d.

    unfold cpl_from_lclauses in Hcpl_sat. cbn [Lclauses.cpls] in Hcpl_sat.
    specialize (Hind A T1s' Heq IHnt Hcpl_sat).
    destruct Hind as [Hboxes [Hdias Hmc1]].

    (* T1d forces required cpls/boxes/dias. *)
    specialize (IHnt _ _ (eq_sym Heq0)) as HT1d_f.
    (* HT1d_f unsimplified used for successor case *)
    pose proof HT1d_f as H.
    cbn in H. autorewrite with ct prop in H.
    destruct H as [[HT1d_f_d [HT1d_f_boxes HT1d_f_l1]] HT1d_f_w1].

    repeat split.
    + intros T1 b [HT1d | HT1_in] Hb_in.
      (* new dia world also forces box by IHnt *)
      * subst T1.
        rewrite Cnf.force_forall in HT1d_f_boxes.
        specialize (HT1d_f_boxes (CplClause.from_lit b)).
        rewrite CplClause.force_singleton in HT1d_f_boxes.
        apply HT1d_f_boxes.
        apply List.in_map.
        cbn in Hb_in. exact Hb_in.
      * apply Hboxes...

    + intros c' d' [Hcd | Hc'd'_in] Hf_c' Hnf_d'.
      * inv_clear Hcd. exists T1d. split...
      * specialize (Hdias c' d' Hc'd'_in Hf_c' Hnf_d').
        destruct Hdias as [T1 [HT1_in HT1_f_d]]. exists T1. split...

    + intros T1 [HT1_T1d | HT1_in]... subst T1.
      apply force_rm_assumptions in HT1d_f. exact HT1d_f.

  - discriminate.
Qed.


(* TODO: move these to mcnf module *)
Lemma in_kt_boxes_cpls : forall mc0 a b,
  List.In (a,b) (first_boxes (Mcnf.add_kt mc0)) ->
  List.In [Lit.Neg a; b] (first_cpls (Mcnf.add_kt mc0)).
Proof with try easy.
  intros * Hab_in.
  induction mc0 as [|[cpls boxes dias] mc1 IH]...
  cbn in *. unfold Lclauses.merge in *. cbn in *.
  repeat rewrite List.in_app_iff in *.
  destruct Hab_in as [Hab_in_boxes | Hab_in_boxes1].
  - left. right.
    rewrite List.in_map_iff. exists (a,b)...
  - right. apply IH...
Qed.


Lemma force_add_kt_tail : forall V T1s mc0,
  Lclauses.force Tree.as_refl (Tree.make V T1s) (Mcnf.first_ctx (Mcnf.add_kt mc0)) ->
  (forall T, List.In T T1s -> Mcnf.force Tree.as_refl T (Mcnf.next_ctx (Mcnf.add_kt mc0))) ->
  Mcnf.force Tree.as_refl (Tree.make V T1s) (Mcnf.next_ctx (Mcnf.add_kt mc0)).
Proof with try easy.
  intros V T1s mc0 Hf_l0 Hf_mc1.
  induction mc0 as [|[cpls boxes dias] mc1 IH]...

  cbn in Hf_mc1 |- *.

  destruct (Mcnf.add_kt mc1) as [|l1kt mc2kt] eqn:Hmc1...
  cbn in *. autorewrite with ct in *. rewrite Hmc1 in *. cbn in *.
  split...

  intros T1 [HT1_in | HT1].
  + specialize (Hf_mc1 T1 HT1_in). apply Hf_mc1...
  + subst T1. apply IH... intros T HT_in.
    specialize (Hf_mc1 T HT_in). apply Hf_mc1...
Qed.




Lemma tableau_jumps_completeness : forall A V mc0 l0 mc1 T1s,
  Mcnf.add_kt mc0 = l0::mc1 ->
  tableau_jumps V l0 mc1 (tableau $mc1) = JumpSolution.Sat T1s ->
  (forall A' T0,
    Solution.Sat T0 = tableau $mc1 A' ->
    Mcnf.force Tree.as_refl T0 (Mcnf.add_A mc1 A')) ->
  CplSolver.solve_with_assumptions (cpl_from_lclauses l0) A = CplSolution.Sat V ->
  Mcnf.force Tree.as_refl (Tree.make V T1s) (Mcnf.add_A (l0::mc1) A).
Proof with try easy; try congruence; auto with ct datatypes.
  intros * Hkt Hsat IHnt Hcpl_sat.

  pose proof (tableau_jumps_completeness_ind _ _ _ _ _ Hsat IHnt Hcpl_sat) as [Hboxes [Hdia Hmc1]].

  assert (Lclauses.force Tree.as_refl (Tree.make V T1s) l0) as Hf_l0. {
    destruct l0 as [cpls boxes dias].
    rewrite Lclauses.force_destruct. repeat split.

    (* forces cpls *)
    - apply CplSolver.solution_completeness in Hcpl_sat.
      unfold cpl_from_lclauses, CplSolver.solved_clauses in Hcpl_sat.
      rewrite CplSolver.clauses_of_make_with_clauses, Cnf.forceb_app in Hcpl_sat.
      rewrite Cnf.force_cpl_forceb.
      + apply Hcpl_sat.
      + cbn. reflexivity.

    (* forces boxes *)
    - rewrite List.Forall_forall.
      intros (a,b) Hab_in Hval_a T1 HR_T1.
      cbn. destruct HR_T1 as [HR_T1 | HT1].
      (* b forced at all successors. *)
      + apply Hboxes...
        cbn in Hab_in |- *.

        change (b) with (snd (a,b)).
        apply List.in_map.
        apply List.filter_In. split...

      (* T1 forces b here because of add_kt *)
      + rewrite <- HT1. cbn in Hab_in.
        rewrite Lit.force_cpl_forceb with (V := V)...
        (* replace_hyp Hval_a with (Lit.cpl_) *)
        apply CplSolver.solution_completeness in Hcpl_sat.
        unfold CplSolver.solved_clauses, cpl_from_lclauses in Hcpl_sat.
        rewrite CplSolver.clauses_of_make_with_clauses in Hcpl_sat.
        autorewrite with ct in Hcpl_sat. cbn in Hcpl_sat.
        destruct Hcpl_sat as [_ Hf_cpls].
        rewrite Cnf.forceb_forall in Hf_cpls.
        specialize (Hf_cpls [Lit.Neg a; b]).
        autorewrite with ct prop in Hf_cpls.
        forward Hf_cpls. {
          change cpls with (first_cpls (Lclauses.make cpls boxes dias :: mc1)).
          rewrite <- Hkt.
          apply in_kt_boxes_cpls.
          rewrite Hkt. cbn...
        }
        destruct Hf_cpls as [Hf_na | Hf_b]...
        cbn in Hf_na, Hval_a. =autorewrite with bool in Hf_na...

    - rewrite List.Forall_forall.
      intros (c,d) Hcd_in Hval_c.
      destruct (Lit.cpl_forceb V d) eqn:Hf_d.
      + exists (Tree.make V T1s). split...
        cbn. rewrite Lit.force_cpl_forceb with (V := V)...
      + specialize (Hdia c d Hcd_in Hval_c Hf_d).
        destruct Hdia as [T1 [HT1_in HT1_f_d]].
        exists T1. split... now left.
  }

  cbn. autorewrite with ct. split; [split|].
  - apply CplSolver.solution_completeness in Hcpl_sat.
    unfold cpl_from_lclauses, CplSolver.solved_clauses in Hcpl_sat.
    rewrite Cnf.forceb_app in Hcpl_sat.
    rewrite Cnf.force_cpl_forceb.
    + apply Hcpl_sat.
    + cbn. reflexivity.

  - apply Hf_l0.

  - intros T1 HR_T1. destruct HR_T1 as [HT1_in | HR_T1].
    + apply Hmc1. exact HT1_in.
    + subst T1.
      replace mc1 with (Mcnf.next_ctx (Mcnf.add_kt mc0)). 2: { now rewrite Hkt. }
      apply force_add_kt_tail; rewrite Hkt...
Qed.


Theorem tableau_completeness_force : forall mc0 A T,
  tableau $(Mcnf.add_kt mc0) A = Solution.Sat T ->
  Mcnf.force Tree.as_refl T (Mcnf.add_A (Mcnf.add_kt mc0) A).
Proof with try easy; auto with datatypes ct.
  intros * Hsat.

  funelim (tableau $(Mcnf.add_kt mc0) A); rewrite <- Heqcall in Hsat.
  - discriminate.
  - clear H.
    inv_clear Hsat. rewrite <- H0 in *.
    cbn. autorewrite with ct prop.
    rewrite Cnf.force_cpl_forceb with (V := V)...
    apply CplSolver.solution_completeness in Hcsol_eq.
    unfold CplSolver.solved_clauses in Hcsol_eq.
    cbn in Hcsol_eq. autorewrite with ct prop in Hcsol_eq.
    exact Hcsol_eq.

  - clear H H0.
    inv_clear Hsat.
    destruct mc0 as [| l0k mc1k]...
    destruct (Mcnf.add_kt (l0k::mc1k)) eqn:Hmc0... symmetry in H1. inv_clear H1.

    pose proof (Mcnf.add_kt_tail l0k mc1k) as Hkt_mc1.
    rewrite Hmc0 in Hkt_mc1. cbn in Hkt_mc1.

    apply tableau_jumps_completeness with (mc0 := (l0k::mc1k))...
    intros A' T Htab.
    rewrite Hkt_mc1 in Htab |- *.
    setoid_rewrite Hkt_mc1 in Hind.
    apply (Hind A')...

  - clear H0 H1. rename H2 into Hmc0.
    destruct (tableau _ _ _) eqn:Htab_cs... inv_clear Hsat.
    set (cs := conflict_set_of _ _ _ _) in *.

    (* H assumes that T forces an over constrained formula. *)
    specialize (H (Mcnf.add_cs mc0 cs) A T).
    assert (
      CplSolver.add_conflict_set (cplsolver_mcnf (Mcnf.add_kt mc0)) cs
      = cplsolver_mcnf (Mcnf.add_kt (Mcnf.add_cs mc0 cs))
    ) as Hcplsolver. { destruct mc0 as [|[cpls boxes dias] mc1k]; easy. }
    rewrite Hcplsolver in *.
    forward H. { rewrite <- Htab_cs. now rewrite Hmc0, Mcnf.add_cs_kt. }
    forward H. { now rewrite Hmc0, Mcnf.add_cs_kt. }
    forward H. { rewrite <- Htab_cs. now rewrite Hmc0, Mcnf.add_cs_kt. }
    rewrite <- Mcnf.add_cs_kt in H.
    apply incl_cpls_force with (cpls := first_cpls (Mcnf.add_A (Mcnf.add_cs (Mcnf.add_kt mc0) cs) A)).
    + rewrite <- Hmc0. cbn...
    + apply H.
Qed.


Corollary solve_mcnf_complete_force : forall mc0 T,
  solve_mcnf mc0 = Solution.Sat T ->
  Mcnf.force Tree.as_refl T mc0.
Proof with try easy.
  intros mc0 T Hsat.
  unfold solve_mcnf in Hsat.
  apply tableau_completeness_force in Hsat.
  rewrite force_add_no_assumptions in Hsat.
  now apply Mcnf.add_kt_refl.
Qed.

