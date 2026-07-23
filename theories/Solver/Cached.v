(** With a satisfiability cache. *)

From CegarTableaux Require Trie.
From CegarTableaux.Solver Require Import SearchBasics.
From CegarTableaux.Solver Require NoModel.
From Stdlib.Structures Require Import Orders.


Module Cache := Trie.Make (Lit.Ordered).


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


  Lemma add_contains_iff : forall caches prefix A,
    Caches.contains (Caches.add caches A) prefix <->
    Caches.contains caches prefix \/ is_prefix prefix A.
  Proof.
    intros *.
    destruct caches as [|cache0 caches1].
    - cbn. rewrite Cache.contains_singleton.
      split.
      + intros. tauto.
      + intros [F | H]; easy.
    - cbn. now rewrite Cache.add_contains_iff.
  Qed.
End Caches.


(** NOTE: I could make these [NoModel.Solution.t * Caches.t], but putting the
    cache within the variants make the function calls easier to [destruct]. *)
Module JumpSolution.
  Inductive t :=
    | Sat (caches : Caches.t)
    | Unsat (c : Atom.t) (core : Assumptions.t) (caches : Caches.t).


  Definition get_caches (s : t) : Caches.t :=
    match s with
    | Sat caches => caches
    | Unsat _ _ caches => caches
    end.

  Definition without_caches (s : t) : NoModel.JumpSolution.t :=
    match s with
    | Sat _ => NoModel.JumpSolution.Sat
    | Unsat c core _ => NoModel.JumpSolution.Unsat c core
    end.

  
  Lemma get_caches_sat : forall s caches,
    s = Sat caches ->
    get_caches s = caches.
  Proof. intros * Hs. subst s. reflexivity. Qed.

  Lemma get_caches_unsat : forall s c core caches,
    s = Unsat c core caches ->
    get_caches s = caches.
  Proof. intros * Hs. subst s. reflexivity. Qed.
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

  Lemma get_caches_sat : forall s caches,
    s = Sat caches ->
    get_caches s = caches.
  Proof. intros * Hs. subst s. reflexivity. Qed.

  Lemma get_caches_unsat : forall s core caches,
    s = Unsat core caches ->
    get_caches s = caches.
  Proof. intros * Hs. subst s. reflexivity. Qed.

  Definition without_caches (s : t) : NoModel.Solution.t :=
    match s with
    | Sat _ => NoModel.Solution.Sat
    | Unsat core _ => NoModel.Solution.Unsat core
    end.

  Lemma without_caches_sat : forall (s : t),
    is_sat s <->
    NoModel.Solution.is_sat (without_caches s).
  Proof. intros s. destruct s; tauto. Qed.
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
  Valuation.forces_atm V c.
Proof with auto.
  intros * Hunsat. funelim (tableau_jumps V l0 mc1 next_tableau cache); rewrite <- Heqcall in Hunsat.
  - discriminate.
  - eapply H. exact Hunsat.
  - eapply H. exact Hunsat.
  - inversion Hunsat; subst. assumption.
Qed.


Equations tableau
  (mc0 : Mcnf.t)
  (s0 : CplSolver.t)
  (A : Assumptions.t)
  (caches : Caches.t)
  : Solution.t
  by wf (
    List.length mc0,
    List.length (CplSolver.every_sat_valuation s0 A)
  ) lexnat2_lt
:=
tableau mc0 s0 A caches
with Caches.contains caches A =>
  | true => Solution.Sat caches
  | false with inspect (CplSolver.solve_with_assumptions s0 A) =>
    | CplSolution.Unsat A' eqn:Hcsol_eq => Solution.Unsat A' caches
    | CplSolution.Sat V eqn:Hcsol_eq with mc0 =>
      | [] => Solution.Sat (Caches.add caches A)
      | (l0 :: mc1) with Caches.destruct caches =>
        | (cache0, caches1) with
          let s1 := cplsolver_mcnf mc1 in
          inspect (
            tableau_jumps
              V l0 mc1
              (fun A' caches1' => tableau mc1 s1 A' caches1')
              caches1
          ) =>
          | JumpSolution.Sat caches1' eqn:Hj_eq => Solution.Sat (Cache.add cache0 A :: caches1')
          | JumpSolution.Unsat c jump_core caches1' eqn:Hj_eq =>
            let conflict_set := conflict_set_of (l0::mc1) V c jump_core in
            let s0' := CplSolver.add_conflict_set s0 conflict_set in
            let mc0' := add_conflict_set (l0::mc1) conflict_set in
            tableau mc0' s0' A (cache0::caches1')
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
  tableau mc0 (cplsolver_mcnf mc0) [] [].


(** Solve a [Fml.t] formula by converting first. *)
Definition solve_fml (phi : Fml.t) : Solution.t :=
  phi |> Nnf.from_fml |> Mcnf.from_nnf |> solve_mcnf.


(** * Equivalence to [NoModel] *)


Definition sat_cache (cache : Cache.t) (mc0 : Mcnf.t) : Prop :=
  forall A, Cache.contains cache A ->
  Mcnf.satisfiable (add_assumptions mc0 A).


Inductive sat_caches : Caches.t -> Mcnf.t -> Prop :=
  | sat_caches_nil : forall mc0, sat_caches [] mc0
  | sat_caches_cons : forall cache0 caches1 mc0,
    sat_cache cache0 mc0 ->
    sat_caches caches1 (next_ctx mc0) ->
    sat_caches (cache0::caches1) mc0.
Global Hint Constructors sat_caches : ct.


Lemma sat_caches_contains_sat : forall caches mc0 A,
  sat_caches caches mc0 ->
  Caches.contains caches A ->
  Mcnf.satisfiable (add_assumptions mc0 A).
Proof.
  intros * Hsat_caches Hcontains.
  destruct Hsat_caches.
  - cbn in Hcontains. discriminate.
  - cbn in Hcontains. now apply H.
Qed.


Lemma sat_cache_add : forall cache mc0 A,
  sat_cache cache mc0 ->
  Mcnf.satisfiable (add_assumptions mc0 A) ->
  sat_cache (Cache.add cache A) mc0.
Proof with try easy; auto with datatypes.
  intros * Hsat_cache Hsat_tab A' Hcontains.
  apply Cache.add_contains_iff in Hcontains as [Hcontains | Hprefix].
  - apply Hsat_cache...
  - apply incl_sat with (A' := A)...
Qed.


Lemma sat_caches_add : forall caches mc0 A,
  sat_caches caches mc0 ->
  Mcnf.satisfiable (add_assumptions mc0 A) ->
  sat_caches (Caches.add caches A) mc0.
Proof with try easy; auto with datatypes ct.
  intros * Hsat_caches Hsat_tab.
  destruct Hsat_caches.
  - cbn. apply sat_caches_cons...
    apply sat_cache_add...
  - cbn. apply sat_caches_cons...
    apply sat_cache_add...
Qed.


Lemma sat_caches_add_empty_mc0 : forall caches A V,
  sat_caches caches [] ->
  CplSolver.solve_with_assumptions (CplSolver.make ()) A = CplSolution.Sat V ->
  sat_caches (Caches.add caches A) [].
Proof with try easy.
  intros * Hsat_caches Hsat.
  apply sat_caches_add...

  apply CplSolver.solution_completeness in Hsat as Hcnf_force.
  unfold CplSolver.solved_clauses in Hcnf_force.
  rewrite CplSolver.make_is_empty in Hcnf_force.
  rewrite List.app_nil_r in Hcnf_force.
  apply Cnf.cpl_forceb_sat in Hcnf_force.
  unfold Cnf.satisfiable in Hcnf_force. deex. exists W,R,M,w0.
  apply force_app_and. split...
Qed.


Lemma sat_caches_cons_iff : forall caches l0 mc1,
  sat_caches caches (l0::mc1) <->
  sat_cache (fst (Caches.destruct caches)) (l0::mc1) /\ sat_caches (snd (Caches.destruct caches)) mc1.
Proof with try easy; auto with datatypes ct.
  intros *. split.
  - intros Hsat_caches. inv_clear Hsat_caches.
    + cbn. split...
    + cbn in *. split...
  - intros [Hsat_fst Hsat_snd]. destruct caches.
    + apply sat_caches_nil.
    + cbn in *. constructor...
Qed.



Lemma cs_preserve_sat : forall caches l0 mc1 V c jump_core,
  let cs := conflict_set_of (l0::mc1) V c jump_core in
  NoModel.tableau_jumps V l0 mc1 (NoModel.tableau $mc1) = NoModel.JumpSolution.Unsat c jump_core ->
  sat_caches caches (l0::mc1) ->
  sat_caches caches (add_conflict_set (l0::mc1) cs).
Proof with try easy; auto with datatypes ct.
  intros * Hunsat Hsat_caches.
  rewrite <- NoModel.tableau_jumps_spec in Hunsat.

  destruct (Spec.tableau_jumps V l0 mc1 (Spec.tableau $mc1)) eqn:Hspec...
  cbn in Hunsat. inv_clear Hunsat.
  destruct failed_dia as [c d]. cbn [fst] in cs.
  apply Soundness.tableau_jumps_deriv in Hspec as Hconds.
  apply Soundness.deriv_sound in Hconds as Hunsat.
  apply Soundness.jump_failed_dia in Hspec as Hfailed_dia.
  apply Spec.jump_c_forced in Hspec as Hforce_c.
  apply Soundness.jump_deriv_core in Hspec as Hjump_core.

  (* destruct l0 as [cpls boxes dias] eqn:Hl0. rewrite <- Hl0 in *. *)
  apply sat_caches_cons_iff in Hsat_caches as [Hsat_cache0 Hsat_caches1].
  apply sat_caches_cons_iff. cbn. split...

  intros A Hcontains_A.
  specialize (Hsat_cache0 A Hcontains_A).

  set (mc0 := l0::mc1) in *.
  set (mc0A := add_assumptions mc0 A) in *.

  enough (Mcnf.satisfiable (add_conflict_set mc0A cs)). {
    cbn in H |- *.
    unfold Mcnf.satisfiable in H. deex.
    exists W, R, M, w0.
    cbn in H |- *. intuition.
    eapply (Cnf.permutation_force). 2: { exact H. }
    symmetry. apply Permutation_middle.
  }

  rewrite add_conflict_set_neg_assumptions.
  apply Soundness.sat_not_A_neg_A...

  apply Soundness.unsat_pos_cs_jump with (d := d).
  - exact Hfailed_dia.
  - rewrite <- Hjump_core. eapply Soundness.deriv_core_incl_A. exact Hconds.
  - now rewrite Hjump_core in Hunsat.
Qed.


Lemma remove_cs_preserve_sat : forall caches mc0 cs,
  sat_caches caches (add_conflict_set mc0 cs) ->
  sat_caches caches mc0.
Proof with try easy; auto with ct.
  intros * Hsat_caches_cs.
  inv_clear Hsat_caches_cs...
  cbn in H0.
  apply sat_caches_cons...
  intros A Hcontains_A.
  specialize (H A Hcontains_A).
  unfold Mcnf.satisfiable in H. deex. exists W,R,M,w0.
  cbn in *. autorewrite with list in *. tauto.
Qed.



Definition tableau_jumps_correct V l0 mc1 caches1 :=
  JumpSolution.without_caches (tableau_jumps V l0 mc1 (tableau mc1 (cplsolver_mcnf mc1)) caches1) =
  NoModel.tableau_jumps V l0 mc1 (NoModel.tableau $mc1) /\
  sat_caches (JumpSolution.get_caches (tableau_jumps V l0 mc1 (tableau mc1 (cplsolver_mcnf mc1)) caches1)) mc1.


Definition tableau_correct mc0 A caches :=
  Solution.without_caches (tableau mc0 (cplsolver_mcnf mc0) A caches) = NoModel.tableau mc0 (cplsolver_mcnf mc0) A /\
  sat_caches (Solution.get_caches (tableau mc0 (cplsolver_mcnf mc0) A caches)) mc0.


Lemma tableau_jumps_nomodel_sat_caches : forall V l0 mc1 caches1,
  sat_caches caches1 mc1 ->
  (forall A caches, sat_caches caches mc1 -> tableau_correct mc1 A caches) ->
  tableau_jumps_correct V l0 mc1 caches1.
Proof with try easy; try congruence; auto with datatypes ct.
  intros * Hsat_caches1 Hnt_ind. unfold tableau_jumps_correct.
  funelim (NoModel.tableau_jumps V l0 mc1 (NoModel.tableau $mc1)).
  - simp tableau_jumps. cbn. easy.
  - simp tableau_jumps.
    unfold tableau_jumps_unfold_clause_2.
    rewrite Heq.
    apply H...
  (* TODO: below two cases are almost identical. maybe can merge? *)
  - simp tableau_jumps.
    unfold tableau_jumps_unfold_clause_2.
    rewrite Heq0.
    set (A := d :: boxes |> filter (fun '(a, _) => Valuation.forces_atm V a) |> map snd) in *.
    unfold tableau_jumps_unfold_clause_2_clause_2.

    pose proof (Hnt_ind A caches1 Hsat_caches1) as [Hnt_nomodel Hnt_caches]...
    (* Solution.Sat branch *)
    destruct (tableau $mc1 A caches1) eqn:Hnt.
    2: { rewrite Heq in Hnt_nomodel. discriminate. }

    rename caches into caches1'.
    apply H...

  - simp tableau_jumps.
    unfold tableau_jumps_unfold_clause_2.
    rewrite Heq0.
    set (A := d :: boxes |> filter (fun '(a, _) => Valuation.forces_atm V a) |> map snd) in *.
    unfold tableau_jumps_unfold_clause_2_clause_2.

    pose proof (Hnt_ind A caches1 Hsat_caches1) as [Hnt_nomodel Hnt_caches]...
    (* Solution.Unsat branch *)
    destruct (tableau $mc1 A caches1) eqn:Hnt.
    1: { rewrite Heq in Hnt_nomodel. discriminate. }

    rename caches into caches1'. cbn.
    rewrite Heq in Hnt_nomodel.
    cbn in Hnt_nomodel.
    inv_clear Hnt_nomodel.
    tauto.
Qed.


Lemma tableau_nomodel_sat_caches : forall mc0 A caches,
  sat_caches caches mc0 ->
  tableau_correct mc0 A caches.
Proof with try easy; try congruence; auto with datatypes ct.
  intros * Hcaches. unfold tableau_correct.

  funelim (NoModel.tableau mc0 (cplsolver_mcnf mc0) A).
  - clear H.
    simp tableau. unfold tableau_unfold_clause_1.
    destruct (Caches.contains caches A) eqn:Hcached. {
      exfalso.
      pose proof (sat_caches_contains_sat caches mc0 A Hcaches Hcached) as Hsat.
      rewrite <- NoModel.tableau_sound_complete in Hsat.
      rewrite NoModel.Solution.is_sat_eq in Hsat.
      rewrite Hsat in Heqcall. discriminate.
    }

    unfold tableau_unfold_clause_1_clause_2. cbn. split.
    + dep_destruct (CplSolver.solve_with_assumptions (cplsolver_mcnf mc0) A) as Hs...
      rewrite Hs in Hcsol_eq. now inv_clear Hcsol_eq.
    + dep_destruct (CplSolver.solve_with_assumptions (cplsolver_mcnf mc0) A) as Hs...

  - clear H. cbn in *.
    simp tableau. unfold tableau_unfold_clause_1.
    destruct (Caches.contains caches A) eqn:Hcached...

    unfold tableau_unfold_clause_1_clause_2. cbn. split.
    + dep_destruct (CplSolver.solve_with_assumptions (CplSolver.make ()) A) as Hs...
    + dep_destruct (CplSolver.solve_with_assumptions (CplSolver.make ()) A) as Hs...
      cbn. apply sat_caches_add_empty_mc0 with (V := V)...

  - clear H H0.
    simp tableau. unfold tableau_unfold_clause_1.
    destruct (Caches.contains caches A) eqn:Hcached...

    unfold tableau_unfold_clause_1_clause_2. cbn. split.
    + dep_destruct (CplSolver.solve_with_assumptions (cplsolver_mcnf (l0::mc1)) A) as Hs...
      rewrite Hs in Hcsol_eq. inv_clear Hcsol_eq.
      cbn.
      unfold tableau_unfold_clause_1_clause_2_clause_2_clause_2.
      destruct_pair as [cache0 caches1].
      unfold tableau_unfold_clause_1_clause_2_clause_2_clause_2_clause_1.
      cbn. eta.
      dep_destruct (tableau_jumps V l0 mc1 (tableau $mc1) caches1) as Hj...
      exfalso.
      (* Hj_eq and Hj contradict *)
      apply sat_caches_cons_iff in Hcaches as [Hsat_cache0 Hsat_caches1]. fold cache0 caches1 in Hsat_cache0, Hsat_caches1.

      unshelve epose proof (tableau_jumps_nomodel_sat_caches V l0 mc1 caches1 Hsat_caches1 _) as [Hjumps_nomodel Hjumps_sat_caches]. {
        intros A' caches1' Hsat_caches1'. apply Hind...
      }
      rewrite Hj in Hjumps_nomodel. cbn in Hjumps_nomodel. congruence.

    + dep_destruct (CplSolver.solve_with_assumptions (cplsolver_mcnf (l0::mc1)) A) as Hs...
      rewrite Hs in Hcsol_eq. inv_clear Hcsol_eq.
      cbn.
      unfold tableau_unfold_clause_1_clause_2_clause_2_clause_2.
      destruct_pair as [cache0 caches1].
      apply sat_caches_cons_iff in Hcaches as [Hsat_cache0 Hsat_caches1]. fold cache0 caches1 in Hsat_cache0, Hsat_caches1.
      unfold tableau_unfold_clause_1_clause_2_clause_2_clause_2_clause_1.
      cbn. eta.

      unshelve epose proof (tableau_jumps_nomodel_sat_caches V l0 mc1 caches1 Hsat_caches1 _) as [Hjumps_nomodel Hjumps_sat_caches]. {
        intros A' caches1' Hsat_caches1'. apply Hind...
      }

      dep_destruct (tableau_jumps V l0 mc1 (tableau $mc1) caches1) as Hj.
      * rename caches0 into caches1'. rewrite Hj in Hjumps_sat_caches. cbn in *.
        apply sat_caches_cons...
        apply sat_cache_add...
        rewrite <- NoModel.tableau_sound_complete.
        rewrite NoModel.Solution.is_sat_eq. exact (eq_sym Heqcall).
      * rewrite Hj in Hjumps_nomodel. rewrite Hj_eq in Hjumps_nomodel.
        cbn in Hjumps_nomodel. discriminate.

  (* conflict set branch *)
  - clear H0 H1.
    set (cs := conflict_set_of (l0::mc1) V c jump_core) in *.
    set (nomodel_call := NoModel.tableau _ _ _) in *.
    set (s0 := cplsolver_mcnf (l0::mc1)) in *.
    set (mc0_cs := add_conflict_set (l0::mc1) cs) in *.
    assert (CplSolver.add_conflict_set s0 cs = CplSolver.make_with_clauses (first_cpls mc0_cs)) as Hs0_cs by reflexivity.

    simp tableau. unfold tableau_unfold_clause_1.
    destruct (Caches.contains caches A) eqn:Hcached; split...
    (* cached - adding conflict set does not invalidate this cache *)
    + cbn.
      unfold nomodel_call.
      symmetry. rewrite <- NoModel.Solution.is_sat_eq.
      rewrite Hs0_cs. rewrite NoModel.tableau_sound_complete.
      apply sat_caches_contains_sat with (caches := caches)...
      apply cs_preserve_sat...

    + cbn.
      dep_destruct (CplSolver.solve_with_assumptions s0 A) as Hs...
      rewrite Hs in Hcsol_eq. inv_clear Hcsol_eq.
      cbn.
      unfold tableau_unfold_clause_1_clause_2_clause_2_clause_2.
      destruct_pair as [cache0 caches1].
      apply sat_caches_cons_iff in Hcaches as [Hsat_cache0 Hsat_caches1]. fold cache0 caches1 in Hsat_cache0, Hsat_caches1.
      cbn. eta.

      unshelve epose proof (tableau_jumps_nomodel_sat_caches V l0 mc1 caches1 Hsat_caches1 _) as [Hjumps_nomodel Hjumps_sat_caches]. {
        intros A' caches1' Hsat_caches1'. apply Hind...
      }
      rewrite Hj_eq in Hjumps_nomodel.

      dep_destruct (tableau_jumps V l0 mc1 (tableau $mc1) caches1) as Hj; rewrite Hj in *...

      cbn in Hjumps_nomodel. inv_clear Hjumps_nomodel.
      fold cs. rename caches0 into caches1'.
      apply H...
      apply cs_preserve_sat...

    + cbn.
      dep_destruct (CplSolver.solve_with_assumptions s0 A) as Hs...
      rewrite Hs in Hcsol_eq. inv_clear Hcsol_eq.
      cbn.
      unfold tableau_unfold_clause_1_clause_2_clause_2_clause_2.
      destruct_pair as [cache0 caches1].
      apply sat_caches_cons_iff in Hcaches as [Hsat_cache0 Hsat_caches1]. fold cache0 caches1 in Hsat_cache0, Hsat_caches1.
      cbn -[add_conflict_set]. eta.

      unshelve epose proof (tableau_jumps_nomodel_sat_caches V l0 mc1 caches1 Hsat_caches1 _) as [Hjumps_nomodel Hjumps_sat_caches]. {
        intros A' caches1' Hsat_caches1'. apply Hind...
      }
      rewrite Hj_eq in Hjumps_nomodel.

      dep_destruct (tableau_jumps V l0 mc1 (tableau $mc1) caches1) as Hj; rewrite Hj in *...

      cbn in Hjumps_nomodel. inv_clear Hjumps_nomodel.
      cbn in Hjumps_sat_caches.
      fold cs. fold mc0_cs. rename caches0 into caches1'.

      specialize (H mc0_cs A (cache0::caches1')).
      forward H. { apply cs_preserve_sat... }
      forward H by reflexivity.
      forward H by reflexivity.
      destruct H as [Hcs_nomodel Hcs_sat_caches].
      apply remove_cs_preserve_sat in Hcs_sat_caches.
      apply Hcs_sat_caches.
Qed.


Theorem tableau_sound_complete : forall mc0 A caches,
  sat_caches caches mc0 ->
  Solution.is_sat (tableau mc0 (cplsolver_mcnf mc0) A caches) <->
  Mcnf.satisfiable (add_assumptions mc0 A).
Proof.
  intros mc0 A caches Hsat_caches.
  pose proof (tableau_nomodel_sat_caches mc0 A caches Hsat_caches) as [Htableau_nomodel _].
  rewrite Solution.without_caches_sat.
  rewrite Htableau_nomodel.
  apply NoModel.tableau_sound_complete.
Qed.
