(** With a satisfiability cache. *)

From CegarTableaux Require Trie.
From CegarTableaux.Solver Require Import SearchBasics.
From CegarTableaux.Solver Require NoModel.
From Stdlib.Structures Require Import Orders.


Module LitOrd <: OrderedTypeFull.
  Module T <: TotalTransitiveLeBool'.
    Definition t := Lit.t.
    Definition leb := Lit.leb.
    Definition leb_total := Lit.leb_total.
    Definition leb_trans := Lit.leb_trans.
  End T.

  (* TODO: depending on how its extracted, might be more performant
      to give the full definitions manually instead of being derived
      from the above. *)
  Include Orders.TTLB_to_OTF T.
End LitOrd.


Module Cache := Trie.Make (LitOrd).


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
    | Unsat (c : nat) (core : Assumptions.t) (caches : Caches.t).


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


  Definition without_caches (s : t) : NoModel.Solution.t :=
    match s with
    | Sat _ => NoModel.Solution.Sat
    | Unsat core _ => NoModel.Solution.Unsat core
    end.


  Definition matches_nomodel (t : t) (nomodel : NoModel.Solution.t) :=
    match t, nomodel with
    | Sat _, NoModel.Solution.Sat => True
    | Unsat core _, NoModel.Solution.Unsat core' => core = core'
    | _, _ => False
    end.
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
            tableau A s0' mc0' (cache0::caches1')
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


(** * Equivalence to [NoModel] *)


Definition sat_cache (cache : Cache.t) (mc0 : Mcnf.t) : Prop :=
  forall A, Cache.contains cache A ->
  NoModel.Solution.is_sat (NoModel.tableau A (CplSolver.make_with_clauses (first_cpls mc0)) mc0).


Inductive sat_caches : Caches.t -> Mcnf.t -> Prop :=
  | sat_caches_nil : forall mc0, sat_caches [] mc0
  | sat_caches_cons : forall cache0 caches1 mc0,
    sat_cache cache0 mc0 ->
    sat_caches caches1 (next_ctx mc0) ->
    sat_caches (cache0::caches1) mc0.
Hint Constructors sat_caches : ct.


Lemma sat_caches_contains_sat : forall caches mc0 A,
  sat_caches caches mc0 ->
  Caches.contains caches A ->
  NoModel.Solution.is_sat (NoModel.tableau A (CplSolver.make_with_clauses (first_cpls mc0)) mc0).
Proof.
  intros * Hsat_caches Hcontains.
  destruct Hsat_caches.
  - cbn in Hcontains. discriminate.
  - cbn in Hcontains. now apply H.
Qed.

(* Fixpoint sat_caches (caches : Caches.t) (mc0 : Mcnf.t) : Prop :=
  match caches, mc0 with
  | [], _ => True
  | cache0::caches1, [] => sat_cache cache0 []
  | cache0::caches1, l0::mc1 => sat_cache cache0 (l0::mc1) /\ sat_caches caches1 mc1
  end. *)

(* Lemma sat_cache_empty : forall mc0, sat_cache [] mc0.
Proof.
  intros mc0 A HA_in. cbn in HA_in. discriminate.
Qed.

*)
Lemma sat_cache_add : forall cache mc0 A,
  sat_cache cache mc0 ->
  NoModel.Solution.is_sat (NoModel.tableau A (CplSolver.make_with_clauses (first_cpls mc0)) mc0) ->
  sat_cache (Cache.add cache A) mc0.
Proof with try easy; auto with datatypes.
  intros * Hsat_cache Hsat_tab A' Hcontains.
  apply Cache.add_contains_iff in Hcontains as [Hcontains | Hprefix].
  - apply Hsat_cache...
  - rewrite NoModel.tableau_sound_complete in *.
    apply incl_sat with (A' := A)...
Qed.

(*
Lemma sat_cache_prefix : forall caches mc0 A A',
  sat_cache caches mc0 ->
  is_prefix A A' ->
  Caches.contains caches A' ->
  NoModel.Solution.is_sat (NoModel.tableau A (CplSolver.make_with_clauses (first_cpls mc0)) mc0).
Proof with try easy.
  intros * Hsat_cache Hprefix Hcontains.
  apply (sat_cache_add caches mc0 A')...
  - apply Hsat_cache...
  - apply Caches.add_contains_iff. now right.
Qed. *)


(* Lemma sat_caches_empty : forall mc0, sat_caches [] mc0.
Proof. cbn. tauto. Qed. *)


Lemma sat_caches_add : forall caches mc0 A,
  sat_caches caches mc0 ->
  NoModel.Solution.is_sat (NoModel.tableau A (CplSolver.make_with_clauses (first_cpls mc0)) mc0) ->
  sat_caches (Caches.add caches A) mc0.
Proof with try easy; auto with datatypes ct.
  intros * Hsat_caches Hsat_tab.
  destruct Hsat_caches.
  - cbn. apply sat_caches_cons...
    apply sat_cache_add...
  - cbn. apply sat_caches_cons...
    apply sat_cache_add...
Qed.

(* Lemma sat_cache_prefix : forall caches mc0 A A',
  sat_cache caches mc0 ->
  is_prefix A A' ->
  Caches.contains caches A' ->
  NoModel.Solution.is_sat (NoModel.tableau A (CplSolver.make_with_clauses (first_cpls mc0)) mc0).
Proof with try easy.
  intros * Hsat_cache Hprefix Hcontains.
  apply (sat_cache_add caches mc0 A')...
  - apply Hsat_cache...
  - apply Caches.add_contains_iff. now right.
Qed. *)


(* Lemma sat_cache_ctx : forall caches l0 mc1,
  sat_cache caches (l0::mc1) -> sat_cache caches mc1.
Proof.
  intros * Hsat_cache A Hcontains_A.
  cbn in Hsat_cache. *)

(* Lemma tableau_jumps_nomodel : forall V l0 mc1 next_tableau next_tableau' caches1,
  (forall A, Solution.matches_spec (next_tableau A) (next_tableau' A)) ->
  JumpSolution.matches_spec (tableau_jumps V l0 mc1 next_tableau) (Spec.tableau_jumps V l0 mc1 next_tableau'). *)



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

Definition next_tableau mc1 := fun A' caches1' =>
  tableau A' (CplSolver.make_with_clauses (first_cpls mc1)) mc1 caches1'.



Lemma cs_preserve_sat : forall caches l0 mc1 V c jump_core,
  let cs := conflict_set_of (l0::mc1) V c jump_core in
  NoModel.tableau_jumps V l0 mc1 (NoModel.next_tableau mc1) = NoModel.JumpSolution.Unsat c jump_core ->
  sat_caches caches (l0::mc1) ->
  sat_caches caches (add_conflict_set (l0::mc1) cs).
Proof with try easy; auto with datatypes ct.
  intros * Hunsat Hsat_caches.
  rewrite <- NoModel.tableau_jumps_spec in Hunsat.

  destruct (Spec.tableau_jumps V l0 mc1 (Spec.next_tableau mc1)) eqn:Hspec...
  cbn in Hunsat. inv_clear Hunsat.
  destruct failed_dia as [c d]. cbn [fst] in cs.
  apply Soundness.tableau_jumps_deriv in Hspec as Hconds.
  apply Soundness.deriv_sound in Hconds as Hunsat.
  apply Soundness.jump_failed_dia in Hspec as Hfailed_dia.
  apply Spec.jump_c_forced in Hspec as Hforce_c.

  (* destruct l0 as [cpls boxes dias] eqn:Hl0. rewrite <- Hl0 in *. *)
  apply sat_caches_cons_iff in Hsat_caches as [Hsat_cache0 Hsat_caches1].
  apply sat_caches_cons_iff. cbn. split...

  intros A Hcontains_A.
  specialize (Hsat_cache0 A Hcontains_A).
  rewrite NoModel.tableau_sound_complete in *.

  set (mc0 := l0::mc1) in *.
  set (mc0A := add_assumptions mc0 A) in *.
  pose proof (Soundness.mcnf_resolution_cs mc0A cs) as Hresolution.

  (* TODO: this is awful *)
  replace_hyp Hresolution with (Mcnf.unsatisfiable (add_assumptions mc0A (map Lit.Pos cs)) -> Mcnf.satisfiable mc0A -> Mcnf.satisfiable (add_conflict_set mc0A cs)).
  {
    intros.
    assert (forall P Q R, (P -> Q -> R) -> (Q -> ~R -> ~P)) as Hswap by tauto.
    specialize (Hswap _ _ _ Hresolution).
    forward Hswap by assumption.
    apply NNPP. apply Hswap.
    assert (forall P, P -> ~ ~ P) by tauto.
    now apply H1.
  }

  enough (Mcnf.satisfiable (add_conflict_set mc0A cs)). {
    cbn in H |- *.
    unfold Mcnf.satisfiable in H. deex.
    exists W, R, M, w0.
    cbn in H |- *. intuition.
    eapply (Cnf.permutation_force). 2: { exact H. }
    symmetry. apply Permutation_middle.
  }

  apply Hresolution...
  intro Hsat_mc0A_cs. apply Hunsat.

  unfold Mcnf.satisfiable in *.
  deex. exists W, R, M.
  apply Soundness.force_pos_cs_forces_jump with (l0 := l0) (V := V) (c := c) (d := d) (w0 := w0).
  - exact Hfailed_dia.
  - destruct Hsat_mc0A_cs as [[Hf_cpls _] _]. cbn in Hf_cpls.
    repeat rewrite List.Forall_app in Hf_cpls. destruct Hf_cpls as [Hf_cs _].
    rewrite List.Forall_forall in Hf_cs.
    specialize (Hf_cs (CplClause.from_lit (Lit.Pos c))).
    forward Hf_cs by now left.
    rewrite CplClause.force_singleton in Hf_cs.
    now cbn in Hf_cs.
  - eapply Soundness.deriv_core_incl_A. exact Hconds.
  - apply Soundness.jump_deriv_core in Hspec. rewrite Hspec in *.
    fold mc0. fold cs.
    unfold mc0A in Hsat_mc0A_cs.
    apply force_assumptions_comm in Hsat_mc0A_cs.
    apply force_rm_assumptions in Hsat_mc0A_cs.
    exact Hsat_mc0A_cs.
Qed.


Lemma tableau_jumps_nomodel : forall V l0 mc1 next_tableau next_tableau' caches1,
  sat_caches caches1 mc1 ->
  (forall A caches, sat_caches caches mc1 -> Solution.without_caches (next_tableau A caches) = (next_tableau' A)) ->
  JumpSolution.without_caches (tableau_jumps V l0 mc1 next_tableau caches1) = NoModel.tableau_jumps V l0 mc1 next_tableau'.
Proof. Admitted.

Lemma tableau_nomodel : forall A s0 mc0 caches,
  CplSolver.make_with_clauses (first_cpls mc0) = s0 ->
  sat_caches caches mc0 ->
  Solution.without_caches (tableau A s0 mc0 caches) = NoModel.tableau A s0 mc0.
Proof with try easy; auto with datatypes ct.
  intros * Hs0 Hcaches.
  funelim (NoModel.tableau A s0 mc0).
  - clear H. cbn in *.
    simp tableau. unfold tableau_unfold_clause_1.
    destruct (Caches.contains caches A) eqn:Hcached.
    + exfalso.
      pose proof (sat_caches_contains_sat caches mc1 A Hcaches Hcached) as Hsat.
      rewrite NoModel.Solution.is_sat_eq in Hsat.
      rewrite Hsat in Heqcall. discriminate.
    + unfold tableau_unfold_clause_1_clause_2. cbn.
      dep_destruct (CplSolver.solve_with_assumptions (CplSolver.make_with_clauses (first_cpls mc1)) A) as Hs.
      * rewrite Hs in Hcsol_eq. discriminate.
      * rewrite Hs in Hcsol_eq. now inv_clear Hcsol_eq.
  - clear H. cbn in *.
    simp tableau. unfold tableau_unfold_clause_1.
    destruct (Caches.contains caches A) eqn:Hcached...
    unfold tableau_unfold_clause_1_clause_2. cbn.
    dep_destruct (CplSolver.solve_with_assumptions (CplSolver.make ()) A) as Hs...
    rewrite Hs in Hcsol_eq. discriminate.
  - clear H H0. cbn in *.
    simp tableau. unfold tableau_unfold_clause_1.
    destruct (Caches.contains caches A) eqn:Hcached...
    unfold tableau_unfold_clause_1_clause_2. cbn.
    dep_destruct (CplSolver.solve_with_assumptions (CplSolver.make_with_clauses (first_cpls (l0::mc1))) A) as Hs.
    + rewrite Hs in Hcsol_eq. inv_clear Hcsol_eq.
      cbn.
      unfold tableau_unfold_clause_1_clause_2_clause_2_clause_2.
      destruct_pair as [cache0 caches1].
      unfold tableau_unfold_clause_1_clause_2_clause_2_clause_2_clause_1.
      cbn. fold (next_tableau mc1). fold (NoModel.next_tableau mc1) in Hj_eq.
      dep_destruct (tableau_jumps V l0 mc1 (next_tableau mc1) caches1) as Hj...
      exfalso.
      (* Hj_eq and Hj contradict *)
      apply sat_caches_cons_iff in Hcaches as [Hsat_cache0 Hsat_caches1]. fold cache0 caches1 in Hsat_cache0, Hsat_caches1.
      pose proof (tableau_jumps_nomodel V l0 mc1 (next_tableau mc1) (NoModel.next_tableau mc1) caches1 Hsat_caches1).
      forward H. { intros A' caches1' Hsat_caches1'. apply Hind... }
      rewrite Hj in H. cbn in H.
      rewrite <- H in Hj_eq. discriminate.
    + rewrite Hs in Hcsol_eq. discriminate.
  (* conflict set branch *)
  - clear H0 H1.
    set (cs := (conflict_set_of (l0::mc1) V c jump_core)) in *.
    set (nomodel_call := NoModel.tableau _ _ _) in *.
    set (s0 := CplSolver.make_with_clauses (first_cpls (l0::mc1))) in *.
    set (mc0_cs := add_conflict_set (l0::mc1) cs) in *.
      assert (CplSolver.add_conflict_set s0 cs = CplSolver.make_with_clauses (first_cpls mc0_cs)) as Hs0_cs by reflexivity.

    simp tableau. unfold tableau_unfold_clause_1.
    destruct (Caches.contains caches A) eqn:Hcached.
    (* cached - adding conflict set does not invalidate this cache *)
    + cbn.
      unfold nomodel_call.
      symmetry. rewrite <- NoModel.Solution.is_sat_eq.
      rewrite Hs0_cs.
      apply sat_caches_contains_sat with (caches := caches)...
      (* TODO: what do i have here, what can i add to preconds of cs_preserve_sat *)
      apply cs_preserve_sat...

    + cbn.
      dep_destruct (CplSolver.solve_with_assumptions s0 A) as Hs.
      * rewrite Hs in Hcsol_eq. inv_clear Hcsol_eq.
        cbn.
        unfold tableau_unfold_clause_1_clause_2_clause_2_clause_2.
        destruct_pair as [cache0 caches1].
        apply sat_caches_cons_iff in Hcaches as [Hsat_cache0 Hsat_caches1]. fold cache0 caches1 in Hsat_cache0, Hsat_caches1.
        cbn. fold (next_tableau mc1). fold (NoModel.next_tableau mc1) in Hj_eq.
        pose proof (tableau_jumps_nomodel V l0 mc1 (next_tableau mc1) (NoModel.next_tableau mc1) caches1 Hsat_caches1) as Hjumps_spec.
        forward Hjumps_spec. { intros A' caches1' Hsat_caches1'. apply Hind... }
        rewrite Hj_eq in Hjumps_spec.

        dep_destruct (tableau_jumps V l0 mc1 (next_tableau mc1) caches1) as Hj.
        { rewrite Hj in Hjumps_spec... }

        rewrite Hj in Hjumps_spec. cbn in Hjumps_spec. inv_clear Hjumps_spec.
        fold cs. rename caches0 into caches1'.
        apply H...
        apply cs_preserve_sat...
        apply sat_caches_cons... 
        admit. (* TODO: needs to be jump lemma *)
Admitted.
