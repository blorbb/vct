(** Helpers to manipulate an [Mcnf.t] for the CEGARBox implementation. *)

From Vct Require CplSolver Lit Assumptions Valuation Tree Mcnf.
From Vct Require Import ImportStd.


Definition fired_boxes (mc0 : Mcnf.t) (V : Valuation.t) :=
  Mcnf.fst_boxes mc0
  |> List.filter (fun '(a,b) => Valuation.forces_atm V a)
  |> List.map snd.

Definition box_culprits (mc0 : Mcnf.t) (V : Valuation.t) (core : Assumptions.t) :=
  Mcnf.fst_boxes mc0
  |> List.filter (fun box => Valuation.forces_atm V (fst box))
  |> List.filter (fun box => List.existsb (Lit.eqb (snd box)) core)
  |> List.map fst.
Arguments box_culprits : simpl never.


Definition cplsolver_mcnf (mc0 : Mcnf.t) :=
  CplSolver.make_with_clauses (Mcnf.fst_cpls mc0).

Definition cpl_from_lclauses (l0 : Lclauses.t) :=
  CplSolver.make_with_clauses (Lclauses.cpls l0).

Definition cpl_solve (mc0 : Mcnf.t) (A : Assumptions.t) :=
  CplSolver.solve_with_assumptions (cplsolver_mcnf mc0) A.


(** * Conflict set lemmas *)

(** The conflict set is a subset of the valuation. *)
Lemma cs_incl_V : forall mc0 V core c s A,
  CplSolution.Sat V = CplSolver.solve_with_assumptions s A ->
  Valuation.forces_atm V c ->
  List.incl (c :: box_culprits mc0 V core) V.
Proof.
  intros mc0 V core c s A Hval Hf_c.
  intros p [Hp_c | Hp_in].
  - subst p.
    unfold Valuation.forces_atm in Hf_c.
    apply List.existsb_exists in Hf_c as [l [Hl_in_val Heq_ante]].
    apply Atom.eqb_eq in Heq_ante. subst l. assumption.
  - setoid_rewrite List.in_map_iff in Hp_in.
    destruct Hp_in as [(a,b) [Ha_p Hab_in]].

    (* remove the two filters *)
    (* first filter doesn't matter, second filter shows that (fst box) is in solver V *)
    apply List.incl_filter in Hab_in.
    apply List.filter_In in Hab_in.
    destruct Hab_in as [_ Hp_in].

    cbn [fst snd] in *. subst p.
    now rewrite <- Valuation.forces_atm_iff_in.
Qed.


(** Adding a subset of a CPL solver valuation adds no new atoms to the solver state. *)
Lemma val_subset_no_new_atms : forall s A V subset,
  CplSolution.Sat V = CplSolver.solve_with_assumptions s A ->
  List.incl subset V ->
  CplSolver.clause_atms_incl (List.map Lit.Neg subset) s A.
Proof with auto.
  intros s A V subset Hval Hsubset.
  unfold List.incl in Hsubset.
  cbn. intros x Hx_in_subset.
  apply CplSolver.valuation_in_clauses with (V:=V)...

  unfold CplClause.atm_in in Hx_in_subset.

  rewrite List.map_map in Hx_in_subset. cbn in Hx_in_subset. rewrite List.map_id in Hx_in_subset.
  now apply Hsubset.
Qed.

Lemma incl_cpls_force : forall {W} {R} {M : @Kripke.t W R} {w0 : W} cpls' cpls boxes dias mc1,
  List.incl cpls' cpls ->
  Mcnf.force M w0 (Lclauses.make cpls boxes dias :: mc1) ->
  Mcnf.force M w0 (Lclauses.make cpls' boxes dias :: mc1).
Proof.
  intros * Hincl Hf_cpls.
  cbn in *. rewrite Lclauses.force_destruct in *.
  intuition.
  apply Cnf.incl_force with (A' := cpls); easy.
Qed.

Lemma incl_A_force : forall {W} {R} {M : @Kripke.t W R} {w0 : W} mc0 A A',
  List.incl A A' ->
  Mcnf.force M w0 (Mcnf.add_A mc0 A') ->
  Mcnf.force M w0 (Mcnf.add_A mc0 A).
Proof with try easy.
  intros * Hincl Hforce.
  cbn in *. autorewrite with ct in *.
  split... split...
  destruct Hforce as [[Hforce _] _].
  apply Cnf.incl_force with (A' := (Cnf.from_assumptions A'))...
  unfold Cnf.from_assumptions.
  now apply incl_map.
Qed.

Corollary incl_A_sat : forall mc0 A A',
  List.incl A A' ->
  Mcnf.satisfiable (Mcnf.add_A mc0 A') ->
  Mcnf.satisfiable (Mcnf.add_A mc0 A).
Proof.
  intros mc0 A A' Hincl Hsat.
  unfold Mcnf.satisfiable in *. deex.
  exists W, R, M, w0.
  apply incl_A_force with A'; easy.
Qed.


Lemma force_assumptions_comm : forall {W} {R} (M : @Kripke.t W R) (w0 : W) mc0 A B,
  Mcnf.force M w0 (Mcnf.add_A (Mcnf.add_A mc0 A) B) <->
  Mcnf.force M w0 (Mcnf.add_A (Mcnf.add_A mc0 B) A).
Proof.
  intros *. cbn. autorewrite with ct. intuition; repeat rewrite List.Forall_app in *; tauto.
Qed.


Lemma force_ctx_first_next : forall {W} {R} (M : @Kripke.t W R) (w0 : W) mc0,
  Mcnf.force M w0 (Mcnf.fst_mc mc0 :: Mcnf.next_mc mc0) <-> Mcnf.force M w0 mc0.
Proof.
  intros *. destruct mc0 as [|l0 mc1].
  - cbn. now autorewrite with list ct prop.
  - reflexivity.
Qed.

Lemma force_rm_assumptions : forall {W} {R} (M : @Kripke.t W R) (w0 : W) mc0 A,
  Mcnf.force M w0 (Mcnf.add_A mc0 A) ->
  Mcnf.force M w0 mc0.
Proof.
  intros * Hforce. destruct mc0 as [|l0 mc1].
  - apply I.
  - cbn in *. autorewrite with ct in *. tauto.
Qed.


Lemma force_app_and : forall {W} {R} (M : @Kripke.t W R) (w0 : W) mc0 A,
  Mcnf.force M w0 (Mcnf.add_A mc0 A) <->
  Mcnf.force M w0 mc0 /\ Cnf.force M w0 (Cnf.from_assumptions A).
Proof with try easy.
  intros *. split.
  - intro Hforce_mc0A. split.
    + cbn in *. autorewrite with ct in Hforce_mc0A. destruct mc0...
    + cbn in *. autorewrite with ct in Hforce_mc0A...
  - intros [Hforce_mc0 Hforce_A].
    cbn in *. autorewrite with ct.
    destruct mc0.
    + cbn. rewrite Lclauses.force_empty. tauto.
    + cbn in *. tauto.
Qed.


Lemma force_add_no_assumptions : forall {W} {R} (M : @Kripke.t W R) (w0 : W) mc0,
  Mcnf.force M w0 (Mcnf.add_A mc0 []) <-> Mcnf.force M w0 mc0.
Proof. intros *. destruct mc0 as [|l0 mc1]; cbn; autorewrite with ct; intuition. Qed.
Global Hint Resolve force_add_no_assumptions : ct.

Lemma sat_add_no_assumptions : forall mc0,
  Mcnf.satisfiable (Mcnf.add_A mc0 []) <-> Mcnf.satisfiable mc0.
Proof. unfold Mcnf.satisfiable. setoid_rewrite force_add_no_assumptions. tauto. Qed.
Global Hint Resolve sat_add_no_assumptions : ct.
