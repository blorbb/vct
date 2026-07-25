(** Helpers to manipulate an [Mcnf.t] for the CEGARBox implementation. *)

From Vct Require CplSolver Lit Assumptions Valuation Tree Mcnf.
From Vct Require Import ImportStd.



Definition first_ctx (mc0 : Mcnf.t) :=
  match mc0 with
  | [] => Lclauses.empty
  | l0::_ => l0
  end.

Definition first_cpls (mc0 : Mcnf.t) :=
  Lclauses.cpls (first_ctx mc0).

Definition first_boxes (mc0 : Mcnf.t) :=
  Lclauses.boxes (first_ctx mc0).

Definition first_dias (mc0 : Mcnf.t) :=
  Lclauses.dias (first_ctx mc0).

Definition fired_boxes (mc0 : Mcnf.t) (V : Valuation.t) :=
  first_boxes mc0
  |> List.filter (fun '(a,b) => Valuation.forces_atm V a)
  |> List.map snd.

Definition next_ctx (mc0 : Mcnf.t) :=
  match mc0 with
  | [] => []
  | _::mc1 => mc1
  end.


Definition with_first_cpls mc0 f :=
  let l0 := first_ctx mc0 in
  let mc1 := next_ctx mc0 in
  Lclauses.make (f (Lclauses.cpls l0)) (Lclauses.boxes l0) (Lclauses.dias l0) :: mc1.
Arguments with_first_cpls mc0 f /.

Definition add_conflict_set mc0 cs :=
  with_first_cpls mc0 (cons (List.map Lit.Neg cs)).
Arguments add_conflict_set mc0 cs /.

(** Adds the conjunction of each literal in [A]. *)
Definition add_assumptions mc0 A :=
  with_first_cpls mc0 (app (Cnf.from_assumptions A)).
Arguments add_assumptions mc0 A /.

(** Adds [~A] to the cpls of [mc0] via adding the disjunction of
    the negation of each literal in [A]. *)
Definition add_neg_assumptions mc0 A :=
  with_first_cpls mc0 (cons (List.map Lit.negate A)).
Arguments add_neg_assumptions mc0 A /.


Lemma add_conflict_set_neg_assumptions : forall mc0 cs,
  add_conflict_set mc0 cs = add_neg_assumptions mc0 (List.map Lit.Pos cs).
Proof. intros mc0 cs. cbn. rewrite List.map_map. cbn. reflexivity. Qed.

Definition cplsolver_mcnf (mc0 : Mcnf.t) :=
  CplSolver.make_with_clauses (first_cpls mc0).

Definition cpl_from_lclauses (l0 : Lclauses.t) :=
  CplSolver.make_with_clauses (Lclauses.cpls l0).

Definition cpl_solve (mc0 : Mcnf.t) (A : Assumptions.t) :=
  CplSolver.solve_with_assumptions (cplsolver_mcnf mc0) A.


(** * Conflict set lemmas *)

(** Creates a conflict set. *)
Definition conflict_set_of mc0 V dia_antecedent core :=
  first_boxes mc0
  |> List.filter (fun box => Valuation.forces_atm V (fst box))
  |> List.filter (fun box => List.existsb (Lit.eqb (snd box)) core)
  |> List.map fst
  |> cons dia_antecedent.
Arguments conflict_set_of mc0 V dia_antecedent core : simpl never.


(** The conflict set is a subset of the valuation. *)
Lemma conflict_set_incl_val : forall mc0 V dia_antecedent core s A,
  CplSolution.Sat V = CplSolver.solve_with_assumptions s A ->
  Valuation.forces_atm V dia_antecedent ->
  let conflict_set := conflict_set_of mc0 V dia_antecedent core in
  List.incl conflict_set V.
Proof.
  intros mc0 V dia_antecedent core s A Hval Hforce_ante conflict_set.
  unfold conflict_set, conflict_set_of. intros x Hx_in_cs.
  cbn in Hx_in_cs. destruct Hx_in_cs as [Hante | Hin].
  - subst x.
    unfold Valuation.forces_atm in Hforce_ante.
    apply List.existsb_exists in Hforce_ante as [l [Hl_in_val Heq_ante]].
    apply Atom.eqb_eq in Heq_ante. subst l. assumption.
  - setoid_rewrite List.in_map_iff in Hin.
    destruct Hin as [pair [Hfst_x Hpair_in]].

    (* remove the two filters *)
    (* first filter doesn't matter, second filter shows that (fst box) is in solver V *)
    apply List.incl_filter in Hpair_in.
    apply List.filter_In in Hpair_in.
    destruct Hpair_in as [_ Hin].

    unfold Valuation.forces_atm in Hin.
    apply List.existsb_exists in Hin as [l [Hl_in_val Heq_ante]].
    apply Atom.eqb_eq in Heq_ante. subst l x. assumption.
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


Lemma incl_force : forall {W} {R} {M : @Kripke.t W R} {w0 : W} mc0 A A',
  List.incl A A' ->
  Mcnf.force M w0 (add_assumptions mc0 A') ->
  Mcnf.force M w0 (add_assumptions mc0 A).
Proof with try easy.
  intros * Hincl Hforce.
  cbn in *. autorewrite with ct in *.
  split... split...
  destruct Hforce as [[Hforce _] _].
  apply Cnf.incl_force with (A' := (Cnf.from_assumptions A'))...
  unfold Cnf.from_assumptions.
  now apply incl_map.
Qed.

Corollary incl_sat : forall mc0 A A',
  List.incl A A' ->
  Mcnf.satisfiable (add_assumptions mc0 A') ->
  Mcnf.satisfiable (add_assumptions mc0 A).
Proof.
  intros mc0 A A' Hincl Hsat.
  unfold Mcnf.satisfiable in *. deex.
  exists W, R, M, w0.
  apply incl_force with A'; easy.
Qed.


Lemma force_assumptions_comm : forall {W} {R} (M : @Kripke.t W R) (w0 : W) mc0 A B,
  Mcnf.force M w0 (add_assumptions (add_assumptions mc0 A) B) <->
  Mcnf.force M w0 (add_assumptions (add_assumptions mc0 B) A).
Proof.
  intros *. cbn. autorewrite with ct. intuition; repeat rewrite List.Forall_app in *; tauto.
Qed.


Lemma force_ctx_first_next : forall {W} {R} (M : @Kripke.t W R) (w0 : W) mc0,
  Mcnf.force M w0 (first_ctx mc0 :: next_ctx mc0) <-> Mcnf.force M w0 mc0.
Proof.
  intros *. destruct mc0 as [|l0 mc1].
  - cbn. now autorewrite with list ct prop.
  - reflexivity.
Qed.

Lemma force_rm_assumptions : forall {W} {R} (M : @Kripke.t W R) (w0 : W) mc0 A,
  Mcnf.force M w0 (add_assumptions mc0 A) ->
  Mcnf.force M w0 mc0.
Proof.
  intros * Hforce. destruct mc0 as [|l0 mc1].
  - apply I.
  - cbn in *. autorewrite with ct in *. tauto.
Qed.


Lemma force_app_and : forall {W} {R} (M : @Kripke.t W R) (w0 : W) mc0 A,
  Mcnf.force M w0 (add_assumptions mc0 A) <->
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
  Mcnf.force M w0 (add_assumptions mc0 []) <-> Mcnf.force M w0 mc0.
Proof. intros *. destruct mc0 as [|l0 mc1]; cbn; autorewrite with ct; intuition. Qed.
Global Hint Resolve force_add_no_assumptions : ct.

Lemma sat_add_no_assumptions : forall mc0,
  Mcnf.satisfiable (add_assumptions mc0 []) <-> Mcnf.satisfiable mc0.
Proof. unfold Mcnf.satisfiable. setoid_rewrite force_add_no_assumptions. tauto. Qed.
Global Hint Resolve sat_add_no_assumptions : ct.
