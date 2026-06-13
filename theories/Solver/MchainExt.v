(** Helpers to manipulate an [Mchain.t] for the CEGARBox implementation. *)

From CegarTableaux Require CplSolver Lit Mchain Assumptions Valuation Tree.
From CegarTableaux Require Import ImportStd Utils ListExt.



Definition first_ctx (mc0 : Mchain.t) :=
  match mc0 with
  | [] => Lclauses.empty
  | l0::_ => l0
  end.

Definition first_cpls (mc0 : Mchain.t) :=
  Lclauses.cpls (first_ctx mc0).

Definition first_boxes (mc0 : Mchain.t) :=
  Lclauses.boxes (first_ctx mc0).

Definition first_dias (mc0 : Mchain.t) :=
  Lclauses.dias (first_ctx mc0).

Definition fired_boxes (mc0 : Mchain.t) (V : Valuation.t) :=
  first_boxes mc0
  |> List.filter (fun '(a,b) => Valuation.forces_atm V a)
  |> List.map snd.

Definition next_ctx (mc0 : Mchain.t) :=
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


Definition cpl_solve (mc0 : Mchain.t) (A : Assumptions.t) :=
  CplSolver.solve_with_assumptions (CplSolver.make_with_clauses (first_cpls mc0)) A.


(** * Conflict set lemmas *)

(** Creates a conflict set. *)
Definition conflict_set_of mc0 V dia_antecedent core :=
  first_boxes mc0
  |> List.filter (fun box => Valuation.forces_atm V (fst box))
  |> List.filter (fun box => List.existsb (Lit.eqb (snd box)) core)
  |> List.map fst
  |> cons dia_antecedent.


(** The conflict set is a subset of the valuation. *)
Lemma conflict_set_incl_val : forall mc0 V dia_antecedent core s A,
  CplSolver.Solution.Sat V = CplSolver.solve_with_assumptions s A ->
  Valuation.forces_atm V dia_antecedent = true ->
  let conflict_set := conflict_set_of mc0 V dia_antecedent core in
  List.incl conflict_set V.
Proof.
  intros mc0 V dia_antecedent core s A Hval Hforce_ante conflict_set.
  unfold conflict_set, conflict_set_of, "|>". intros x Hx_in_cs.
  cbn in Hx_in_cs. destruct Hx_in_cs as [Hante | Hin].
  - subst x.
    unfold Valuation.forces_atm in Hforce_ante.
    apply List.existsb_exists in Hforce_ante as [l [Hl_in_val Heq_ante]].
    apply Nat.eqb_eq in Heq_ante. subst l. assumption.
  - setoid_rewrite List.in_map_iff in Hin.
    destruct Hin as [pair [Hfst_x Hpair_in]].

    (* remove the two filters *)
    (* first filter doesn't matter, second filter shows that (fst box) is in solver V *)
    apply List.incl_filter in Hpair_in.
    apply List.filter_In in Hpair_in.
    destruct Hpair_in as [_ Hin].

    unfold Valuation.forces_atm in Hin.
    apply List.existsb_exists in Hin as [l [Hl_in_val Heq_ante]].
    apply Nat.eqb_eq in Heq_ante. subst l x. assumption.
Qed.


(** Adding a subset of a CPL solver valuation adds no new atoms to the solver state. *)
Lemma val_subset_no_new_atms : forall s A V subset,
  CplSolver.Solution.Sat V = CplSolver.solve_with_assumptions s A ->
  List.incl subset V ->
  CplSolver.clause_atms_incl (List.map Lit.Neg subset) s A.
Proof with auto.
  intros s A V subset Hval Hsubset.
  unfold List.incl in Hsubset.
  cbn. intros x Hx_in_subset.
  apply CplSolver.valuation_in_clauses with (V:=V)...

  cbn in Hx_in_subset.

  rewrite List.map_map in Hx_in_subset. cbn in Hx_in_subset. rewrite List.map_id in Hx_in_subset.
  now apply Hsubset.
Qed.
