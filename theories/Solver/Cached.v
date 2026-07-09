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
            tableau A s0' mc0' caches1'
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
