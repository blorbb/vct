From CegarTableaux Require Lclauses Mcnf Cnf Nnfl.
From CegarTableaux Require Import ImportStd Utils.
From Stdlib Require Import Sorting.

(** TODO: change MCNF procedures to use this type directly instead of MCNF. *)


(** An alternative equivalent representation of an MCNF formula.

    A linked list of clauses, where the local clauses at the head represent
    clauses that need to be satisfied at the "current" world, and the tail
    is one modal context away. *)
Definition t : Type := list Lclauses.t.


Fixpoint force {W} {R} (M : @Kripke.t W R) (w0 : W) (phi : t) : Prop :=
  match phi with
  | [] => True
  | head :: tail => Lclauses.force M w0 head /\
    forall w1, R w0 w1 -> force M w1 tail
  end.


Definition satisfiable (phi : t) : Prop :=
  exists W R (M : @Kripke.t W R) (w0 : W), force M w0 phi.


Definition unsatisfiable (phi : t) : Prop :=
  ~ satisfiable phi.


Definition atm_in (p : nat) (phi : t) : Prop := List.Exists (Lclauses.atm_in p) phi.


Definition agree {W} {R} (phi : t) (M M' : @Kripke.t W R) : Prop :=
  forall (w0 : W) (p : nat), atm_in p phi -> (Kripke.valuation M w0 p <-> Kripke.valuation M' w0 p).


Definition max_atm (phi : t) : nat :=
  list_max_nat (List.map Lclauses.max_atm phi).


Lemma atm_le_max : forall (phi : t) (p : nat),
  atm_in p phi -> p <= (max_atm phi).
Proof with try easy.
  intros phi p Hatm.
  unfold atm_in in Hatm. rewrite List.Exists_exists in Hatm.
  destruct Hatm as [lclause [Hlclause_in Hp_lclauses]].
  apply Lclauses.atm_le_max in Hp_lclauses.
  apply nat_le_mapped_list_max with (a := lclause)...
Qed.


Section Conversion.
  Fixpoint from_mclause (phi : Mclause.t) : t :=
    match phi with
    | Mclause.Cpl cpl => [Lclauses.make [cpl] [] []]
    | Mclause.Box box => [Lclauses.make [] [box] []]
    | Mclause.Dia dia => [Lclauses.make [] [] [dia]]
    | Mclause.Ctx ctx => Lclauses.empty :: from_mclause ctx
    end.

  (** Merge two [Mchain.t]'s together.

      This will retain all elements, and output a list the length of
      the longer list. *)
  Local Fixpoint zip_merge (a b : t) : t :=
    match a, b with
    | ha::ta, hb::tb => Lclauses.merge ha hb :: zip_merge ta tb
    | a, [] => a
    | [], b => b
    end.


  Fixpoint from_mcnf (phi : Mcnf.t) : t :=
    match phi with
    | [] => []
    | head :: tail => zip_merge (from_mclause head) (from_mcnf tail)
    end.
End Conversion.


(** Logical equivalence of the [from_mcnf] conversion. *)
Section Correctness.
  Lemma equiv_mclause : forall {W} {R} (M : @Kripke.t W R) (w0 : W) (phi : Mclause.t),
    Mclause.force M w0 phi <-> force M w0 (from_mclause phi).
  Proof with auto; try tauto.
    intros W R M w0 phi. revert w0.

    induction phi as
      [ cpl
      | boxes
      | dias
      | mclause IHmclause]; intro w0.

    (* cpl *)
    - cbn. split.
      + intro Hforce_lclause. split...
      + intros [[Hforce_chain _] _].
        rewrite List.Forall_cons_iff in Hforce_chain...

    (* box *)
    - cbn. split.
      + intro Hforce_lclause. split...
      + intros [[_ [Hforce_chain _]] _].
        rewrite List.Forall_cons_iff in Hforce_chain...

    (* dia *)
    - cbn. split.
      + intro Hforce_lclause. split...
      + intros [[_ [_ Hforce_chain]] _].
        rewrite List.Forall_cons_iff in Hforce_chain...

    (* (Mclause.Ctx ctx) case *)
    - split.
      + intro Hforce_mclause.
        cbn. split...
        intros w1 HR_w1.

        apply IHmclause.
        cbn in Hforce_mclause.
        apply Hforce_mclause.
        assumption.

      + intro Hforce_chain.
        cbn.
        intros w1 HR_w1.

        apply IHmclause.
        cbn in Hforce_chain.
        apply proj2 in Hforce_chain.
        apply Hforce_chain.
        assumption.
  Qed.

  Lemma force_zip_and : forall {W} {R} (M : @Kripke.t W R) (w0 : W) (A B : t),
    force M w0 (zip_merge A B) <-> force M w0 A /\ force M w0 B.
  Proof.
    intros W R M w0 A. revert w0.

    (* induction on A, case-by-case on arbitrary B *)
    induction A as [|ha ta IHta]; intros w0 B; destruct B as [| hb tb].
    (* trivial empty cases *)
    - cbn. tauto.
    - cbn. tauto.
    - cbn. tauto.
    (* merge (ha::ta) (hb::tb) <-> (ha::ta) and (hb::tb) *)
    - cbn [zip_merge force].
      rewrite Lclauses.force_merge_and.
      setoid_rewrite IHta.
      intuition (auto with solve_subterm).
  Qed.


  Theorem equiv_mcnf : forall {W} {R} (M : @Kripke.t W R) (w0 : W) (phi : Mcnf.t),
    Mcnf.force M w0 phi <-> force M w0 (from_mcnf phi).
  Proof with auto; try tauto.
    intros W R M w0 phi. revert w0.

    induction phi as [| head tail IHtail].
    - cbn. tauto.
    - intro w0. cbn.
      rewrite force_zip_and, equiv_mclause, IHtail.
      tauto.
  Qed.


  Corollary equisat_mcnf : forall phi,
    Mcnf.satisfiable phi <-> satisfiable (from_mcnf phi).
  Proof.
    intro phi. split.
    - intros [W [M [R [w0 Hforce]]]]. exists W, M, R, w0.
      now apply equiv_mcnf.
    - intros [W [M [R [w0 Hforce]]]]. exists W, M, R, w0.
      now apply equiv_mcnf.
  Qed.
End Correctness.

(** * Simplifications *)
(** TODO: prove its correctness *)

Module ClauseOrd1 <: Orders.TotalLeBool'.
  Definition t := BoxClause.t.
  Definition leb (x y : t) := fst x <=? fst y.
  Lemma leb_total : forall n m, leb n m = true \/ leb m n = true.
  Proof. intros n m. apply nat_leb_total. Qed.
End ClauseOrd1.

Module ClauseOrd2 <: Orders.TotalLeBool'.
  Definition t := BoxClause.t.
  Definition leb (x y : t) := Lit.leb (snd x) (snd y).
  Lemma leb_total : forall n m, leb n m = true \/ leb m n = true.
  Proof. intros n m. apply Lit.leb_total. Qed.
End ClauseOrd2.

Module ClauseSort1 := Mergesort.Sort ClauseOrd1.
Module ClauseSort2 := Mergesort.Sort ClauseOrd2.

(** Groups adjacent elements by the relation. *)
Fixpoint group_by {A} (R : A -> A -> bool) (l: list A) : list (list A) :=
  match l with
  | [] => []
  | x::xs =>
    match group_by R xs with
    | [] => [[x]]
    | ((y::ys) as g) :: gs =>
      if R x y then (x::g) :: gs
      else [x] :: g :: gs
    | [] :: gs => [x] :: gs
    end
  end.


Definition rhs_opt (group : list BoxClause.t) (sur : nat) : (BoxClause.t * list CplClause.t * nat) :=
  match group with
  | [] => ((0,Lit.Pos 0), [], sur) (* [group] should be non-empty so this is an impossible case *)
  | [cl] => (cl, [], sur) (* single clause, don't change *)
  | (_,b)::_ => ((sur, b), List.map (fun '(a, _) => [Lit.Neg a; Lit.Pos sur]) group, S sur)
  end.


Definition lhs_opt (group : list BoxClause.t) (sur : nat) : (BoxClause.t * list CplClause.t * nat) :=
  match group with
  | [] => ((0,Lit.Pos 0), [], sur) (* [group] should be non-empty so this is an impossible case *)
  | [cl] => (cl, [], sur) (* single clause, don't change *)
  | (a,_)::_ => ((a, Lit.Pos sur), List.map (fun '(_, b) => [Lit.Neg sur; b]) group, S sur)
  end.


Definition opt_on_groups
  (opt : list BoxClause.t -> nat -> (BoxClause.t * list CplClause.t * nat))
  (groups : list (list BoxClause.t))
  (sur : nat)
  : (list BoxClause.t * list CplClause.t * nat) :=
  List.fold_left (fun '(new_clauses, cpls, sur) group =>
    let '(new_clause, new_cpls, sur1) := opt group sur in
    (new_clause::new_clauses, new_cpls ++ cpls, sur1))
    groups
    ([], [], sur).

(** Multiple [a* -> []/<>b] can be replaced with [a* -> sur; sur -> []/<>b].

    [BoxClause.t] and [DiaClause.t] are the same type, so this function can be used with both. *)
Definition simplify_eq_rhs (clauses : list BoxClause.t) (sur : nat) : (list BoxClause.t * list CplClause.t * nat) :=
  let sorted := ClauseSort2.sort clauses in
  let grouped := group_by (fun a b => Lit.eqb (snd a) (snd b)) sorted in
  opt_on_groups rhs_opt grouped sur.

Definition simplify_eq_lhs (clauses : list BoxClause.t) (sur : nat) : (list BoxClause.t * list CplClause.t * nat) :=
  let sorted := ClauseSort1.sort clauses in
  let grouped := group_by (fun a b => fst a =? fst b) sorted in
  opt_on_groups lhs_opt grouped sur.

(** Replace [a* -> []/<>b] with [a* -> sur; sur -> []/<>b] and
    [a -> []b*] with [a -> []sur; []( sur -> b* )]. *)
Fixpoint simplify_sur (mc0 : t) (sur : nat) :=
  match mc0 with
  | [] => []
  | (Lclauses.make cpls boxes dias) :: mc1 =>
    let '(boxes_lhs_opt, cpls_mc1, sur1) := simplify_eq_lhs boxes sur in
    let '(boxes_rhs_opt, cpls_box, sur2) := simplify_eq_rhs boxes_lhs_opt sur1 in
    let '(dias_rhs_opt,  cpls_dia, sur3) := simplify_eq_rhs dias sur2 in
    let mc1' := simplify_sur mc1 sur3 in
      Lclauses.make (cpls_box ++ cpls_dia ++ cpls) boxes_rhs_opt dias_rhs_opt
        :: zip_merge [Lclauses.make_cpls cpls_mc1] mc1'
  end.

Definition simplify (mc0 : t) := simplify_sur mc0 (1 + max_atm mc0).
