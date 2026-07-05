From CegarTableaux Require Import ImportStd.
From Stdlib Require Import Sorting.
From CegarTableaux Require CplClause BoxClause Lclauses.
From CegarTableaux.Mcnf Require Mcnf.

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
Fixpoint simplify_sur (mc0 : Mcnf.t) (sur : nat) :=
  match mc0 with
  | [] => []
  | (Lclauses.make cpls boxes dias) :: mc1 =>
    let '(boxes_lhs_opt, cpls_mc1, sur1) := simplify_eq_lhs boxes sur in
    let '(boxes_rhs_opt, cpls_box, sur2) := simplify_eq_rhs boxes_lhs_opt sur1 in
    let '(dias_rhs_opt,  cpls_dia, sur3) := simplify_eq_rhs dias sur2 in
    let mc1' := simplify_sur mc1 sur3 in
      Lclauses.make (cpls_box ++ cpls_dia ++ cpls) boxes_rhs_opt dias_rhs_opt
        :: Mcnf.zip_merge [Lclauses.make_cpls cpls_mc1] mc1'
  end.

Definition simplify (mc0 : Mcnf.t) := simplify_sur mc0 (1 + Mcnf.max_atm mc0).
