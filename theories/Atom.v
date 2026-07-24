From Stdlib Require Import BinNums ZArith ZifyClasses RelationClasses Morphisms Orders Lia.

(** Same as the one in [ImportStd], but we can't import it
    here as we want to export this module in [ImportStd]. *)
Local Coercion is_true : bool >-> Sortclass.

Record t := of_pos {
  to_pos : positive
}.

(** Operations via [positive]. *)

Local Definition pos_unop (f : positive -> positive) (p : t) : t :=
  of_pos (f (to_pos p)).
Arguments pos_unop f p /.

Local Definition pos_binop (f : positive -> positive -> positive) (p : t) (q : t) : t :=
  of_pos (f (to_pos p) (to_pos q)).
Arguments pos_binop f p q /.

Local Definition pos_unrel {A} (f : positive -> A) (p : t) : A :=
  f (to_pos p).
Arguments pos_unrel {A} f p /.

Local Definition pos_binrel {A} (f : positive -> positive -> A) (p : t) (q : t) : A :=
  f (to_pos p) (to_pos q).
Arguments pos_binrel {A} f p q /.


Definition lt := pos_binrel Pos.lt.
Definition ltb := pos_binrel Pos.ltb.
Definition le := pos_binrel Pos.le.
Definition leb := pos_binrel Pos.leb.
Definition eqb := pos_binrel Pos.eqb.
Definition succ := pos_unop Pos.succ.
Definition max := pos_binop Pos.max.
Definition compare := pos_binrel Pos.compare.
Definition to_Z (p : t) := Z.pos (to_pos p).
Definition eq := @Logic.eq t.
Global Instance eq_equiv : Equivalence eq := _.

Definition one := of_pos 1.

(** Notations. *)

Declare Scope atom_scope.
Delimit Scope atom_scope with atom.
Bind Scope atom_scope with t.
Open Scope atom_scope.

Module Notations.
  Infix "<" := lt : atom_scope.
  Infix "<?" := ltb : atom_scope.
  Infix "<=" := le : atom_scope.
  Infix "<=?" := leb : atom_scope.
  Notation "x <= y <= z" := (x <= y /\ y <= z) : atom_scope.
  Notation "x <= y < z" := (x <= y /\ y < z) : atom_scope.
  Notation "x < y < z" := (x < y /\ y < z) : atom_scope.
  Notation "x < y <= z" := (x < y /\ y <= z) : atom_scope.
  Infix "=?" := eqb (at level 70, no associativity) : atom_scope.
End Notations.

Import Notations.


Lemma of_pos_eq_iff : forall px py,
  of_pos px = of_pos py <-> px = py.
Proof. intros px py. split; congruence. Qed.


(** Equality lemmas. *)

Lemma eq_dec : forall (x y : t), {x = y} + {x <> y}.
Proof. decide equality. apply Pos.eq_dec. Defined.


Lemma eqb_eq : forall (x y : t), x =? y <-> x = y.
Proof.
  intros x y. unfold eqb. cbn. unfold is_true.
  rewrite Pos.eqb_eq. split.
  - intros H. destruct x as [px], y as [py]. cbn in *. now subst.
  - intros H. now f_equal.
Qed.


Lemma eqb_neq : forall (x y : t), (x =? y) = false <-> x <> y.
Proof. intros [px] [py]. rewrite of_pos_eq_iff. apply Pos.eqb_neq. Qed.


Global Instance eqb_refl : Reflexive eqb.
Proof. intros x. apply Pos.eqb_refl. Qed.

Global Instance eqb_sym : Symmetric eqb.
Proof. intros x y H. now rewrite eqb_eq in *. Qed.

Global Instance eqb_trans : Transitive eqb.
Proof. intros x y z Hxy Hyz. repeat rewrite eqb_eq in *. now transitivity y. Qed.

Global Instance eqb_equiv : Equivalence eqb.
Proof. split; auto using eqb_refl, eqb_sym, eqb_trans. Qed.


(** Ordering lemmas. *)

Lemma compare_spec : forall (x y : t), CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
Proof.
  intros [px] [py]. unfold compare, lt. cbn.
  destruct (Pos.compare_spec px py); constructor; congruence.
Qed.

Global Instance lt_strorder : StrictOrder lt.
Proof.
  split.
  - intros [px] Hx. inversion Hx. now rewrite Pos.compare_refl in H0.
  - intros [px] [py] [pz]. apply Pos.lt_trans.
Qed.

Lemma lt_compat : Proper (eq ==> eq ==> iff) lt.
Proof.
  intros x x' Hx y y' Hy. rewrite Hx, Hy. reflexivity.
Qed.

Lemma le_lteq : forall (x y : t), le x y <-> lt x y \/ x = y.
Proof.
  intros [px] [py]. unfold le, lt. cbn. now rewrite of_pos_eq_iff, Pos.le_lteq.
Qed.

Module Compare <: Orders.UsualOrderedTypeFull.
  Definition t := t.
  Definition eq := eq.
  Definition eq_equiv := eq_equiv.
  Definition lt := lt.
  Definition lt_strorder := lt_strorder.
  Definition lt_compat := lt_compat.
  Definition compare := compare.
  Definition compare_spec := compare_spec.
  Definition eq_dec := eq_dec.
  Definition le := le.
  Definition le_lteq := le_lteq.
End Compare.

Module CompareFacts := Structures.OrdersFacts.OrderedTypeFacts Compare.
Definition compare_refl := CompareFacts.compare_refl.
Definition compare_eq_iff := CompareFacts.compare_eq_iff.
Definition compare_lt_iff := CompareFacts.compare_lt_iff.
Definition compare_gt_iff := CompareFacts.compare_gt_iff.

Lemma leb_le : forall (x y : t), x <=? y <-> x <= y.
Proof. intros [px] [py]. apply Pos.leb_le. Qed.

Lemma leb_gt : forall (x y : t), (x <=? y) = false <-> y < x.
Proof. intros [px] [py]. apply Pos.leb_gt. Qed.

Lemma ltb_lt : forall (x y : t), x <? y <-> x < y.
Proof. intros [px] [py]. apply Pos.ltb_lt. Qed.

Lemma ltb_ge : forall (x y : t), (x <? y) = false <-> y <= x.
Proof. intros [px] [py]. apply Pos.ltb_ge. Qed.

Global Instance lt_trans : Transitive lt := _.

Global Instance le_refl : Reflexive le.
Proof. intros [px]. apply Pos.le_refl. Qed.

Global Instance le_trans : Transitive le.
Proof. intros [px] [py] [pz]. apply Pos.le_trans. Qed.

Lemma leb_total : forall (x y : t), x <=? y \/ y <=? x.
Proof.
  intros [px] [py]. unfold leb. cbn.
  unfold is_true. repeat rewrite Pos.leb_le. lia.
Qed.


(** [max] lemmas. *)

Lemma le_max_l : forall (x y : t), x <= max x y.
Proof. intros [px] [py]. apply Pos.le_max_l. Qed.

Lemma le_max_r : forall (x y : t), y <= max x y.
Proof. intros [px] [py]. apply Pos.le_max_r. Qed.

Lemma max_le_iff : forall (n m p : t),
  p <= max n m <-> p <= n \/ p <= m.
Proof. intros [pn] [pm] [pp]. apply Pos.max_le_iff. Qed.


(** Lemmas for getting the max atom of a list. *)

Definition list_max (l : list t) : t :=
  List.fold_left max l (of_pos 1).
Arguments list_max : simpl never.

Lemma le_list_max_ind : forall l n acc,
  List.In n l \/ n <= acc ->
  n <= List.fold_left max l acc.
Proof with try easy.
  intros l. induction l as [|hd tl IH]; intros n acc Hn.
  - destruct Hn...
  - apply IH. destruct Hn as [[Hn_hd | Hn_tl] | Hn_acc].
    + right. subst. apply le_max_r.
    + left. exact Hn_tl.
    + right. transitivity acc... apply le_max_l.
Qed.

Corollary le_list_max : forall l n,
  List.In n l -> n <= list_max l.
Proof.
  intros * Hn. apply le_list_max_ind. now left.
Qed.

Lemma le_mapped_list_max :
  forall {A} (n : t) (max_f : A -> t) (a : A) (l : list A),
  List.In a l ->
  n <= max_f a ->
  n <= list_max (List.map max_f l).
Proof.
  intros * Ha_in Hn_le_a.
  transitivity (max_f a); try easy.
  apply le_list_max.
  rewrite List.in_map_iff.
  exists a. easy.
Qed.


(** Zify lets the [lia] tactic still work.

  Implementations are based on the [positive] implementations in [micromega.ZifyInst]. *)

Lemma eq_Z_inj : forall (x y : t), x = y <-> to_Z x = to_Z y.
Proof.
  intros [px] [py]. unfold to_Z. cbn.
  now rewrite of_pos_eq_iff, Pos2Z.inj_iff.
Qed.

Lemma atom_is_pos : forall (p : t), (0 < to_Z p)%Z.
Proof. intro p. unfold to_Z. apply Pos2Z.pos_is_pos. Qed.


Global Instance Inj_atom_Z : InjTyp t Z :=
  { inj := to_Z ; pred x := (0 < x)%Z ; cstr := atom_is_pos }.
Add Zify InjTyp Inj_atom_Z.

Global Instance Op_atom_lt : BinRel lt :=
  { TR := Z.lt; TRInj x y := (iff_refl (to_Z x < to_Z y)%Z) }.
Add Zify BinRel Op_atom_lt.

Global Instance Op_atom_le : BinRel le :=
  { TR := Z.le; TRInj x y := (iff_refl (to_Z x <= to_Z y)%Z) }.
Add Zify BinRel Op_atom_le.

Global Instance Op_eq_atom : BinRel (@Logic.eq t) :=
  { TR := @Logic.eq Z; TRInj := eq_Z_inj }.
Add Zify BinRel Op_eq_atom.

Global Instance Op_Z_atom : UnOp to_Z :=
  { TUOp x := x; TUOpInj _ := eq_refl }.
Add Zify UnOp Op_Z_atom.

Global Program Instance Op_atom_succ : UnOp succ :=
  { TUOp x := (x+1)%Z; TUOpInj := _ }.
Next Obligation. unfold to_Z. cbn. lia. Qed.
Add Zify UnOp Op_atom_succ.

Global Program Instance Op_atom_max : BinOp max :=
  { TBOp := Z.max; TBOpInj := _ }.
Next Obligation. unfold to_Z. cbn. lia. Qed.
Add Zify BinOp Op_atom_max.


(* Do not simplify elsewhere. *)
Arguments lt : simpl never.
Arguments ltb : simpl never.
Arguments le : simpl never.
Arguments leb : simpl never.
Arguments eqb : simpl never.
Arguments succ : simpl never.
Arguments max : simpl never.
Arguments compare : simpl never.
