From CegarTableaux Require Kripke Valuation.
From CegarTableaux Require Import ImportStd.

(** A positive or negative literal. *)
Inductive t : Set :=
  | Pos (p : Atom.t)
  | Neg (p : Atom.t).


Definition negate (l : t) : t :=
  match l with
  | Pos n => Neg n
  | Neg n => Pos n
  end.


Definition atm (l : t) : Atom.t :=
  match l with
  | Pos n => n
  | Neg n => n
  end.


Definition get_pos (l : t) : option Atom.t :=
  match l with
  | Pos n => Some n
  | Neg n => None
  end.


Definition eqb (a b : t) : bool :=
  match a, b with
  | Pos p, Pos q => p =? q
  | Neg p, Neg q => p =? q
  | _, _ => false
  end.


(** * Equality lemmas *)

Lemma eqb_eq (a b : t) : eqb a b <-> a = b.
Proof.
  destruct a, b; cbn.
  - rewrite Atom.eqb_eq. split; congruence.
  - split; discriminate.
  - split; discriminate.
  - rewrite Atom.eqb_eq. split; congruence.
Qed. Global Hint Rewrite eqb_eq : ct.


Global Instance eqb_equiv : Equivalence eqb.
Proof.
  constructor.
  - intros a. now rewrite eqb_eq.
  - intros a b. now repeat rewrite eqb_eq.
  - intros a b c. repeat rewrite eqb_eq. congruence.
Qed.


(** This also has computational content that needs to be extracted.

    It generates the 'obvious' implementation, matching on the variants
    and checking equality of the [Atom]s. *)
Lemma eq_dec (a b : t) : {a = b} + {a <> b}.
Proof. decide equality; apply Atom.eq_dec. Defined.


Lemma negate_eq_atm (l : t) : atm (negate l) = atm l.
Proof.
  destruct l; reflexivity.
Qed. Global Hint Rewrite negate_eq_atm : ct.


Lemma negate_involution : forall l, Lit.negate (Lit.negate l) = l.
Proof.
  intro l. destruct l as [x|x]; auto.
Qed. Global Hint Rewrite negate_involution : ct.


(** Whether the atom within the literal is the same. *)
Definition eq_atm (a b : t) : Prop :=
  atm a = atm b.

Arguments eq_atm a b /.


Global Instance eq_atm_refl : Reflexive eq_atm.
Proof.
  intro atm. reflexivity.
Qed.

Global Instance eq_atm_sym : Symmetric eq_atm.
Proof.
  intros p q Heq.
  cbn in *. now symmetry.
Qed.

Global Instance eq_atm_trans : Transitive eq_atm.
Proof.
  intros p q r Hpq Hqr.
  cbn in *. now rewrite Hpq.
Qed.

Global Instance eq_atm_equivalence : Equivalence eq_atm := {
  Equivalence_Reflexive := eq_atm_refl;
  Equivalence_Symmetric := eq_atm_sym;
  Equivalence_Transitive := eq_atm_trans;
}.


(** Pos < Neg to match inductive definition order. *)
Definition compare (x y : t) : comparison :=
  match x, y with
  | Pos p, Pos q => Atom.compare p q
  | Neg p, Neg q => Atom.compare p q
  | Pos p, Neg q => Lt
  | Neg p, Pos q => Gt
  end.


Definition lt (x y : t) := compare x y = Lt.
Arguments lt x y /.


Lemma compare_spec : forall (x y : t),
  CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
Proof with try congruence.
  intros [p|p] [q|q]; cbn.
  - destruct (Atom.compare_spec p q); constructor...
    rewrite Atom.compare_lt_iff...
  - now constructor.
  - now constructor.
  - destruct (Atom.compare_spec p q); constructor...
    rewrite Atom.compare_lt_iff...
Qed.

Definition leb (x y : t) : bool :=
  match x, y with
  | Pos p, Pos q => p <=? q
  | Neg p, Neg q => p <=? q
  | Pos p, Neg q => true
  | Neg p, Pos q => false
  end.


Lemma leb_total : forall (x y : t), leb x y \/ leb y x.
Proof.
  intros x y.
  induction x; destruct y; cbn.
  - apply Atom.leb_total.
  - =tauto.
  - =tauto.
  - apply Atom.leb_total.
Qed.


Global Instance leb_trans : Transitive leb.
Proof.
  intros x y z Hxy Hyz.
  destruct x; destruct y; destruct z; try easy.
  - cbn in *. rewrite Atom.leb_le in *. transitivity p0; easy.
  - cbn in *. rewrite Atom.leb_le in *. transitivity p0; easy.
Qed.


(** * Forcing *)

Definition force {W} {R} (M : @Kripke.t W R) (w0 : W) (l : t) : Prop :=
  match l with
  | Pos p =>   Kripke.valuation M w0 p
  | Neg p => ~ Kripke.valuation M w0 p
  end.


Definition cpl_forceb (val : Valuation.t) (l : t) : bool :=
  match l with
  | Pos p => List.existsb (Atom.eqb p) val
  | Neg p => negb (List.existsb (Atom.eqb p) val)
  end.


Lemma force_cpl_forceb : forall {W} {R} (M : @Kripke.t W R) w0 V l,
  Kripke.valuation M w0 (Lit.atm l) <-> Valuation.forces_atm V (Lit.atm l) ->
  force M w0 l <-> cpl_forceb V l.
Proof.
  intros * HV. unfold Valuation.forces_atm in HV. destruct l as [p|p].
  - now cbn in *.
  - cbn in *. =rewrite <- Bool.eq_true_not_negb_iff. tauto.
Qed.


Definition atm_in (p : Atom.t) (phi : t) : Prop :=
  p = atm phi.

Arguments atm_in p phi /.


Definition agree {W} {R} (phi : t) (M M' : @Kripke.t W R) : Prop :=
  forall (w0 : W) (p : Atom.t), atm_in p phi -> (Kripke.valuation M w0 p <-> Kripke.valuation M' w0 p).


Lemma meaningful_valuations :
  forall {W} {R} (M M' : @Kripke.t W R) (phi : t) (w0 : W),
  agree phi M M' -> (force M w0 phi <-> force M' w0 phi).
Proof with simpl; easy.
  intros W R M M' phi w0 Hagree.
  unfold agree in Hagree.

  destruct phi as [p | p].
  - simpl. rewrite Hagree...
  - simpl. rewrite Hagree...
Qed.


Global Instance proper_cpl_forceb (l : t) :
  Proper (Valuation.eq ==> eq) (fun val => cpl_forceb val l).
Proof.
  intros v1 v2 Heq.
  destruct l as [p|p].
  - apply perm_existsb. assumption.
  - unfold cpl_forceb. repeat rewrite negb_exb_forallb.
    apply perm_forallb. assumption.
Qed.


(* Requires classical logic. *)
Lemma not_force_negate : forall {W} {R} (M : @Kripke.t W R) (w0 : W) l,
  ~ Lit.force M w0 l <-> Lit.force M w0 (Lit.negate l).
Proof.
  intros *. split.
  - intros Hnforce. destruct l; auto.
    cbn in *. tauto.
  - intros Hforcen Hforce. destruct l; auto.
Qed.


Module Ordered <: Orders.UsualOrderedTypeFull.
  (** Should give the full definitions instead of using [Orders.TTLB_to_OTF]
      for a more efficient [compare] implementation. *)
  Definition t := Lit.t.

  Definition eq := @eq Lit.t.

  Definition eq_dec := eq_dec.

  Definition eq_equiv := @eq_equivalence Lit.t.

  Definition lt (x y : t) := compare x y = Lt.
  Arguments lt x y /.

  Definition compare := compare.

  Definition compare_spec := compare_spec.

  Lemma lt_strorder : StrictOrder lt.
  Proof with try easy.
    split.
    - intros [p|p] Hlt; cbn in Hlt; now rewrite Atom.compare_refl in Hlt.
    - intros [p|p] [q|q] [r|r]...
      all: cbn; repeat rewrite Atom.compare_lt_iff; apply Atom.lt_trans.
  Qed.

  Lemma lt_compat : Proper (Logic.eq ==> Logic.eq ==> iff) lt.
  Proof. intros x x' Hx y y' Hy. now subst. Qed.

  Definition le (x y : t) := lt x y \/ x = y.

  Lemma le_lteq : forall x y : t, le x y <-> lt x y \/ x = y.
  Proof. reflexivity. Qed.
End Ordered.
