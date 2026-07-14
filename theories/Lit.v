From CegarTableaux Require Kripke Valuation.
From CegarTableaux Require Import ImportStd.

(** A positive or negative literal. *)
Inductive t : Set :=
  | Pos (p : nat)
  | Neg (p : nat).


Definition negate (l : t) : t :=
  match l with
  | Pos n => Neg n
  | Neg n => Pos n
  end.


Definition atm (l : t) : nat :=
  match l with
  | Pos n => n
  | Neg n => n
  end.


Definition get_pos (l : t) : option nat :=
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
  unfold is_true. destruct a, b; cbn.
  - rewrite Nat.eqb_eq. split; congruence.
  - split; discriminate.
  - split; discriminate.
  - rewrite Nat.eqb_eq. split; congruence.
Qed. Global Hint Rewrite eqb_eq : ct.


Global Instance eqb_equiv : Equivalence eqb.
Proof.
  constructor.
  - intros a. now rewrite eqb_eq.
  - intros a b. now repeat rewrite eqb_eq.
  - intros a b c. repeat rewrite eqb_eq. congruence.
Qed.


Lemma eq_dec (a b : t) : {a = b} + {a <> b}.
Proof. decide equality; apply Nat.eq_dec. Qed.


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
Definition leb (x y : t) : bool :=
  match x, y with
  | Pos p, Pos q => p <=? q
  | Neg p, Neg q => p <=? q
  | Pos p, Neg q => true
  | Neg p, Pos q => false
  end.


Lemma leb_total : forall (x y : t), leb x y = true \/ leb y x = true.
Proof.
  intros x y.
  induction x; destruct y; cbn.
  - apply nat_leb_total.
  - tauto.
  - tauto.
  - apply nat_leb_total.
Qed.


Global Instance leb_trans : Transitive leb.
Proof.
  intros x y z Hxy Hyz.
  destruct x; destruct y; destruct z; try easy.
  - cbn in *. unfold is_true in *. rewrite Nat.leb_le in *. transitivity p0; easy.
  - cbn in *. unfold is_true in *. rewrite Nat.leb_le in *. transitivity p0; easy.
Qed.


(** * Forcing *)

Definition force {W} {R} (M : @Kripke.t W R) (w0 : W) (l : t) : Prop :=
  match l with
  | Pos p =>   Kripke.valuation M w0 p
  | Neg p => ~ Kripke.valuation M w0 p
  end.


Definition cpl_forceb (val : Valuation.t) (l : t) : bool :=
  match l with
  | Pos p => List.existsb (Nat.eqb p) val
  | Neg p => negb (List.existsb (Nat.eqb p) val)
  end.


Lemma force_cpl_forceb : forall {W} {R} (M : @Kripke.t W R) w0 V l,
  Kripke.valuation M w0 (Lit.atm l) <-> Valuation.forces_atm V (Lit.atm l) = true ->
  force M w0 l <-> cpl_forceb V l = true.
Proof.
  intros * HV. unfold Valuation.forces_atm in HV. destruct l as [p|p].
  - now cbn in *.
  - cbn in *. rewrite <- Bool.eq_true_not_negb_iff. tauto.
Qed.


Definition atm_in (p : nat) (phi : t) : Prop :=
  p = atm phi.

Arguments atm_in p phi /.


Definition agree {W} {R} (phi : t) (M M' : @Kripke.t W R) : Prop :=
  forall (w0 : W) (p : nat), atm_in p phi -> (Kripke.valuation M w0 p <-> Kripke.valuation M' w0 p).


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
