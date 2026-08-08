From Vct Require CplClause.
From Vct Require Import ImportStd.

(** A classical formula in conjunctive normal form. *)
Definition t := list CplClause.t.


(** Whether a CNF formula is forced at a particular world. *)
Definition force {W} {R} (M : @Kripke.t W R) (w0 : W) (phi : t) : Prop :=
  List.Forall (CplClause.force M w0) phi.
Arguments force : simpl never.

(** Whether a particular _classical_ valuation forces this formula. *)
Definition cpl_forceb (V : Valuation.t) (phi : t) : bool :=
  List.forallb (CplClause.cpl_forceb V) phi.
Arguments cpl_forceb : simpl never.

Definition atm_in (p : Atom.t) (phi : t) : Prop :=
  List.Exists (CplClause.atm_in p) phi.
Arguments atm_in : simpl never.


Lemma force_forall : forall {W} {R} (M : @Kripke.t W R) (w0 : W) (phi : t),
  force M w0 phi <-> forall clause, List.In clause phi -> CplClause.force M w0 clause.
Proof. unfold force. now setoid_rewrite List.Forall_forall. Qed.

Lemma forceb_forall : forall V phi,
  cpl_forceb V phi <-> forall clause, List.In clause phi -> CplClause.cpl_forceb V clause.
Proof. unfold cpl_forceb. now setoid_rewrite forallb_forall. Qed.

Lemma atm_in_exists : forall p phi,
  atm_in p phi <-> exists clause, List.In clause phi /\ CplClause.atm_in p clause.
Proof. unfold atm_in. now setoid_rewrite List.Exists_exists. Qed.


(* TODO: maybe add a [atm_in p phi] premise? *)
Lemma force_cpl_forceb : forall {W} {R} (M : @Kripke.t W R) w0 V phi,
  (forall p, Kripke.valuation M w0 p <-> Valuation.forces_atm V p) ->
  force M w0 phi <-> cpl_forceb V phi.
Proof with try easy; auto.
  intros * HV.
  rewrite force_forall, forceb_forall.
  setoid_rewrite CplClause.force_cpl_forceb...
Qed.

Lemma atm_in_cons : forall p hd tl,
  atm_in p (hd::tl) <-> CplClause.atm_in p hd \/ atm_in p tl.
Proof. unfold atm_in. now setoid_rewrite List.Exists_cons. Qed.
Global Hint Rewrite atm_in_cons : ct.

(** Creates a CNF formula from unit assumptions.

    Each literal in the assumptions is put in it's own CPL clause to
    have the same semantics (assumptions is a _conjunction_ of literals). *)
Definition from_assumptions (A : list Lit.t) : t :=
  List.map CplClause.from_lit A.


Definition satisfiable (phi : t) : Prop :=
  exists W R (M : @Kripke.t W R) (w0 : W), force M w0 phi.


Definition unsatisfiable (phi : t) : Prop := ~ satisfiable phi.


Lemma cpl_forceb_sat : forall V phi,
  cpl_forceb V phi -> satisfiable phi.
Proof.
  intros V phi Hforceb.
  set (W := unit).
  set (R := fun (_ _ : W) => False).
  set (val := fun (w : W) (p : Atom.t) => Valuation.forces_atm V p).
  set (M := Kripke.make W R val).
  exists W, R, M, tt.
  rewrite force_cpl_forceb.
  - exact Hforceb.
  - intros p. subst val. cbn. reflexivity.
Qed.



(** The set of atoms that exist in the formula.

    Duplicates are removed. *)
Definition atms_of (phi : t) : list Atom.t :=
  List.nodup (Atom.eq_dec) (List.flat_map (fun cpl => List.map Lit.atm cpl) phi).


Lemma in_atms_of : forall (phi : t) (p : Atom.t), atm_in p phi <-> List.In p (atms_of phi).
Proof.
  intros phi p.
  destruct phi as [| head tail].
  - cbn. apply List.Exists_nil.
  - cbn.
    rewrite atm_in_cons, List.nodup_In, List.in_app_iff.
    rewrite CplClause.atm_in_exists, atm_in_exists, List.in_map_iff, List.in_flat_map.
    setoid_rewrite (and_comm (In _ head)).
    setoid_rewrite List.in_map_iff.
    tauto.
Qed. Hint Resolve in_atms_of : ct.


Global Instance proper_cpl_forceb (t : t) :
  Proper (Valuation.eq ==> eq) (fun val => cpl_forceb val t).
Proof.
  intros v1 v2 Heq.
  unfold cpl_forceb.
  induction t as [|cl t IH].
  - reflexivity.
  - cbn. rewrite (CplClause.proper_cpl_forceb cl v1 v2).
    + now rewrite IH.
    + assumption.
Qed.


Lemma incl_force : forall {W} {R} {M : @Kripke.t W R} {w0 : W} A A',
  List.incl A A' -> Cnf.force M w0 A' -> Cnf.force M w0 A.
Proof.
  intros * Hincl Hforce_A'.
  cbn in *. apply List.incl_Forall with (l1 := A'); easy.
Qed.


Lemma incl_unsat : forall A A', List.incl A A' -> Cnf.unsatisfiable A -> Cnf.unsatisfiable A'.
Proof.
  intros A A' Hincl HA_unsat HB_sat.
  apply HA_unsat.
  unfold Cnf.satisfiable in *.
  destruct HB_sat as [W [R [M [w0 Hforce]]]].
  exists W,R,M,w0.
  cbn in Hforce |- *.
  apply incl_force with (A' := A'); easy.
Qed.


Lemma force_nil : forall {W} {R} (M : @Kripke.t W R) (w0 : W),
  force M w0 [] <-> True.
Proof. intros *. unfold force. now rewrite Forall_nil_iff. Qed.
Global Hint Rewrite @force_nil : ct.

Lemma forceb_nil : forall V,
  cpl_forceb V [] <-> True.
Proof. now unfold cpl_forceb, forallb. Qed.
Global Hint Rewrite forceb_nil : ct.

Lemma force_app : forall A B {W} {R} (M : @Kripke.t W R) (w0 : W),
  Cnf.force M w0 (A ++ B) <-> Cnf.force M w0 A /\ Cnf.force M w0 B.
Proof.
  intros. unfold force. apply List.Forall_app.
Qed. Global Hint Rewrite force_app : ct.

Lemma forceb_app : forall V A B,
  Cnf.cpl_forceb V (A ++ B) <-> Cnf.cpl_forceb V A /\ Cnf.cpl_forceb V B.
Proof.
  intros *. unfold cpl_forceb. rewrite forallb_app.
  now =rewrite Bool.andb_true_iff.
Qed. Global Hint Rewrite forceb_app : ct.

Lemma force_map : forall {A} {W} {R} (M : @Kripke.t W R) (w0 : W) (f : A -> CplClause.t) (xs : list A),
  Cnf.force M w0 (List.map f xs) <-> forall x, List.In x xs -> CplClause.force M w0 (f x).
Proof.
  unfold force. setoid_rewrite List.Forall_map.
  now setoid_rewrite List.Forall_forall.
Qed.

Lemma force_from_assumptions : forall {W} {R} (M : @Kripke.t W R) (w0 : W) A,
  Cnf.force M w0 (Cnf.from_assumptions A) <-> List.Forall (Lit.force M w0) A.
Proof.
  intros *. cbn. unfold from_assumptions, force.
  rewrite List.Forall_map.
  repeat rewrite List.Forall_forall.
  setoid_rewrite CplClause.force_singleton.
  reflexivity.
Qed.

Lemma permutation_force : forall A B {W} {R} (M : @Kripke.t W R) (w0 : W),
  Permutation A B -> Cnf.force M w0 A <-> Cnf.force M w0 B.
Proof.
  intros * Hperm. split.
  - cbn. now apply Permutation_Forall.
  - cbn. apply Permutation_Forall. now symmetry.
Qed.

Lemma permutation_sat : forall A B, Permutation A B -> Cnf.satisfiable A <-> Cnf.satisfiable B.
Proof.
  intros * Hperm. unfold satisfiable. setoid_rewrite (permutation_force A B); easy.
Qed.

Corollary permutation_unsat : forall A B, Permutation A B -> Cnf.unsatisfiable A <-> Cnf.unsatisfiable B.
Proof.
  intros * Hperm. unfold unsatisfiable. setoid_rewrite (permutation_sat A B); easy.
Qed.

Definition logically_equivalent A B := forall W R (M : @Kripke.t W R) (w0 : W),
  force M w0 A <-> force M w0 B.


Lemma force_singleton : forall {W} {R} (M : @Kripke.t W R) (w0 : W) clause,
  Cnf.force M w0 [clause] <-> CplClause.force M w0 clause.
Proof.
  intros *. unfold force. now rewrite Forall_singleton.
Qed. Global Hint Rewrite @force_singleton : ct.


Lemma force_local : forall {W} {R1 R2} (M1 : @Kripke.t W R1) (M2 : @Kripke.t W R2) (w0 : W) (phi : t),
  Kripke.valuation M1 = Kripke.valuation M2 ->
  force M1 w0 phi <-> force M2 w0 phi.
Proof.
  intros * HV. cbn. repeat rewrite force_forall.
  setoid_rewrite CplClause.force_local; easy.
Qed.
