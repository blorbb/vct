From CegarTableaux Require CplClause.
From CegarTableaux Require Import ImportStd.

(** A classical formula in conjunctive normal form. *)
Definition t := list CplClause.t.


(** Whether a CNF formula is forced at a particular world. *)
Definition force {W} {R} (M : @Kripke.t W R) (w0 : W) (phi : t) : Prop :=
  List.Forall (CplClause.force M w0) phi.

Arguments force {W R} M w0 phi /.


(** Whether a particular _classical_ valuation forces this formula. *)
Definition cpl_forceb (V : Valuation.t) (phi : t) : bool :=
  List.forallb (CplClause.cpl_forceb V) phi.


(* TODO: maybe add a [atm_in p phi] premise? *)
Lemma force_cpl_forceb : forall {W} {R} (M : @Kripke.t W R) w0 V phi,
  (forall p, Kripke.valuation M w0 p <-> Valuation.forces_atm V p = true) ->
  force M w0 phi <-> cpl_forceb V phi = true.
Proof with try easy; auto.
  intros * HV.
  cbn. unfold cpl_forceb. rewrite List.Forall_forall, forallb_forall.
  split.
  - intros Hforce clause Hclause_in.
    setoid_rewrite CplClause.force_cpl_forceb with (V := V) in Hforce...
  - intros Hforceb clause Hclause_in.
    rewrite CplClause.force_cpl_forceb with (V := V)...
Qed.


Definition atm_in (p : nat) (phi : t) : Prop :=
  List.Exists (CplClause.atm_in p) phi.

Arguments atm_in p phi /.


(** Creates a CNF formula from unit assumptions.

    Each literal in the assumptions is put in it's own CPL clause to
    have the same semantics (assumptions is a _conjunction_ of literals). *)
Definition from_assumptions (A : list Lit.t) : t :=
  List.map CplClause.from_lit A.


Definition satisfiable (phi : t) : Prop :=
  exists W R (M : @Kripke.t W R) (w0 : W), force M w0 phi.


Definition unsatisfiable (phi : t) : Prop := ~ satisfiable phi.


Lemma cpl_forceb_sat : forall V phi,
  cpl_forceb V phi = true -> satisfiable phi.
Proof.
  intros V phi Hforceb.
  set (W := unit).
  set (R := fun (_ _ : W) => False).
  set (val := fun (w : W) (p : nat) => Valuation.forces_atm V p = true).
  set (M := Kripke.make W R val).
  exists W, R, M, tt.
  rewrite force_cpl_forceb.
  - exact Hforceb.
  - intros p. subst val. cbn. reflexivity.
Qed.



(** The set of atoms that exist in the formula.

    Duplicates are removed. *)
Definition atms_of (phi : t) : list nat :=
  List.nodup (Nat.eq_dec) (List.flat_map (fun cpl => List.map Lit.atm cpl) phi).


Lemma in_atms_of : forall (phi : t) (p : nat), atm_in p phi <-> List.In p (atms_of phi).
Proof.
  intros phi p.
  destruct phi as [| head tail].
  - cbn. apply List.Exists_nil.
  - cbn. rewrite List.nodup_In, List.Exists_cons, List.in_app_iff, List.Exists_exists.
    split.
    + intro Hxin.
      destruct Hxin as [Hxhead | [clause [Hclause_in_tail Hx_in_clause]]].
      * left. cbn in Hxhead. exact Hxhead.
      * right. apply List.in_flat_map.
        exists clause. cbn in Hx_in_clause. split; assumption.
    + intros [Hxhead | Hxtail].
      * left. cbn. exact Hxhead.
      * right. apply List.in_flat_map in Hxtail.
        destruct Hxtail as [clause [Hclause_in_tail Hx_in_clause]].
        exists clause. cbn. split; assumption.
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



Lemma force_app : forall A B {W} {R} (M : @Kripke.t W R) (w0 : W),
  Cnf.force M w0 (A ++ B) <-> Cnf.force M w0 A /\ Cnf.force M w0 B.
Proof.
  intros. unfold force. apply List.Forall_app.
Qed. Global Hint Resolve force_app : ct.


Lemma force_from_assumptions : forall {W} {R} (M : @Kripke.t W R) (w0 : W) A,
  Cnf.force M w0 (Cnf.from_assumptions A) <-> List.Forall (Lit.force M w0) A.
Proof.
  intros *. cbn. unfold from_assumptions.
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
  intros *. cbn. split.
  - intros Hforce.
    rewrite List.Forall_forall in Hforce.
    apply Hforce.
    now apply In_singleton.
  - rewrite List.Forall_forall.
    intros Hforce clause' Hclause'.
    rewrite In_singleton in Hclause'. subst.
    apply Hforce.
Qed.
