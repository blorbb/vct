From Vct Require Import ImportStd.
From Vct Require Lit Nnf.

Scheme All for list.
Scheme All for Forall.
Scheme All for Exists.

(** NNF formula but and/or are represented by lists. *)
Inductive t : Set :=
  | Lit (l : Lit.t)
  | And (A : list t)
  | Or  (A : list t)
  | Box (A : t)
  | Dia (A : t).


(** It is easier for this to be an inductive definition as a [Fixpoint]
    does not know that the applications of [force] with
    [List.Forall]/[Exists] are decreasing.

    Should use the [force_*_iff] lemmas below to simplify specific cases. *)
Inductive force {W} {R} (M : @Kripke.t W R) : W -> t -> Prop :=
  | force_lit : forall w0 l,
    Lit.force M w0 l -> force M w0 (Lit l)
  | force_and : forall w0 A,
    List.Forall (force M w0) A -> force M w0 (And A)
  | force_or  : forall w0 A,
    List.Exists (force M w0) A -> force M w0 (Or A)
  | force_box : forall w0 A,
    (forall w1, R w0 w1 -> force M w1 A) -> force M w0 (Box A)
  | force_dia : forall w0 A w1,
    R w0 w1 -> force M w1 A -> force M w0 (Dia A).


Section ForceIff.
  Context {W R} (M : @Kripke.t W R) (w0 : W).

  Local Ltac finish :=
    let H := fresh in
    split; intro H; [now inv_clear H | now constructor].

  Lemma force_lit_iff l : force M w0 (Lit l) <-> Lit.force M w0 l.
  Proof. finish. Qed.
  Lemma force_and_iff A : force M w0 (And A) <-> List.Forall (force M w0) A.
  Proof. finish. Qed.
  Lemma force_or_iff  A : force M w0 (Or A)  <-> List.Exists (force M w0) A.
  Proof. finish. Qed.
  Lemma force_box_iff A : force M w0 (Box A) <-> (forall w1, R w0 w1 -> force M w1 A).
  Proof. finish. Qed.
  Lemma force_dia_iff A : force M w0 (Dia A) <-> (exists w1, R w0 w1 /\ force M w1 A).
  Proof.
    split; intro H.
    - inv_clear H. now exists w2.
    - deex. apply force_dia with (w1 := w1); easy.
  Qed.
End ForceIff.


Definition satisfiable (phi : t) : Prop :=
  exists W R (M : @Kripke.t W R) (w0 : W), force M w0 phi.


Definition unsatisfiable (phi : t) : Prop :=
  forall W R (M : @Kripke.t W R) (w0 : W), ~ force M w0 phi.


(** Converts several conj/disjuncts into a list.

    A lot of repeats of specific cases are needed for termination
    to be automatically proven. *)
Fixpoint from_nnf (f : Nnf.t) : Nnfl.t :=
  match f with
  | Nnf.Lit l => Nnfl.Lit l
  | Nnf.Box p => Nnfl.Box (from_nnf p)
  | Nnf.Dia p => Nnfl.Dia (from_nnf p)
  | Nnf.And a b => Nnfl.And (gather_and a (gather_and b []))
  | Nnf.Or a b  => Nnfl.Or (gather_or a (gather_or b []))
  end
with gather_and (f : Nnf.t) (acc : list Nnfl.t) : list Nnfl.t :=
  match f with
  | Nnf.And a b => gather_and a (gather_and b acc)
  | Nnf.Lit l   => Nnfl.Lit l :: acc
  | Nnf.Box p   => Nnfl.Box (from_nnf p) :: acc
  | Nnf.Dia p   => Nnfl.Dia (from_nnf p) :: acc
  | Nnf.Or a b  => Nnfl.Or (gather_or a (gather_or b [])) :: acc
  end
with gather_or (f : Nnf.t) (acc : list Nnfl.t) : list Nnfl.t :=
  match f with
  | Nnf.Or a b  => gather_or a (gather_or b acc)
  | Nnf.Lit l   => Nnfl.Lit l :: acc
  | Nnf.Box p   => Nnfl.Box (from_nnf p) :: acc
  | Nnf.Dia p   => Nnfl.Dia (from_nnf p) :: acc
  | Nnf.And a b => Nnfl.And (gather_and a (gather_and b [])) :: acc
  end.


Lemma forall_and_distrib {A} (P Q : A -> Prop) :
  (forall a, P a /\ Q a) <-> (forall a, P a) /\ (forall a, Q a).
Proof. repeat split; apply H. Qed.

Lemma equiv_nnf_ind : forall {W} {R} (M : @Kripke.t W R) (w0 : W) (phi : Nnf.t),
  (Nnf.force M w0 phi <-> force M w0 (from_nnf phi)) /\
  (forall acc, List.Forall (force M w0) (gather_and phi acc) <-> Nnf.force M w0 phi /\ List.Forall (force M w0) acc) /\
  (forall acc, List.Exists (force M w0) (gather_or phi acc) <-> Nnf.force M w0 phi \/ List.Exists (force M w0) acc).
Proof with try solve [intuition].
  intros W R M w0 phi. revert w0.
  induction phi as
    [ p
    | A IHA B IHB
    | A IHA B IHB
    | A IHA
    | A IHA
    ]; intro w0.
  - cbn. split; [|split].
    + now rewrite force_lit_iff.
    + intro acc. now rewrite List.Forall_cons_iff, force_lit_iff.
    + intro acc. now rewrite List.Exists_cons, force_lit_iff.
  - destruct (IHA w0) as [IHA_from [IHA_and IHA_or]].
    destruct (IHB w0) as [IHB_from [IHB_and IHB_or]].
    cbn. split; [|split].
    + rewrite force_and_iff, IHA_and, IHB_and. intuition.
    + intros acc. rewrite IHA_and, IHB_and. intuition.
    + intros acc. rewrite List.Exists_cons, force_and_iff.
      rewrite IHA_and, IHB_and. intuition.
  - destruct (IHA w0) as [IHA_from [IHA_and IHA_or]].
    destruct (IHB w0) as [IHB_from [IHB_and IHB_or]].
    cbn. split; [|split].
    + rewrite force_or_iff, IHA_or, IHB_or, Exists_nil. intuition.
    + intros acc. rewrite List.Forall_cons_iff, force_or_iff, IHA_or, IHB_or, List.Exists_nil. intuition.
    + intros acc. rewrite IHA_or, IHB_or. intuition.
  - apply forall_and_distrib in IHA as [IHA_from _].
    cbn. split; [|split].
    + rewrite force_box_iff. now setoid_rewrite IHA_from.
    + intros acc. rewrite List.Forall_cons_iff, force_box_iff.
      now setoid_rewrite IHA_from.
    + intros acc. rewrite List.Exists_cons, force_box_iff.
      now setoid_rewrite IHA_from.
  - apply forall_and_distrib in IHA as [IHA_from _].
    cbn. split; [|split].
    + rewrite force_dia_iff. now setoid_rewrite IHA_from.
    + intros acc. rewrite List.Forall_cons_iff, force_dia_iff.
      now setoid_rewrite IHA_from.
    + intros acc. rewrite List.Exists_cons, force_dia_iff.
      now setoid_rewrite IHA_from.
Qed.


Theorem equiv_nnf :
  forall {W} {R} (M : @Kripke.t W R) (w0 : W) (phi : Nnf.t),
  Nnf.force M w0 phi <-> force M w0 (from_nnf phi).
Proof.
  intros *. apply equiv_nnf_ind.
Qed.


Corollary equisat_nnf :
  forall (phi : Nnf.t), Nnf.satisfiable phi <-> Nnfl.satisfiable (from_nnf phi).
Proof.
  intro phi. split.
  - intros [W [M [R [w0 Hforce]]]]. exists W, M, R, w0. 
    now apply equiv_nnf.
  - intros [W [M [R [w0 Hforce]]]]. exists W, M, R, w0. 
    now apply equiv_nnf.
Qed.
