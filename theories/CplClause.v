From CegarTableaux Require Lit Valuation.
From CegarTableaux Require Import ImportStd.

(** A CPL-clause, a _disjunction_ of literals. *)
Definition t : Type := list Lit.t.


Definition force {W} {R} (M : @Kripke.t W R) (w0 : W) (phi : t) : Prop :=
  List.Exists (Lit.force M w0) phi.
Arguments force : simpl never.

Definition cpl_forceb (val : Valuation.t) (phi : t) : bool :=
  List.existsb (Lit.cpl_forceb val) phi.
Arguments cpl_forceb : simpl never.

Definition atm_in (p : Atom.t) (phi : t) : Prop :=
  List.In p (List.map Lit.atm phi).
Arguments atm_in : simpl never.


Lemma force_exists : forall {W} {R} (M : @Kripke.t W R) (w0 : W) (phi : t),
  force M w0 phi <-> exists l, List.In l phi /\ Lit.force M w0 l.
Proof. intros *. unfold force. now rewrite List.Exists_exists. Qed.

Lemma force_nil : forall {W} {R} (M : @Kripke.t W R) (w0 : W),
  force M w0 [] <-> False.
Proof. unfold force. now setoid_rewrite List.Exists_nil. Qed.
Global Hint Rewrite @force_nil : ct.

Lemma force_cons : forall {W} {R} (M : @Kripke.t W R) (w0 : W) l tl,
  force M w0 (l::tl) <-> Lit.force M w0 l \/ force M w0 tl.
Proof. intros *. unfold force. now rewrite List.Exists_cons. Qed.
Global Hint Rewrite @force_cons : ct.

Lemma forceb_exists : forall V phi,
  cpl_forceb V phi <-> exists l, List.In l phi /\ Lit.cpl_forceb V l.
Proof. unfold cpl_forceb. now setoid_rewrite existsb_exists. Qed.

Lemma atm_in_exists : forall p phi,
  atm_in p phi <-> exists l, List.In l phi /\ Lit.atm_in p l.
Proof. unfold atm_in. setoid_rewrite List.in_map_iff. now setoid_rewrite (and_comm (In _ _)). Qed.

Lemma atm_in_nil : forall p, atm_in p [] <-> False.
Proof. intros. now unfold atm_in. Qed.
Global Hint Rewrite atm_in_nil : ct.

Lemma atm_in_cons : forall p l tl, atm_in p (l::tl) <-> Lit.atm_in p l \/ atm_in p tl.
Proof. intros. now unfold atm_in. Qed.
Global Hint Rewrite atm_in_cons : ct.



Lemma force_cpl_forceb : forall {W} {R} (M : @Kripke.t W R) w0 V phi,
  (forall p, Kripke.valuation M w0 p <-> Valuation.forces_atm V p) ->
  force M w0 phi <-> cpl_forceb V phi.
Proof with try easy; auto.
  intros * HV. unfold Valuation.forces_atm in HV. split.
  - rewrite force_exists.
    intros [l [Hl_in Hforce_l]].
    rewrite forceb_exists.
    exists l. split...
    rewrite Lit.force_cpl_forceb with (V := V) in Hforce_l...
  - cbn. intros Hforceb.
    rewrite forceb_exists in Hforceb.
    destruct Hforceb as [l [Hl_in Hforce_l]].
    rewrite force_exists.
    exists l. split... rewrite Lit.force_cpl_forceb with (V := V)...
Qed.




Definition agree {W} {R} (phi : t) (M M' : @Kripke.t W R) : Prop :=
  forall (w0 : W) (p : Atom.t), atm_in p phi -> (Kripke.valuation M w0 p <-> Kripke.valuation M' w0 p).


Lemma meaningful_valuations :
  forall {W} {R} (M M' : @Kripke.t W R) (phi : t) (w0 : W),
  agree phi M M' -> (force M w0 phi <-> force M' w0 phi).
Proof with simpl; auto.
  intros W R M M' phi w0 Hagree. revert w0.

  assert (
    forall w0 l, atm_in (Lit.atm l) phi ->
    Lit.force M w0 l <-> Lit.force M' w0 l
  ) as Heq_lit.
  {
    intros w0' l Hlin.
    unfold agree in Hagree.
    destruct l as [p | p]; simpl; rewrite Hagree; tauto.
  }

  unfold force. setoid_rewrite List.Exists_exists.
  split.
  - intros [l [Hl_in Hforce_l]].
    exists l. split...
    apply Heq_lit...
    simpl. now apply List.in_map.
  - intros [l [Hl_in Hforce_l]].
    exists l. split...
    apply Heq_lit...
    simpl. now apply List.in_map.
Qed.



Definition max_atm (phi : t) : Atom.t :=
  List.map Lit.atm phi |> Atom.list_max.


Lemma atm_le_max : forall (phi : t) (p : Atom.t),
  atm_in p phi -> p <= (max_atm phi).
Proof with try easy.
  intros phi p Hatm. now apply Atom.le_list_max.
Qed.


(** Creates a CPL clause from a single literal. *)
Definition from_lit (l : Lit.t) : t := [l].

Arguments from_lit l /.


Lemma force_singleton : forall {W} {R} (M : @Kripke.t W R) (w0 : W) (l : Lit.t),
  CplClause.force M w0 (from_lit l) <->
  Lit.force M w0 l.
Proof.
  intros *. unfold force, from_lit.
  rewrite Exists_singleton. reflexivity.
Qed.
Hint Rewrite @force_singleton : ct.


Global Instance proper_cpl_forceb (clause : t) :
  Proper (Valuation.eq ==> eq) (fun val => cpl_forceb val clause).
Proof.
  intros v1 v2 Heq. unfold cpl_forceb. induction clause as [|l clause IH].
  - reflexivity.
  - cbn. rewrite (Lit.proper_cpl_forceb l v1 v2).
    + now rewrite IH.
    + assumption.
Qed.

Lemma force_local : forall {W} {R1 R2} (M1 : @Kripke.t W R1) (M2 : @Kripke.t W R2) (w0 : W) (phi : t),
  Kripke.valuation M1 = Kripke.valuation M2 ->
  force M1 w0 phi <-> force M2 w0 phi.
Proof.
  intros * HV. unfold force. setoid_rewrite List.Exists_exists.
  setoid_rewrite Lit.force_local; easy.
Qed.
