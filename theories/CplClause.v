From CegarTableaux Require Lit Valuation.
From CegarTableaux Require Import ImportStd.

(** A CPL-clause, a _disjunction_ of literals. *)
Definition t : Type := list Lit.t.


Definition force {W} {R} (M : @Kripke.t W R) (w0 : W) (phi : t) : Prop :=
  exists l, List.In l phi /\ Lit.force M w0 l.

Arguments force {W R} M w0 phi /.


Definition cpl_forceb (val : Valuation.t) (phi : t) : bool :=
  List.existsb (Lit.cpl_forceb val) phi.


Lemma force_cpl_forceb : forall {W} {R} (M : @Kripke.t W R) w0 V phi,
  (forall p, Kripke.valuation M w0 p <-> Valuation.forces_atm V p) ->
  force M w0 phi <-> cpl_forceb V phi.
Proof with try easy; auto.
  intros * HV. unfold Valuation.forces_atm in HV. split.
  - cbn. intros [l [Hl_in Hforce_l]].
    unfold cpl_forceb.
    =rewrite existsb_exists. exists l. split...
    rewrite Lit.force_cpl_forceb with (V := V) in Hforce_l...
  - cbn. intros Hforceb.
    unfold cpl_forceb in Hforceb. =rewrite existsb_exists in Hforceb.
    destruct Hforceb as [l [Hl_in Hforce_l]].
    exists l. split... rewrite Lit.force_cpl_forceb with (V := V)...
Qed.


Definition atm_in (p : nat) (phi : t) : Prop :=
  List.In p (List.map Lit.atm phi).

Arguments atm_in p phi /.


Definition agree {W} {R} (phi : t) (M M' : @Kripke.t W R) : Prop :=
  forall (w0 : W) (p : nat), atm_in p phi -> (Kripke.valuation M w0 p <-> Kripke.valuation M' w0 p).


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

  simpl. split.
  - intros [l [Hl_in Hforce_l]].
    exists l. split...
    apply Heq_lit...
    simpl. now apply List.in_map.
  - intros [l [Hl_in Hforce_l]].
    exists l. split...
    apply Heq_lit...
    simpl. now apply List.in_map.
Qed.



Definition max_atm (phi : t) : nat :=
  List.map Lit.atm phi |> list_max_nat.


Lemma atm_le_max : forall (phi : t) (p : nat),
  atm_in p phi -> p <= (max_atm phi).
Proof with try easy.
  intros phi p Hatm. now apply nat_le_list_max.
Qed.


(** Creates a CPL clause from a single literal. *)
Definition from_lit (l : Lit.t) : t := [l].

Arguments from_lit l /.


Lemma force_singleton : forall {W} {R} (M : @Kripke.t W R) (w0 : W) (l : Lit.t),
  CplClause.force M w0 (from_lit l) <->
  Lit.force M w0 l.
Proof.
  intros *. split.
  - intros Hforce_clause. cbn in Hforce_clause.
    destruct Hforce_clause as [l' [[Hl_l' | F] Hforce_l']]; subst; easy.
  - intros Hforce_lit. cbn.
    exists l. auto.
Qed.


Global Instance proper_cpl_forceb (clause : t) :
  Proper (Valuation.eq ==> eq) (fun val => cpl_forceb val clause).
Proof.
  intros v1 v2 Heq. unfold cpl_forceb. induction clause as [|l clause IH].
  - reflexivity.
  - cbn. rewrite (Lit.proper_cpl_forceb l v1 v2).
    + now rewrite IH.
    + assumption.
Qed.
