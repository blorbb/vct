From Stdlib Require List.
From Stdlib Require Import Lia.
From CegarTableaux Require Lit Kripke CplClause BoxClause DiaClause Cnf.
From CegarTableaux Require Import ImportStd.
Import List.ListNotations.
Open Scope list_scope.

(** Set of clauses at the current world. *)
Record t : Type := make {
  cpls  : list CplClause.t;
  boxes : list BoxClause.t;
  dias  : list DiaClause.t;
}.

Definition empty := make [] [] [].

Definition make_cpls cpls := make cpls [] [].


(** Merge two sets of local clauses into one. *)
Definition merge (A B : t) : t :=
  make (cpls A ++ cpls B) (boxes A ++ boxes B) (dias A ++ dias B).


Definition force {W} {R} (M : @Kripke.t W R) (w0 : W) (phi : t) : Prop :=
  Cnf.force M w0 (cpls phi) /\
  List.Forall (BoxClause.force M w0) (boxes phi) /\
  List.Forall (DiaClause.force M w0) (dias phi).

Arguments force {W R} M w0 phi /.


Lemma force_merge_and : forall {W} {R} {M : @Kripke.t W R} {w0 : W} (A B : t),
  force M w0 (merge A B) <-> force M w0 A /\ force M w0 B.
Proof.
  intros W R M w0 A B.
  destruct A as [cpls boxes dias].

  unfold force, merge; cbn.
  repeat rewrite List.Forall_app.
  intuition.
Qed.


Definition atm_in (p : nat) (phi : t) : Prop :=
  List.Exists (CplClause.atm_in p) (cpls phi) \/
  List.Exists (BoxClause.atm_in p) (boxes phi) \/
  List.Exists (DiaClause.atm_in p) (dias phi).

Arguments atm_in p phi /.


Definition agree {W} {R} (phi : t) (M M' : @Kripke.t W R) : Prop :=
  forall (w0 : W) (p : nat), atm_in p phi -> (Kripke.valuation M w0 p <-> Kripke.valuation M' w0 p).


Lemma meaningful_valuations :
  forall {W} {R} (M M' : @Kripke.t W R) (phi : t) (w0 : W),
  agree phi M M' -> (force M w0 phi <-> force M' w0 phi).
Proof with try solve [simpl; auto; tauto].
  intros W R M M' phi w0 Hagree.
  destruct phi as [cpls boxes dias].

  unfold agree in Hagree.
  cbn in Hagree.

  cbn. split.
  - intros [Hc [Hb Hd]].
    repeat split.

    (* cpl *)
    + apply List.Forall_forall.
      intros cpl Hin.
      apply (CplClause.meaningful_valuations M M').
      * unfold CplClause.agree.
        intros w x Hx_in_cpl.
        apply Hagree. left.
        apply List.Exists_exists. exists cpl...
      * rewrite List.Forall_forall in Hc. apply Hc...

      (* box *)
    + apply List.Forall_forall.
      intros box Hin.
      apply (BoxClause.meaningful_valuations M M').
      * unfold BoxClause.agree.
        intros w x Hx_in_box.
        apply Hagree. right. left.
        apply List.Exists_exists. exists box...
      * rewrite List.Forall_forall in Hb. apply Hb...

    (* dia *)
    + apply List.Forall_forall.
      intros dia Hin.
      apply (DiaClause.meaningful_valuations M M').
      * unfold DiaClause.agree.
        intros w x Hx_in_dia.
        apply Hagree. right. right.
        apply List.Exists_exists. exists dia...
      * rewrite List.Forall_forall in Hd. apply Hd...

  - intros [Hc [Hb Hd]].
    repeat split.

    (* cpl *)
    + apply List.Forall_forall.
      intros cpl Hin.
      apply (CplClause.meaningful_valuations M M').
      * unfold CplClause.agree.
        intros w x Hx_in_cpl.
        apply Hagree. left.
        apply List.Exists_exists. exists cpl...
      * rewrite List.Forall_forall in Hc. apply Hc...

      (* box *)
    + apply List.Forall_forall.
      intros box Hin.
      apply (BoxClause.meaningful_valuations M M').
      * unfold BoxClause.agree.
        intros w x Hx_in_box.
        apply Hagree. right. left.
        apply List.Exists_exists. exists box...
      * rewrite List.Forall_forall in Hb. apply Hb...

    (* dia *)
    + apply List.Forall_forall.
      intros dia Hin.
      apply (DiaClause.meaningful_valuations M M').
      * unfold DiaClause.agree.
        intros w x Hx_in_dia.
        apply Hagree. right. right.
        apply List.Exists_exists. exists dia...
      * rewrite List.Forall_forall in Hd. apply Hd...
Qed.


Definition max_atm (phi : t) : nat :=
  Nat.max (Lclauses.cpls phi |> List.map CplClause.max_atm |> list_max_nat)
  (Nat.max
    (Lclauses.boxes phi |> List.map BoxClause.max_atm |> list_max_nat)
    (Lclauses.dias phi |> List.map DiaClause.max_atm |> list_max_nat)).


Lemma atm_le_max : forall (phi : t) (p : nat),
  atm_in p phi -> p <= (max_atm phi).
Proof with try easy.
  intros phi p Hatm. destruct phi as [cpls boxes dias].
  cbn -[list_max_nat] in *. repeat rewrite Nat.max_le_iff.

  destruct Hatm as [Hp_cpls | [Hp_boxes | Hp_dias]].
  - left.
    rewrite List.Exists_exists in Hp_cpls.
    destruct Hp_cpls as [cl [Hcl_cpls Hp_cl]].
    apply nat_le_list_max in Hp_cl.
    apply nat_le_mapped_list_max with (a := cl)...
  - right. left.
    rewrite List.Exists_exists in Hp_boxes.
    destruct Hp_boxes as [box [Hbox_boxes Hp_box]].
    apply BoxClause.atm_le_max in Hp_box.
    apply nat_le_mapped_list_max with (a := box)...
  - right. right.
    rewrite List.Exists_exists in Hp_dias.
    destruct Hp_dias as [dia [Hdia_dias Hp_dia]].
    apply DiaClause.atm_le_max in Hp_dia.
    apply nat_le_mapped_list_max with (a := dia)...
Qed.
