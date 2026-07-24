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



Definition force {W} {R} (M : @Kripke.t W R) (w0 : W) (phi : t) : Prop :=
  Cnf.force M w0 (cpls phi) /\
  List.Forall (BoxClause.force M w0) (boxes phi) /\
  List.Forall (DiaClause.force M w0) (dias phi).
Arguments force {W} {R} M w0 !phi.


Definition atm_in (p : Atom.t) (phi : t) : Prop :=
  List.Exists (CplClause.atm_in p) (cpls phi) \/
  List.Exists (BoxClause.atm_in p) (boxes phi) \/
  List.Exists (DiaClause.atm_in p) (dias phi).
Arguments atm_in p !phi.


Definition agree {W} {R} (phi : t) (M M' : @Kripke.t W R) : Prop :=
  forall (w0 : W) (p : Atom.t), atm_in p phi -> (Kripke.valuation M w0 p <-> Kripke.valuation M' w0 p).


Lemma meaningful_valuations :
  forall {W} {R} (M M' : @Kripke.t W R) (phi : t) (w0 : W),
  agree phi M M' -> (force M w0 phi <-> force M' w0 phi).
Proof with try easy; auto.
  intros W R M M' phi w0 Hagree.
  destruct phi as [cpls boxes dias].

  unfold agree, atm_in in Hagree.
  setoid_rewrite List.Exists_exists in Hagree.
  unfold force. cbn in *.
  repeat rewrite List.Forall_forall.
  repeat rewrite Cnf.force_forall.

  split.
  - intros [Hc [Hb Hd]].
    repeat split; intros cl Hcl_in.
    + apply (CplClause.meaningful_valuations M M')...
      intros w p Hp_in. apply Hagree. left. exists cl...
    + apply (BoxClause.meaningful_valuations M M')...
      intros w p Hp_in. apply Hagree. right. left. exists cl...
    + apply (DiaClause.meaningful_valuations M M')...
      intros w p Hp_in. apply Hagree. right. right. exists cl...
  - intros [Hc [Hb Hd]].
    repeat split; intros cl Hcl_in.
    + apply (CplClause.meaningful_valuations M M')...
      intros w p Hp_in. apply Hagree. left. exists cl...
    + apply (BoxClause.meaningful_valuations M M')...
      intros w p Hp_in. apply Hagree. right. left. exists cl...
    + apply (DiaClause.meaningful_valuations M M')...
      intros w p Hp_in. apply Hagree. right. right. exists cl...
Qed.


Definition max_atm (phi : t) : Atom.t :=
  Atom.max (Lclauses.cpls phi |> List.map CplClause.max_atm |> Atom.list_max)
  (Atom.max
    (Lclauses.boxes phi |> List.map BoxClause.max_atm |> Atom.list_max)
    (Lclauses.dias phi |> List.map DiaClause.max_atm |> Atom.list_max)).


Lemma atm_le_max : forall (phi : t) (p : Atom.t),
  atm_in p phi -> p <= (max_atm phi).
Proof with try easy.
  intros phi p Hatm. destruct phi as [cpls boxes dias].
  cbn in *. unfold max_atm. repeat rewrite Atom.max_le_iff.

  destruct Hatm as [Hp_cpls | [Hp_boxes | Hp_dias]].
  - left.
    rewrite List.Exists_exists in Hp_cpls.
    destruct Hp_cpls as [cl [Hcl_cpls Hp_cl]].
    apply Atom.le_list_max in Hp_cl.
    apply Atom.le_mapped_list_max with (a := cl)...
  - right. left.
    rewrite List.Exists_exists in Hp_boxes.
    destruct Hp_boxes as [box [Hbox_boxes Hp_box]].
    apply BoxClause.atm_le_max in Hp_box.
    apply Atom.le_mapped_list_max with (a := box)...
  - right. right.
    rewrite List.Exists_exists in Hp_dias.
    destruct Hp_dias as [dia [Hdia_dias Hp_dia]].
    apply DiaClause.atm_le_max in Hp_dia.
    apply Atom.le_mapped_list_max with (a := dia)...
Qed.


(** Merge two sets of local clauses into one. *)
Definition merge (A B : t) : t :=
  make (cpls A ++ cpls B) (boxes A ++ boxes B) (dias A ++ dias B).
Arguments merge : simpl never.

Lemma force_merge_and : forall {W} {R} {M : @Kripke.t W R} {w0 : W} (A B : t),
  force M w0 (merge A B) <-> force M w0 A /\ force M w0 B.
Proof.
  intros W R M w0 A B.
  destruct A as [cpls boxes dias].

  unfold force, merge; cbn.
  autorewrite with list ct.
  tauto.
Qed. Global Hint Rewrite @force_merge_and : ct.


Lemma in_merge_or : forall (A B : t) (p : Atom.t),
  atm_in p (merge A B) <-> atm_in p A \/ atm_in p B.
Proof.
  intros *.
  destruct A as [Acpls Aboxes Adias].
  destruct B as [Bcpls Bboxes Bdias].
  unfold merge, atm_in.
  cbn. autorewrite with list. tauto.
Qed. Global Hint Rewrite in_merge_or : ct.


Lemma force_cpls_app : forall {W} {R} (M : @Kripke.t W R) (w0 : W) app cpls boxes dias,
  force M w0 (make (app++cpls) boxes dias) <-> Cnf.force M w0 app /\ force M w0 (make cpls boxes dias).
Proof.
  intros *. unfold force. cbn. rewrite Cnf.force_app. tauto.
Qed. Global Hint Rewrite @force_cpls_app : ct.

Lemma force_cpls_cons : forall {W} {R} (M : @Kripke.t W R) (w0 : W) cl cpls boxes dias,
  force M w0 (make (cl::cpls) boxes dias) <-> CplClause.force M w0 cl /\ force M w0 (make cpls boxes dias).
Proof.
  intros *.
  change (cl::cpls0) with ([cl]++cpls0).
  rewrite force_cpls_app with (app := [cl]).
  now rewrite Cnf.force_singleton.
Qed. Global Hint Rewrite @force_cpls_cons : ct.

Lemma force_empty : forall {W} {R} (M : @Kripke.t W R) (w0 : W),
  force M w0 empty <-> True.
Proof.
  intros *. cbn. unfold force. cbn. now autorewrite with list ct prop.
Qed.
Global Hint Rewrite @force_empty : ct.

Lemma force_cpls : forall {W} {R} (M : @Kripke.t W R) (w0 : W) cpls,
  force M w0 (make_cpls cpls) <-> Cnf.force M w0 cpls.
Proof.
  unfold force. cbn. now autorewrite with list prop.
Qed. Global Hint Rewrite @force_cpls : ct.


Lemma force_destruct : forall {W} {R} (M : @Kripke.t W R) (w0 : W) cpls boxes dias,
  force M w0 (make cpls boxes dias) <->
  Cnf.force M w0 cpls /\
  List.Forall (BoxClause.force M w0) boxes /\
  List.Forall (DiaClause.force M w0) dias.
Proof. unfold force. reflexivity. Qed.

Lemma force_destruct_forall : forall {W} {R} (M : @Kripke.t W R) (w0 : W) cpls boxes dias,
  force M w0 (make cpls boxes dias) <->
  (forall cl : CplClause.t, In cl cpls -> CplClause.force M w0 cl) /\
  (forall bcl : BoxClause.t, In bcl boxes -> BoxClause.force M w0 bcl) /\
  (forall dcl : DiaClause.t, In dcl dias -> DiaClause.force M w0 dcl).
Proof.
  intros *. rewrite force_destruct.
  rewrite Cnf.force_forall. repeat rewrite List.Forall_forall.
  reflexivity.
Qed.

Lemma atm_in_cpls : forall p cpls,
  atm_in p (make_cpls cpls) <-> List.Exists (CplClause.atm_in p) cpls.
Proof. intros. unfold atm_in. cbn. now autorewrite with list prop. Qed.
Global Hint Rewrite atm_in_cpls : ct.

Lemma atm_in_destruct : forall p cpls boxes dias,
  atm_in p (make cpls boxes dias) <->
  List.Exists (CplClause.atm_in p) cpls \/
  List.Exists (BoxClause.atm_in p) boxes \/
  List.Exists (DiaClause.atm_in p) dias.
Proof. now unfold atm_in. Qed.
Global Hint Rewrite atm_in_destruct : ct.
