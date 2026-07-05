(** Extra lemmas regarding lists. *)

From Stdlib Require List.
Import List.ListNotations.
Open Scope list_scope.
From Stdlib Require Import Relations SetoidPermutation Permutation RelationClasses SetoidList PeanoNat Lia Classical.
From CegarTableaux Require Import Tactics.


Lemma In_singleton : forall {A} (x y : A), List.In x [y] <-> x = y.
Proof.
  intros *. cbn. intuition.
Qed. Global Hint Rewrite @In_singleton : list.


Lemma ex_eqA_iff_inA : forall {A} (eqA : relation A) (x : A) (l : list A),
  List.Exists (eqA x) l <-> InA eqA x l.
Proof.
  intros.
  induction l as [| head tail IH].
  - rewrite List.Exists_nil, InA_nil. reflexivity.
  - rewrite List.Exists_cons, InA_cons, IH.
    reflexivity.
Qed.


Lemma InA_flat_map : forall {A B} (eqB : relation B) (f : A -> list B) (l : list A) (y : B),
  InA eqB y (List.flat_map f l) <-> (exists x : A, List.In x l /\ InA eqB y (f x)).
Proof.
  intros.
  rewrite InA_altdef, List.Exists_flat_map, List.Exists_exists.
  setoid_rewrite ex_eqA_iff_inA. reflexivity.
Qed.


Lemma InA_concat : forall {A} (eqA : relation A) (l : list (list A)) (y : A),
  InA eqA y (List.concat l) <-> (exists x, List.In x l /\ InA eqA y x).
Proof.
  intros A eqA l y.
  rewrite InA_altdef, List.Exists_concat, List.Exists_exists.
  setoid_rewrite ex_eqA_iff_inA. reflexivity.
Qed.


Lemma PermutationA_inA : forall {A} (eqA : relation A) (l l' : list A) (x : A),
  Equivalence eqA ->
  PermutationA eqA l l' ->
  InA eqA x l ->
  InA eqA x l'.
Proof with try easy.
  intros A eqA l l' x Hequiv Hperm Hx_in_l.
  apply PermutationA_equivlistA in Hperm...
  unfold equivlistA in Hperm.
  apply Hperm. assumption.
Qed.


Lemma PermutationA_inclA : forall {A} (eqA : relation A) (subset l l' : list A),
  Equivalence eqA ->
  PermutationA eqA l l' ->
  inclA eqA subset l ->
  inclA eqA subset l'.
Proof with try easy.
  intros A eqA subset l l' Hequiv Hperm_ab Hs_incl_a.
  unfold inclA in *.
  intros x Hx_in_subset.
  apply PermutationA_inA with (l:=l)...
  apply Hs_incl_a. assumption.
Qed.


Lemma inclA_cons : forall {A} (eqA : relation A) (h : A) (t l : list A),
  Equivalence eqA ->
  InA eqA h l /\ inclA eqA t l <-> inclA eqA (h :: t) l.
Proof with auto.
  intros A eqA h t l. unfold inclA. split.
  - intros [Hhin Htincl] x Hx_ht.
    apply InA_cons in Hx_ht.
    destruct Hx_ht as [Hxh | Hxt].
    + apply InA_eqA with (x:=h)... now symmetry.
    + now apply Htincl.
  - intros Hincl. split.
    + apply Hincl. now apply InA_cons_hd.
    + intros x Hxt.
      apply Hincl. now apply InA_cons_tl.
Qed.


Lemma inclA_nil : forall {A} (eqA : relation A) (l : list A),
  inclA eqA [] l.
Proof.
  intros A eqA l x Hxin.
  apply InA_nil in Hxin. contradiction.
Qed. Global Hint Resolve inclA_nil : datatypes.


Lemma incl_middle : forall {A} (l1 l2 : list A) (a : A) (s : list A),
  incl (a :: l1 ++ l2) s <-> incl (l1 ++ a :: l2) s.
Proof.
  intros.
  split.
  - intros H x Hx_in.
    apply Permutation_in with (l' := a::l1++l2) in Hx_in; auto.
    symmetry. apply Permutation_middle.
  - intros H x Hx_in.
    apply Permutation_in with (l' := l1++a::l2) in Hx_in; auto.
    apply Permutation_middle.
Qed. Global Hint Resolve incl_middle : datatypes.


Lemma cons_NoDupA : forall {A} (eqA : relation A) a l,
  NoDupA eqA (a :: l) -> NoDupA eqA l.
Proof.
  intros A eqA a l Hnd.
  inversion Hnd. assumption.
Qed. Global Hint Resolve cons_NoDupA : datatypes.


Lemma NoDupA_incl_length : forall {A} (eqA : relation A) l l',
  Equivalence eqA ->
  NoDupA eqA l -> inclA eqA l l' -> List.length l <= List.length l'.
Proof with try easy.
  intros A eqA l l' Hequiv Hnodup. revert l'.
  induction Hnodup as [|a l Hal Hnd IH]; cbn.
  - lia.
  - intros l' Hincl.
    (* a in l' but not in l *)
    apply inclA_cons in Hincl as [Hal' Hincl_ll']...
    apply InA_split in Hal' as [l1 [b [l2 [Hab ->]]]].
    (* remove a and b from the goal *)
    enough (length l <= length (l1 ++ l2)). { rewrite length_app in *. cbn. lia. }
    apply IH.
    intros x Hxin.
    specialize (Hincl_ll' x Hxin).
    apply InA_app in Hincl_ll'. rewrite InA_cons in Hincl_ll'.
    destruct Hincl_ll' as [Hxl1 | [Hxb | Hxl2]].
    + apply InA_app_iff. now left.
    (* contradiction *)
    + apply InA_eqA with (y:=a) in Hxin...
      transitivity b...
    + apply InA_app_iff. now right.
Qed.


(* TODO: can probably prove this without [classic]. *)
Lemma NoDupA_length_incl : forall {A} (eqA : relation A) (l l' : list A),
  Equivalence eqA ->
  NoDupA eqA l ->
  List.length l' <= List.length l ->
  inclA eqA l l' ->
  inclA eqA l' l.
Proof with try easy; auto.
  intros A eqA l l' Hequiv Hnodup Hlen Hincl x Hxin.

  (* destruct (InA_dec eqA_dec x l) as [Hin | Hnin]... *)
  destruct (classic (InA eqA x l)) as [Hin | Hnin]...
  (* contradiction with bound on the length *)
  assert (List.length l < List.length l').
  {
    apply Nat.succ_lt_mono, PeanoNat.le_lt_n_Sm.
    pose proof (NoDupA_incl_length eqA (x::l) (l')) as Hl.
    forward Hl by assumption.
    forward Hl. { apply NoDupA_cons... }
    forward Hl. { apply inclA_cons... }
    now cbn in Hl.
  }
  lia.
Qed.


(** PermutationA counterpart to NoDup_Permutation_bis.
  Has an extra [NoDupA eqA l'] requirement that isn't strictly necessary,
  but proving that the other preconditions imply this is hard. *)
Lemma NoDup_PermutationA_bis : forall {A} (eqA : relation A) (l l' : list A), 
  Equivalence eqA ->
  NoDupA eqA l ->
  NoDupA eqA l' ->
  List.length l' <= List.length l ->
  inclA eqA l l' ->
  PermutationA eqA l l'.
Proof with auto.
  intros A eqA l l' Hequiv Hnodupl Hnodupl' Hlen Hincl.
  apply NoDupA_equivlistA_PermutationA...
  split...
  apply NoDupA_length_incl...
Qed.


Lemma NoDupA_filter : forall {A} (eqA : relation A) (f : A -> bool) (l : list A),
  Proper (eqA ==> eq) f ->
  NoDupA eqA l -> NoDupA eqA (filter f l).
Proof.
  intros A eqA f l Hequiv Hnd. induction Hnd.
  - cbn. apply NoDupA_nil.
  - cbn. destruct (f x).
    + apply NoDupA_cons; auto.
      intro Hx_in_filter. apply H.
      apply filter_InA in Hx_in_filter; tauto.
    + assumption.
Qed. Global Hint Resolve NoDupA_filter : datatypes.


(** If for setoid-equal inputs, f is a setoid-permutation, then flat mapping will also be a permutation. *)
Lemma PermutationA_flat_map : forall {A} (eqA : relation A) (f : A -> list A) (l l' : list A),
  Equivalence eqA ->
  (Proper (eqA ==> PermutationA eqA) f) ->
  PermutationA eqA l l' -> PermutationA eqA (List.flat_map f l) (List.flat_map f l').
Proof with auto.
  intros A eqA f l l' Hequiv Hf Hperm.
  induction Hperm as
    [
    | a a' l l' Haa' Hperm IHperm
    | a b c
    | a b c Hab Hbc IHab IHbc
    ].
  - constructor.
  - cbn. apply PermutationA_app.
    + exact Hequiv.
    + now apply Hf.
    + exact IHperm.
  - cbn. repeat rewrite List.app_assoc.
    apply PermutationA_app_tail... apply PermutationA_app_comm...
  - apply permA_trans with (l₂ := List.flat_map f b)...
Qed.


(* Setoid version of Permutation_map. *)
Lemma PermutationA_map : forall {A} (eqA : relation A) (f : A -> A) (l l' : list A),
  Equivalence eqA ->
  (Proper (eqA ==> eqA) f) ->
  PermutationA eqA l l' -> PermutationA eqA (map f l) (map f l').
Proof with auto.
  intros A eqA f l l' Hequiv Hf Hperm.
  induction Hperm as [|h h' t t' Heq_h Hperm IHperm|h1 h2 t|a b c Hab Hbc IHab IHbc].
  - cbn. reflexivity.
  - cbn. apply permA_skip...
  - cbn. apply permA_swap.
  - eapply permA_trans.
    + exact Hbc.
    + exact IHbc.
Qed.


Lemma PermutationA_swap_heads : forall {A} (eqA : relation A) l x y tl,
  PermutationA eqA l (x :: y :: tl) ->
  PermutationA eqA l (y :: x :: tl).
Proof with auto.
  intros.
  apply permA_trans with (l₂ := x::y::tl).
  - exact H.
  - apply permA_swap.
Qed.


(** Equivalent of [NoDup_concat] for setoid equality. *)
Lemma NoDupA_concat : forall {A} (eqA : relation A) (l : list (list A)),
  Equivalence eqA ->
  List.Forall (NoDupA eqA) l ->
  List.ForallOrdPairs (fun l1 l2 => forall a, InA eqA a l1 -> ~ InA eqA a l2) l ->
  NoDupA eqA (List.concat l).
Proof.
  intros A eqA l Hequiv Hforall Hfop.
  induction l as [|h t IH].
  { constructor. }
  cbn. apply NoDupA_app.
  - exact Hequiv.
  - now apply List.Forall_inv in Hforall.
  - apply IH.
    + now apply List.Forall_inv_tail in Hforall.
    + inversion Hfop. assumption.
  - intros a Ha_in_h Ha_in_t%InA_concat.
    destruct Ha_in_t as [l' [Hl'_in_t Ha_in_l']].
    inversion Hfop. rewrite List.Forall_forall in H1.
    apply (H1 _ Hl'_in_t _ Ha_in_h). assumption.
Qed.


Lemma NoDupA_swap_iff : forall {A} (eqA : relation A) (l l' : list A) (x : A),
  Equivalence eqA ->
  NoDupA eqA (l++x::l') <-> NoDupA eqA (x::l++l').
Proof with auto.
  intros A eqA l l' x Hequiv.
  split.
  - apply NoDupA_swap. assumption.
  - intro Hnd.
    eapply PermutationA_preserves_NoDupA.
    + assumption.
    + apply PermutationA_middle...
    + assumption.
Qed.


Lemma NoDupA_length_2 : forall {A} (eqA : relation A) (x y : A),
  ~ eqA x y ->
  NoDupA eqA [x ; y].
Proof.
  intros A eqA x y Hneq.
  repeat constructor.
  - rewrite InA_singleton. assumption.
  - intro H. apply InA_nil in H. contradiction.
Qed. Global Hint Resolve NoDupA_length_2 : datatypes.


Lemma InA_length_2 : forall {A} (eqA : relation A) (a x y : A),
  InA eqA a [x ; y] -> eqA a x \/ eqA a y.
Proof.
  intros A eqA a x y Hin.
  apply InA_cons in Hin. rewrite InA_singleton in Hin. assumption.
Qed. Global Hint Resolve InA_length_2 : datatypes.


Lemma Permutation_heads_ne : forall {A} (a b : A) (l : list A),
  a <> b ->
  ~ Permutation (a::l) (b::l).
Proof.
  intros A a b l Hne Hperm.
  induction l as [| c l IH].
  - apply Permutation_length_1 in Hperm. contradiction.
  - apply IH.
    apply Permutation_cons_inv with (a := c).
    eapply perm_trans.
    + apply perm_swap.
    + eapply perm_trans.
      * apply Hperm.
      * apply perm_swap.
Qed. Global Hint Resolve Permutation_heads_ne : datatypes.


Lemma Permutation_head_ne : forall {A} (a : A) (l : list A),
  ~ Permutation (a::l) l.
Proof.
  intros A a l Hperm.
  apply Permutation_length in Hperm.
  cbn in Hperm. lia.
Qed. Global Hint Resolve Permutation_head_ne : datatypes.


Lemma Permutation_ne_in : forall {A} (a b : A) (l l' : list A),
  a <> b ->
  Permutation (a :: l) (b :: l') ->
  List.In a l'.
Proof.
  intros A a b l l' Hne Hperm.
  apply Permutation_in with (x:=a) in Hperm.
  - cbn in Hperm. destruct Hperm; auto.
    symmetry in H. contradiction.
  - apply List.in_eq.
Qed. Global Hint Resolve Permutation_ne_in : datatypes.


Lemma PermutationA_length : forall {A} (eqA : relation A) (l l' : list A),
  PermutationA eqA l l' -> length l = length l'.
Proof.
  intros A eqA l l' Hperm.
  induction Hperm; cbn; auto.
  now transitivity (length l₂).
Qed.


Lemma perm_existsb : forall {A} (f : A -> bool) (l1 l2 : list A),
  Permutation l1 l2 -> existsb f l1 = existsb f l2.
Proof.
  intros A f l1 l2 Hperm. induction Hperm.
  - reflexivity.
  - cbn. now rewrite IHHperm.
  - cbn. destruct (f x), (f y); reflexivity.
  - transitivity (existsb f l'); assumption.
Qed.


Lemma perm_forallb : forall {A} (f : A -> bool) (l1 l2 : list A),
  Permutation l1 l2 -> forallb f l1 = forallb f l2.
Proof.
  intros A f l1 l2 Hperm. induction Hperm.
  - reflexivity.
  - cbn. now rewrite IHHperm.
  - cbn. destruct (f x), (f y); reflexivity.
  - transitivity (forallb f l'); assumption.
Qed.


Definition list_max_nat (l : list nat) : nat :=
  List.fold_left Nat.max l 0.

Lemma nat_le_list_max_ind : forall l n acc,
  List.In n l \/ n <= acc ->
  n <= List.fold_left Nat.max l acc.
Proof with try easy.
  intros l. induction l as [|hd tl IH]; intros n acc Hn.
  - destruct Hn...
  - apply IH. destruct Hn as [[Hn_hd | Hn_tl] | Hn_acc].
    + right. subst. apply Nat.le_max_r.
    + left. exact Hn_tl.
    + right. transitivity acc... apply Nat.le_max_l.
Qed.

Corollary nat_le_list_max : forall l n,
  List.In n l -> n <= list_max_nat l.
Proof.
  intros * Hn. apply nat_le_list_max_ind. now left.
Qed.


Lemma nat_le_mapped_list_max :
  forall {A} (n : nat) (max_f : A -> nat) (a : A) (l : list A),
  List.In a l ->
  n <= max_f a ->
  n <= list_max_nat (List.map max_f l).
Proof.
  intros * Ha_in Hn_le_a.
  transitivity (max_f a); try easy.
  apply nat_le_list_max.
  rewrite List.in_map_iff.
  exists a. easy.
Qed.


Lemma Exists_singleton : forall {A} (P : A -> Prop) (x : A),
  List.Exists P [x] <-> P x.
Proof. intros *. rewrite Exists_cons, Exists_nil. tauto. Qed.
Hint Rewrite @Exists_singleton : list.
