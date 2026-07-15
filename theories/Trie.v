(** A trie that can only check if a string is a _prefix_
    of a previously added string.

    Inspired by https://github.com/xavierleroy/canonical-binary-tries/blob/main/CharTrie.v.
    We likewise implement the trie assuming that the items in the trie are
    sorted according to the provided order. However, we do not need a [sorted] constraint,
    as the lemmas we need work fine without it ([add] and [contains] follow the same
    'path' for each given string).

    In case the [sorted] constraint is required again in the future, proofs of it
    can be found in the diff of commit 67549035066024664d04c7ec236c8d283bd94046. *)

From CegarTableaux Require Import ImportStd.
From Stdlib.Structures Require Import Orders.


(** The ordered type must also be [Usual] so that its [eq] matches Leibniz equality.

    This could in theory support any equivalence class [eq], but we don't need this
    and would complicate the definition of [is_prefix]. *)
Module Make (K : UsualOrderedTypeFull).
  (** Trying [K' := K] reaches a compiler bug :( *)
  Module K' <: OrderedTypeFull.
    Definition t := K.t.
    Definition eq := K.eq.
    Definition eq_equiv := K.eq_equiv.
    Definition lt := K.lt.
    Definition lt_strorder := K.lt_strorder.
    Definition lt_compat := K.lt_compat.
    Definition compare := K.compare.
    Definition compare_spec := K.compare_spec.
    Definition eq_dec := K.eq_dec.
    Definition le := K.le.
    Definition le_lteq := K.le_lteq.
  End K'.

  Module KFacts.
    Include Structures.OrdersFacts.OrderedTypeFacts K'.

    Lemma compare_eq_iff' : forall x y, K.compare x y = Eq <-> x = y.
    Proof. setoid_rewrite compare_eq_iff. tauto. Qed.
  End KFacts.


  (** Same as a [list (K.t * t)], but easier to do induction on. *)
  Inductive forest :=
    | Nil
    | Cons (key : K.t) (child : forest) (next : forest).


  (** Empty contains nothing, Root contains at least the empty prefix [[]]. *)
  Inductive t :=
    | Empty
    | Root (f : forest).


  (** Conventions: kt = k in the trie, kn = new k (from the input list). *)

  Fixpoint containsf (f : forest) (ks : list K.t) : bool :=
    match ks, f with
    | [], _ => true
    | kn::ks', Nil => false
    | kn::ks', Cons kt child next =>
      match K.compare kn kt with
      | Lt => false
      | Eq => containsf child ks'
      | Gt => containsf next (kn::ks')
      end
    end.


  Definition contains (trie : t) (ks : list K.t) : bool :=
    match trie with
    | Empty => false
    | Root f => containsf f ks
    end.


  Fixpoint singletonf (ks : list K.t) : forest :=
    match ks with
    | [] => Nil
    | kn::ks' => Cons kn (singletonf ks') Nil
    end.


  Fixpoint addf (f : forest) (ks : list K.t) : forest :=
    match f, ks with
    | Nil, _ => singletonf ks
    | Cons _ _ _, [] => f
    | Cons kt child next, kn::ks' =>
      match K.compare kn kt with
      | Lt => Cons kn (singletonf ks') f
      | Eq => Cons kt (addf child ks') next
      | Gt => Cons kt child (addf next (kn::ks'))
      end
    end.


  Definition add (trie : t) (ks : list K.t) : t :=
    match trie with
    | Empty => Root (singletonf ks)
    | Root f => Root (addf f ks)
    end.


  Definition singleton := add Empty.


  Lemma contains_singletonf : forall prefix ks,
    is_prefix prefix ks <-> containsf (singletonf ks) prefix.
  Proof with try easy; auto with datatypes.
    intros prefix ks. revert prefix. induction ks as [|kn ks'].
    - intros prefix. rewrite prefix_of_empty. split.
      + intro Hprefix. now subst prefix.
      + intro Hcontains_prefix.
        cbn in Hcontains_prefix. destruct prefix...
    - intros prefix. split.
      + intros Hprefix. cbn. destruct prefix as [|p0 p1s]...
        apply prefix_cons in Hprefix as [Hp0 Hprefix].
        subst p0.
        rewrite KFacts.compare_refl.
        now apply IHks'.
      + intros Hcontains. cbn in Hcontains.
        destruct prefix as [|p0 p1s] eqn:H...
        destruct (K.compare p0 kn) eqn:Hcmp...
        apply prefix_cons.
        rewrite KFacts.compare_eq_iff' in Hcmp.
        rewrite <- IHks' in Hcontains.
        tauto.
  Qed.


  (** [sortedf f] is not needed as [addf] and [containsf] follow the
      same path. *)
  Lemma contains_addf : forall f prefix ks,
    is_prefix prefix ks ->
    containsf (addf f ks) prefix.
  Proof with try easy; auto with datatypes.
    intros f.
    induction f as [| kt child IHchild next IHnext]; intros prefix ks Hprefix.
    { cbn. now apply contains_singletonf. }

    destruct ks as [|kn ks'].
    { rewrite prefix_of_empty in Hprefix. subst prefix... }

    destruct (K.compare kn kt) eqn:Hcmp.
    - cbn. rewrite Hcmp.
      cbn. destruct prefix as [|p0 p1s]...
      apply prefix_cons in Hprefix as [Heq Hprefix]. subst p0.
      rewrite Hcmp.
      apply IHchild...
    - cbn. rewrite Hcmp.
      cbn. destruct prefix as [|p0 p1s]...
      apply prefix_cons in Hprefix as [Heq Hprefix]. subst p0.
      rewrite KFacts.compare_refl.
      apply contains_singletonf...
    - cbn. rewrite Hcmp.
      cbn. destruct prefix as [|p0 p1s]...
      apply prefix_cons in Hprefix as [Heq Hprefix]. subst p0.
      rewrite Hcmp.
      apply IHnext...
      apply prefix_cons...
  Qed.


  Lemma contains_add : forall trie prefix ks,
    is_prefix prefix ks ->
    contains (add trie ks) prefix.
  Proof with try easy.
    intros * Hprefix.
    destruct trie.
    - cbn. apply contains_singletonf...
    - cbn. apply contains_addf...
  Qed.


  Lemma contains_addf_inv : forall f prefix ks,
    containsf (addf f ks) prefix ->
    containsf f prefix \/ is_prefix prefix ks.
  Proof with try easy; auto with datatypes.
    intros f.
    induction f as [| kt child IHchild next IHnext];
    intros prefix ks Hcontains.
    { cbn in Hcontains. right. now apply contains_singletonf. }

    destruct prefix as [|p0 p1s]...
    destruct ks as [|kn ks'].
    { cbn in *. now left. }

    cbn in *.
    destruct (K.compare kn kt) eqn:Hcmp_kn in Hcontains.
    - cbn in *. destruct (K.compare p0 kt) eqn:Hcmp_p0...
      rewrite KFacts.compare_eq_iff' in *. subst kn p0.
      rewrite prefix_cons. autorewrite with prop.
      apply IHchild...
    - cbn in *. destruct (K.compare p0 kn) eqn:Hcmp_p0...
      rewrite KFacts.compare_eq_iff' in *. subst p0.
      rewrite Hcmp_kn. right.
      apply prefix_cons. split...
      apply contains_singletonf...
    - cbn in *. destruct (K.compare p0 kt) eqn:Hcmp_p0...
  Qed.


  Lemma contains_add_inv : forall trie prefix ks,
    contains (add trie ks) prefix ->
    contains trie prefix \/ is_prefix prefix ks.
  Proof with try easy; auto with datatypes.
    intros * Hcontains.
    destruct trie.
    - cbn in *. right. apply contains_singletonf...
    - cbn in *. apply contains_addf_inv...
  Qed.


  Lemma contains_addf_other : forall f ks1 ks2,
    containsf f ks1 ->
    containsf (addf f ks2) ks1.
  Proof with try easy; auto with datatypes.
    intros f.
    induction f as [| kt child IHchild next IHnext];
    intros ks1 ks2 Hcontains.
    { destruct ks1... cbn. apply contains_singletonf... }

    destruct ks1 as [|kn1 ks1'].
    { apply contains_addf... }
    destruct ks2 as [|kn2 ks2'].
    { exact Hcontains. }

    cbn in *.
    destruct (K.compare kn1 kt) eqn:Hcmp_kn1.
    - destruct (K.compare kn2 kt) eqn:Hcmp_kn2.
      + cbn. rewrite Hcmp_kn1...
      + cbn. rewrite Hcmp_kn1.
        apply KFacts.compare_eq_iff' in Hcmp_kn1. subst kn1.
        rewrite KFacts.compare_antisym in Hcmp_kn2.
        destruct (K.compare kt kn2)...
      + cbn. rewrite Hcmp_kn1...
    - discriminate.
    - destruct (K.compare kn2 kt) eqn:Hcmp_kn2.
      + cbn. rewrite Hcmp_kn1...
      + cbn. rewrite Hcmp_kn1.
        Print KFacts.
        destruct (K.compare kn1 kn2) eqn:Hcmp_kn.
        * rewrite KFacts.compare_eq_iff' in Hcmp_kn. subst kn1.
          congruence.
        * rewrite KFacts.compare_lt_iff in *.
          pose proof (KFacts.lt_trans Hcmp_kn Hcmp_kn2) as Hkn1_kt.
          rewrite <- KFacts.compare_lt_iff in Hkn1_kt.
          congruence.
        * exact Hcontains.
      + cbn. rewrite Hcmp_kn1...
  Qed.


  Lemma contains_add_other : forall trie ks1 ks2,
    contains trie ks1 ->
    contains (add trie ks2) ks1.
  Proof with try easy.
    intros * Hcontains.
    destruct trie.
    - cbn in *...
    - cbn in *. apply contains_addf_other...
  Qed.


  Lemma add_contains_iff : forall trie prefix ks,
    contains (add trie ks) prefix <->
    contains trie prefix \/ is_prefix prefix ks.
  Proof.
    intros *. split.
    - apply contains_add_inv.
    - intros [Hcontains | Hprefix].
      + now apply contains_add_other.
      + now apply contains_add.
  Qed.


  Lemma contains_singleton : forall prefix ks,
    is_prefix prefix ks <-> contains (singleton ks) prefix.
  Proof.
    intros. rewrite contains_singletonf. reflexivity.
  Qed.

  (** Don't simplify these defs, other modules should use the lemmas above. *)
  Global Opaque contains add containsf addf.
End Make.
