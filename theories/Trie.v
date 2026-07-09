(** A trie that can only check if a string is a _prefix_
    of a previously added string.

    Inspired by https://github.com/xavierleroy/canonical-binary-tries/blob/main/CharTrie.v. *)

From CegarTableaux Require Import ImportStd.
From Stdlib.Structures Require Import Orders.


Module Make (K : OrderedTypeFull).
  (** Split trie and sorted definitions. *)
  Module Split.
    Scheme All for prod.
    Scheme All for list.

    (** Same as a [list (K.t * t)], but easier to do induction on. *)
    Inductive forest :=
      | Nil
      | Cons (key : K.t) (child : forest) (next : forest).

    (** Empty contains nothing, Root contains at least the empty prefix [[]]. *)
    Inductive t :=
      | Empty
      | Root (f : forest).

    (** Conventions: kt = k in the trie, kn = new k (from the input list). *)

    (** Checks if a character is any key of the current level. *)
    Local Fixpoint in_level kn f :=
      match f with
      | Nil => False
      | Cons kt _ next => K.compare kn kt = Eq \/ in_level kn next
      end.

    (** A condition the forest must satisfy for all operations to be correct.

        The forest must be sorted so that search can short circuit if a greater
        key is found. *)
    Inductive sortedf : forest -> Prop :=
      | sorted_nil : sortedf Nil
      | sorted_cons : forall kn child next,
        sortedf child ->
        sortedf next ->
        (forall kt, in_level kt next -> K.lt kn kt) ->
        sortedf (Cons kn child next).

    Inductive sorted : t -> Prop :=
      | sorted_empty : sorted Empty
      | sorted_root : forall f, sortedf f -> sorted (Root f).

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


    Lemma sorted_singletonf ks : sortedf (singletonf ks).
    Proof.
      induction ks as [|kn ks'].
      - cbn. exact sorted_nil.
      - cbn. apply sorted_cons.
        + exact IHks'.
        + exact sorted_nil.
        + intros kt Hkt_in.
          cbn in Hkt_in. contradiction.
    Qed.

    Lemma in_level_addf : forall f kt kn ks,
      in_level kt (addf f (kn::ks)) ->
      K.compare kt kn = Eq \/ in_level kt f.
    Proof with try easy; auto.
      intros f.
      induction f as [|kt' child IHadd_child next IHadd_next];
        intros kt kn ks Hin_level.
      { cbn in Hin_level. destruct Hin_level... }

      cbn in Hin_level. destruct (K.compare kn kt') eqn:Hcmp; cbn.
      - cbn in Hin_level. destruct Hin_level...
      - cbn in Hin_level. exact Hin_level.
      - cbn in Hin_level. destruct Hin_level...
        apply IHadd_next in H. tauto.
    Qed.


    Lemma sorted_addf : forall f ks, sortedf f -> sortedf (addf f ks).
    Proof with try easy.
      intros f ks Hsortedf. revert ks.
      induction Hsortedf as
        [| k child next Hsorted_child IHsorted_add_child Hsorted_next IHsorted_add_next Hlevel];
        intro ks.
      { cbn. apply sorted_singletonf. }

      cbn. destruct ks as [|kn ks'].
      { apply sorted_cons... }

      destruct matches.
      - apply sorted_cons...
      - apply sorted_cons.
        + apply sorted_singletonf.
        + apply sorted_cons...
        + intros kt Hkt_in_level.
          (* convert compare result to lt *)
          assert (K.lt kn k) as Hlt by now destruct (K.compare_spec kn k). 
          cbn in Hkt_in_level.
          destruct Hkt_in_level as [Hkt_eq_k | Hkt_in_next].
          * assert (K.eq kt k) as Heq by now destruct (K.compare_spec kt k). 
            now rewrite Heq.
          * apply Hlevel in Hkt_in_next.
            transitivity k...
      - apply sorted_cons...
        intros kt Hkt_in_level.
        cbn in IHsorted_add_next.
        apply in_level_addf in Hkt_in_level as [Heq_ktkn | Hkt_in_next].
        + assert (K.eq kt kn) as Heq by now destruct (K.compare_spec kt kn).
          assert (K.lt k kn) as Hlt by now destruct (K.compare_spec kn k).
          now rewrite Heq.
        + now apply Hlevel in Hkt_in_next.
    Qed.


    Lemma sorted_add : forall trie ks, sorted trie -> sorted (add trie ks).
    Proof.
      intros trie ks Hsorted_trie.
      destruct trie.
      - cbn. apply sorted_root.
        apply sorted_singletonf.
      - cbn. apply sorted_root.
        inv_clear Hsorted_trie.
        now apply sorted_addf.
    Qed.


    Lemma contains_prefix : forall trie ks1 ks2,
      sorted trie ->
      contains trie (ks1++ks2) ->
      contains trie ks1.
    Proof. Admitted.

    Lemma add_contains : forall trie ks,
      sorted trie ->
      contains (add trie ks) ks.
    Proof. Admitted.

    (** Adding other words does not remove existing words. *)
    Lemma add_other_contains : forall trie ks ks',
      sorted trie ->
      contains trie ks ->
      contains (add trie ks') ks.
    Admitted.
  End Split.

  (** Merge the trie and sorted defs to be easier to use. *)
  Definition t := { tr : Split.t | Split.sorted tr }.

  Program Definition empty : t := Split.Empty.
  Next Obligation. exact Split.sorted_empty. Qed.

  Definition contains (trie : t) (ks : list K.t) : bool := Split.contains (`trie) ks.

  Program Definition add (trie : t) (ks : list K.t) : t := Split.add (`trie) ks.
  Next Obligation. apply Split.sorted_add. apply proj2_sig. Qed.


  Definition singleton := add empty.

  Lemma contains_prefix : forall trie ks1 ks2,
    contains trie (ks1 ++ ks2) = true -> contains trie ks1 = true.
  Proof.
    intros * Hcontains.
    apply Split.contains_prefix with ks2.
    - apply proj2_sig.
    - exact Hcontains.
  Qed.

  Lemma add_contains : forall trie ks, contains (add trie ks) ks = true.
  Proof.
    intros *. apply Split.add_contains. apply proj2_sig.
  Qed.

  Lemma add_other_contains : forall trie ks ks',
    contains trie ks ->
    contains (add trie ks') ks.
  Proof.
    intros * Hcontains.
    apply Split.add_other_contains.
    - apply proj2_sig.
    - exact Hcontains.
  Qed.

  Lemma contains_empty : forall ks, contains empty ks = false.
  Proof. tauto. Qed.

  Lemma contains_singleton : forall ks, contains (singleton ks) ks.
  Proof. apply add_contains. Qed.

  (** Don't simplify these defs, other modules should use the lemmas above. *)
  Global Opaque contains add.
End Make.
