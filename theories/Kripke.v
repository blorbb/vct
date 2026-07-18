From CegarTableaux Require Import ImportStd.

(** A Kripke model with a parameterised Kripke frame [W, R] and [valuation].

    - [W : Type] is a (possibly infinite) set of worlds.
    - [R : relation W] is the successor relation between worlds.
      For worlds [u] and [v], the mathematical relation notation [uRv] is
      instead a binary function [R u v] that returns whether or not [u] and
      [v] are related.
    - [valuation : W -> nat -> Prop] is the valuation function; given a
      particular world and atom (represented by a natural), returns whether or
      not the atom is true at the particular world.

    We chose to parameterise the frame [W, R] so that we can easily describe
    multiple models with the same frame without requiring additional
    propositions.

    The relation and valuation functions must return a [Prop] instead of a [bool],
    even though we assume classical logic, as the valuation function may not be
    decidable. We want the valuation to be set to whether or not a particular
    formula is forced. [W] could be an infinite set and forcing has [forall] and
    [exists] statements about [W], so forcing is not computable.

    We could change this (and [force]) to a [bool] and possibly get rid of
    classical logic entirely if we add some constraints on [W]. *)
Record t {W : Type} {R : relation W} : Type := {
  valuation : W -> Atom.t -> Prop;
}.

(** [make W R val] constructs a Kripke model. *)
Definition make W R (valuation : W -> Atom.t -> Prop) : @t W R :=
  {| valuation := valuation  |}.
