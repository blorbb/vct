(* shadow the Rocq modules *)
open Stdlib

type clause = Lit.t list

(** [Minisat] has functions that accept [list]s, but they just convert
    immediately to an [array], so it's better to work with an array
    earlier. *)
type minisat_clause = Minisat.Lit.t array

module Atom_set = Set.Make (Int)

(** Minisat prefers to make atoms with no set value to true.
    The algorithm works better with fewer atoms set to true though.
    So, we negate every literal to make unset atoms false. *)

let rocq_lit_to_minisat (l : Lit.t) : Minisat.Lit.t =
  match l with
  | Lit.Pos p -> Minisat.Lit.make (p + 1) |> Minisat.Lit.neg
  | Lit.Neg p -> Minisat.Lit.make (p + 1)
;;

let rocq_clause_to_minisat (cl : clause) : minisat_clause =
  Array.of_list cl |> Array.map rocq_lit_to_minisat
;;

let minisat_lit_to_rocq (l : Minisat.Lit.t) : Lit.t =
  (* this atom is 1-indexed, return 0-indexed *)
  let p = Minisat.Lit.abs l |> Minisat.Lit.to_int in
  if Minisat.Lit.sign l then Lit.Neg (p - 1) else Lit.Pos (p - 1)
;;

let minisat_clause_to_rocq (cl : minisat_clause) : clause =
  Array.map minisat_lit_to_rocq cl |> Array.to_list
;;

let rocq_atm_value (minisat : Minisat.t) (p : int) : Lit.t =
  (* check the 1-indexed atom, but return the 0-indexed one *)
  match Minisat.value minisat (Minisat.Lit.make (p + 1)) with
  | Minisat.V_true -> Lit.Neg p
  | Minisat.V_false -> Lit.Pos p
  | Minisat.V_undef -> raise (Failure "unknown atom")
;;

(** A mutable [Minisat] solver that tracks the number of clauses added.

    INVARIANT: [clauses_added] = number of times [add_clause] has been called
    on this object.

    Note: [Minisat.n_clauses] gives the number of clauses _after simplification_,
    so it does not accurately track the number of clauses added. *)
module Mut_solver = struct
  type t =
    { minisat : Minisat.t
    ; mutable clauses_added : int
    }

  let create () : t = { minisat = Minisat.create (); clauses_added = 0 }

  let add_clause (t : t) (clause : clause) =
    (try Minisat.add_clause_a t.minisat (rocq_clause_to_minisat clause) with
     | Minisat.Unsat -> ());
    t.clauses_added <- t.clauses_added + 1
  ;;

  let make_with_clauses clauses =
    let t = create () in
    List.iter (add_clause t) clauses;
    t
  ;;
end

(** A publically immutable Minisat solver with mutable internals for
    incremental solving.

    Only [solver] is mutable; everything else is immutable. Several
    [t]s could share the same [solver]. The first [t1] that adds a clause
    will take advantage of the incrementality of [solver] and mutate it.
    If a different [t2] tries to add a clause after this, we detect that
    [t1] has already mutated [solver] and instead recreate another [solver].

    INVARIANTS:
    1. Every clause in [clauses] is in [solver], and
    2. We can only add clauses, not remove them.

    Therefore, [solver] can be checked to be 'in sync' with [t] by checking
    that the number of clauses in [clauses] equals the number in [solver].
    If they equal, then every clause in [clauses] is in [solver], and the
    two are in sync. Otherwise, some other [t] has added a clause that we
    are not aware of, so we should recreate the [solver] from scratch.

    See the unit test at the bottom of this file for an example.

    We also add an [n_clauses] field as calculating the length of
    [clauses] takes linear time. The checks are quite frequent, so caching
    the length has performance benefits. *)
type t =
  { mutable solver : Mut_solver.t
  ; atoms : Atom_set.t (** Set of atoms that are in the solver, 0-indexed. *)
  ; clauses : clause list (** The clauses that should be inside the solver. *)
  ; n_clauses : int (** Same as [List.length clauses]. *)
  }

(** Ensures that [t.solver] is in sync with [t] by doing nothing (if it
    already is) or recreating the solver. *)
let sync_mut_solver (t : t) : unit =
  match Int.equal t.solver.clauses_added t.n_clauses with
  | true -> ()
  | false -> t.solver <- Mut_solver.make_with_clauses t.clauses
;;

(** Adds the atoms of a clause to the atom set. *)
let add_clause_atms (set : Atom_set.t) (cl : clause) : Atom_set.t =
  let atoms = cl |> List.map Lit.atm |> Atom_set.of_list in
  Atom_set.union set atoms
;;

let make () : t =
  { solver = Mut_solver.create (); atoms = Atom_set.empty; clauses = []; n_clauses = 0 }
;;

let add_clause (t : t) (cl : clause) =
  sync_mut_solver t;
  Mut_solver.add_clause t.solver cl;
  { solver = t.solver
  ; atoms = add_clause_atms t.atoms cl
  ; clauses = cl :: t.clauses
  ; n_clauses = t.n_clauses + 1
  }
;;

let solve_with_assumptions (t : t) (assumptions : Lit.t list) : CplSolution.t =
  sync_mut_solver t;
  try
    Minisat.solve ~assumptions:(assumptions |> rocq_clause_to_minisat) t.solver.minisat;
    (* no exception means sat *)
    let is_pos = function
      | Lit.Pos _ -> true
      | Lit.Neg _ -> false
    in
    CplSolution.Sat
      (add_clause_atms t.atoms assumptions
       |> Atom_set.elements
       (* p here is 0-indexed *)
       |> List.filter (fun p -> rocq_atm_value t.solver.minisat p |> is_pos))
  with
  | Minisat.Unsat ->
    CplSolution.Unsat (Minisat.unsat_core t.solver.minisat |> minisat_clause_to_rocq)
;;

let%test_unit "solver state" =
  let identical_solvers t t' = Repr.phys_equal t.solver t'.solver in
  let t1 = make () in
  (* First time adding clause - same solver used. *)
  let t1_1 = add_clause t1 [ Lit.Pos 1 ] in
  assert (identical_solvers t1 t1_1);
  assert (Int.equal t1_1.n_clauses 1);
  (* Adding a clause to the old t1 recreates the solver. *)
  let t1_2 = add_clause t1 [ Lit.Pos 2 ] in
  assert (not (identical_solvers t1_1 t1_2));
  (* t1 still has an incorrect solver - trying to solve t1 will fix it though. *)
  assert (identical_solvers t1 t1_2);
  assert (solve_with_assumptions t1_2 [] = CplSolution.Sat [ 2 ]);
  assert (identical_solvers t1 t1_2);
  assert (solve_with_assumptions t1 [] = CplSolution.Sat []);
  assert (not (identical_solvers t1 t1_2))
;;
