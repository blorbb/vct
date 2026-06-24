(* shadow the Rocq modules *)
open Stdlib
module IntSet = Set.Make (Int)

type clause = Lit.t list

module MutSolver = struct
  (* Note: [Minisat.n_clauses] gives the number of clauses _after simplification_,
    so it does not accurately track the number of clauses added. *)
  type t =
    { minisat : Minisat.t
    ; mutable clauses_added : int
    }
end

(* We need to keep track of the clauses to make this type appear immutable.
  The [solver] mutates, so we check if the clauses in the solver have changed,
  and remake a solver if it has.

  Invariant: [clauses] are a subset of the clauses of solver.
  Checking that [clauses] and [solver] are in sync can be done by checking
  the length of the list. *)
type t =
  { solver : MutSolver.t
  ; atoms : IntSet.t (* Set of atoms that are in the solver, 0-indexed. *)
  ; clauses : clause list (* The clauses that should be inside the solver. *)
  }

let union_lits set vals = IntSet.union set (IntSet.of_list (List.map Lit.atm vals))

let rocq_lit_to_minisat l =
  match l with
  | Lit.Pos p -> Minisat.Lit.make (p + 1)
  | Lit.Neg p -> Minisat.Lit.make (p + 1) |> Minisat.Lit.neg
;;

let rocq_clause_to_minisat = List.map rocq_lit_to_minisat

let minisat_lit_to_rocq l =
  (* this atom is 1-indexed, return 0-indexed *)
  let p = Minisat.Lit.abs l |> Minisat.Lit.to_int in
  if Minisat.Lit.sign l then Lit.Pos (p - 1) else Lit.Neg (p - 1)
;;

let minisat_clause_to_rocq = List.map minisat_lit_to_rocq

let rocq_atm_value solver p =
  (* check the 1-indexed atom, but return the 0-indexed one *)
  match Minisat.value solver (Minisat.Lit.make (p + 1)) with
  | Minisat.V_true -> Lit.Pos p
  | Minisat.V_false -> Lit.Neg p
  | Minisat.V_undef -> raise (Failure "unknown atom")
;;

let make () =
  { solver = { minisat = Minisat.create (); clauses_added = 0 }
  ; atoms = IntSet.empty
  ; clauses = []
  }
;;

let add_clause s clause =
  (try Minisat.add_clause_l s.solver.minisat (clause |> rocq_clause_to_minisat) with
   | Minisat.Unsat -> ());
  s.solver.clauses_added <- s.solver.clauses_added + 1;
  { solver = s.solver; atoms = union_lits s.atoms clause; clauses = clause :: s.clauses }
;;

let make_from_clauses clauses = List.fold_left add_clause (make ()) clauses

let check_or_recreate t =
  if Int.equal t.solver.clauses_added (t.clauses |> List.length)
  then t
  else make_from_clauses t.clauses
;;

let solve_with_assumptions s assumptions : Solution.t =
  let s = check_or_recreate s in
  try
    Minisat.solve
      ~assumptions:(assumptions |> rocq_clause_to_minisat |> Array.of_list)
      s.solver.minisat;
    (* no exception means sat *)
    let is_pos = function
      | Lit.Pos _ -> true
      | Lit.Neg _ -> false
    in
    Solution.Sat
      (union_lits s.atoms assumptions
       |> IntSet.elements
       (* p here is 0-indexed *)
       |> List.filter (fun p -> rocq_atm_value s.solver.minisat p |> is_pos))
  with
  | Minisat.Unsat ->
    Solution.Unsat
      (Minisat.unsat_core s.solver.minisat |> Array.to_list |> minisat_clause_to_rocq)
;;
