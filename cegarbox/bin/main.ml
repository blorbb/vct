open Cegarbox
open Stdlib
open Printf

let rec tree_size (Tree.Coq_make (_, children)) =
  1 + (children |> List.map tree_size |> List.fold_left ( + ) 0)
;;

let rec deriv_size = function
  | Derivation.Id _ -> 1
  | Derivation.JumpRestart (_, _, dj, dr) -> 1 + deriv_size dj + deriv_size dr
;;

let check fml =
  let solution = Solver.solve_fml fml in
  match solution with
  | Solver.Solution.Sat t -> printf "SAT: tree size %i\n" (tree_size t)
  | Solver.Solution.Unsat (_, d) -> printf "UNSAT: derivation size %i\n" (deriv_size d)
;;

let check_file filename =
  printf "%s: " filename;
  flush stdout;
  let file_text = In_channel.open_text filename in
  let lexbuf = Lexing.from_channel file_text in
  let fml =
    try Parser.file Lexer.next_token lexbuf with
    | Lexer.SyntaxError s ->
      print_string s;
      exit 1
  in
  check fml
;;

let () = Array.sub Sys.argv 1 ((Sys.argv |> Array.length) - 1) |> Array.iter check_file
