open Lclauses

type t = Lclauses.t list

(** val zip_merge : t -> t -> t **)

let rec zip_merge a b =
  match a with
  | [] -> (match b with
           | [] -> a
           | _ :: _ -> b)
  | ha :: ta ->
    (match b with
     | [] -> a
     | hb :: tb -> (merge ha hb) :: (zip_merge ta tb))
