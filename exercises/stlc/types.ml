(*
 * Types
 *)

module S = Sexplib.Sexp

type t = IntT
       | ArrT of t list * t
       | TupT of t list

let rec of_type = function
  | IntT ->
      S.Atom "int"
  | ArrT(ts, tr) ->
      S.List (S.Atom "->" :: List.map of_type (ts @ [tr]))
  | TupT ts ->
      S.List (S.Atom "*" :: List.map of_type ts)

let rec of_sexp = function
  | S.Atom "int" -> IntT
  | S.List (S.Atom "->" :: args) ->
      (match List.rev (List.map of_sexp args) with
       | last :: init -> ArrT(List.rev init, last)
       | _ -> failwith "(->) expects at least a return type")
  | S.List (S.Atom "*" :: args) ->
      TupT(List.map of_sexp args)
  | s -> failwith ("could not parse type: " ^ S.to_string s)
