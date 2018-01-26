open Syntax

module S = Sexplib.Sexp

let rec type_of_sexp = function
  | S.Atom "int" -> IntT
  | S.List (S.Atom "->" :: args) ->
      (match List.rev (List.map type_of_sexp args) with
       | last :: init -> ArrT(List.rev init, last)
       | _ -> failwith "(->) expects at least a return type")
  | S.List (S.Atom "*" :: args) ->
      TupT(List.map type_of_sexp args)
  | s -> failwith ("could not parse type: " ^ S.to_string s)

let type_of_string s = type_of_sexp (S.of_string s)
