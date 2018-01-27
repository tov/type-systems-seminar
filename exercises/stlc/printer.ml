open Core
open Syntax

module S = Sexp

let rec type_to_sexp = function
  | IntT ->
      S.Atom "int"
  | ArrT(ts, tr) ->
      S.List (S.Atom "->" :: List.map ~f:type_to_sexp (ts @ [tr]))
  | TupT ts ->
      S.List (S.Atom "*" :: List.map ~f:type_to_sexp ts)

let type_to_string t = S.to_string_hum (type_to_sexp t)
