open Syntax

module S = Sexplib.Sexp

let rec type_to_sexp = function
  | IntT ->
      S.Atom "int"
  | ArrT(ts, tr) ->
      S.List (S.Atom "->" :: List.map type_to_sexp (ts @ [tr]))
  | TupT ts ->
      S.List (S.Atom "*" :: List.map type_to_sexp ts)

let type_to_string t = S.to_string (type_to_sexp t)
