open Core
open Syntax

module S = Sexp

exception Bad_syntax of string * S.t

let stx_err exp got = raise (Bad_syntax(exp, got))

let rec type_of_sexp = function
  | S.Atom "int" -> IntT
  | S.List (S.Atom "->" :: args) as t0 ->
      (match List.rev (List.map ~f:type_of_sexp args) with
       | last :: init -> ArrT(List.rev init, last)
       | [] -> stx_err "return type" t0)
  | S.List (S.Atom "tup" :: args) ->
      TupT(List.map ~f:type_of_sexp args)
  | s -> failwith ("could not parse type: " ^ S.to_string s)

let type_of_string s = type_of_sexp (S.of_string s)

let binding_of_sexp x_of_sexp = function
  | S.List [S.Atom x; e] -> (x, x_of_sexp e)
  | s -> stx_err "binding" s

let bindings_of_sexps x_of_sexp = List.map ~f:(binding_of_sexp x_of_sexp)

let rec expr_of_sexp sexp0 =
  match sexp0 with
  | S.Atom s ->
      (try IntE (Int.of_string s)
       with Failure _ ->
         match s with
         | "let" | "let*" | "-" | "if0"
         | "tup" | "prj" | "lam" | "fix" ->
             stx_err "variable name" (S.Atom s)
         | _ -> VarE s)
  | S.List ss ->
      match ss with
      | [] -> stx_err "expression" sexp0
      | [S.Atom "let"; S.List bindings; body] ->
          LetE(bindings_of_sexps expr_of_sexp bindings, expr_of_sexp body)
      | [S.Atom "let*"; S.List bindings; body] ->
          let bindings' = bindings_of_sexps expr_of_sexp bindings in
          List.fold_right ~f:(fun (x, e) e' -> LetE([(x, e)], e'))
                          ~init:(expr_of_sexp body)
                          bindings'
      | [S.Atom "-"; e1; e2] ->
          SubE(expr_of_sexp e1, expr_of_sexp e2)
      | [S.Atom "if0"; e1; e2; e3] ->
          If0E(expr_of_sexp e1, expr_of_sexp e2, expr_of_sexp e3)
      | (S.Atom "tup" :: es) ->
          TupE(List.map ~f:expr_of_sexp es)
      | [S.Atom "prj"; S.Atom ix; e] ->
          (try PrjE(int_of_string ix, expr_of_sexp e)
           with Failure _ -> stx_err "integer" (S.Atom ix))
      | [S.Atom "lam"; S.List bindings; body] ->
          LamE(bindings_of_sexps type_of_sexp bindings, expr_of_sexp body)
      | [S.Atom "fix"; S.Atom x; t; e] ->
          FixE(x, type_of_sexp t, expr_of_sexp e)
      | e0 :: es ->
          AppE(expr_of_sexp e0, List.map ~f:expr_of_sexp es)

let expr_of_string s = expr_of_sexp (S.of_string s)
