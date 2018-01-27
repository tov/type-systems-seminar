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

let rec unfold_let_star bindings body =
  match bindings with
  | binding :: rest ->
      S.List [S.Atom "let"; S.List [binding]; unfold_let_star rest body]
  | [] ->
      body

let expr_of_sexp sexp0 =
  let rec loop env = function
    | S.Atom s ->
        (try IntE (Int.of_string s)
         with Failure _ ->
           match s with
           | "let" | "let*" | "-" | "if0"
           | "tup" | "prj" | "lam" | "fix" ->
               stx_err "variable name" (S.Atom s)
           | _ -> VarE (Env.lookup_exn env s))
    | S.List ss ->
        match ss with
        | [] -> stx_err "expression" (S.List [])
        | [S.Atom "let"; S.List bindings; body] ->
            let xes = bindings_of_sexps (loop env) bindings in
            let xs  = List.map ~f:fst xes in
            let es  = List.map ~f:snd xes in
            LetE(es,
                 fun vs ->
                   let env' = List.fold2_exn ~f:Env.extend ~init:env xs vs in
                   loop env' body)
        | [S.Atom "let*"; S.List bindings; body] ->
            loop env (unfold_let_star bindings body)
        | [S.Atom "-"; e1; e2] ->
            SubE(loop env e1, loop env e2)
        | [S.Atom "if0"; e1; e2; e3] ->
            If0E(loop env e1, loop env e2, loop env e3)
        | (S.Atom "tup" :: es) ->
            TupE(List.map ~f:(loop env) es)
        | [S.Atom "prj"; S.Atom ix; e] ->
            (try PrjE(int_of_string ix, loop env e)
             with Failure _ -> stx_err "integer" (S.Atom ix))
        | [S.Atom "lam"; S.List bindings; body] ->
            let xts = bindings_of_sexps type_of_sexp bindings in
            let xs  = List.map ~f:fst xts in
            let ts  = List.map ~f:snd xts in
            LamE(ts,
                 fun vs ->
                   let env' = List.fold2_exn ~f:Env.extend ~init:env xs vs in
                   loop env' body)
        | [S.Atom "fix"; S.Atom x; t; e] ->
            FixE(type_of_sexp t, fun v -> loop (Env.extend env x v) e)
        | e0 :: es ->
            AppE(loop env e0, List.map ~f:(loop env) es)
  in loop Env.empty sexp0

let expr_of_string s = expr_of_sexp (S.of_string s)
