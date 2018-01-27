open Core
open Syntax

exception Type_error of string

let got_exp got exp =
  raise (Type_error ("got " ^ Printer.type_to_string got ^
                     " where " ^ exp ^ " expected"))

let rec tc env = function
  | VarE x ->
      (try Env.lookup env x
       with Env.Unbound_variable _ ->
         raise (Type_error ("unbound variable: " ^ x)))
  | LetE(xes, body) ->
      let xts = List.map ~f:(fun (x, e) -> (x, tc env e)) xes in
        tc (Env.extend_list env xts) body
  | IntE _ -> IntT
  | SubE(e1, e2) ->
      (match tc env e1, tc env e2 with
       | IntT, IntT -> IntT
       | IntT, t2 -> got_exp t2 "int"
       | t1, _ -> got_exp t1 "int")
  | If0E(e1, e2, e3) ->
      (match tc env e1 with
       | IntT ->
           let t2 = tc env e2 in
           let t3 = tc env e3 in
             if t2 = t3
             then t2
             else raise (Type_error "mismatch in if0")
       | t1 ->
           got_exp t1 "int")
  | TupE(es) ->
      TupT(List.map ~f:(tc env) es)
  | _ -> raise (Type_error "syntax not handled")

let type_check = tc Env.empty
