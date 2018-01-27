open Core
open Syntax

(* Values are the result of evaluation. *)
type value =
         | IntV of int
         | TupV of value list
         | FunV of (value list -> value exp)

(* Value printing: *)
let rec string_of_value = function
  | IntV z -> string_of_int z
  | TupV vs ->
      let ss = List.map ~f:string_of_value vs in
        "(" ^ String.concat ~sep:" " ("tup" :: ss) ^ ")"
  | FunV _ -> "#<function>"

(* Exception thrown in cases that should not be possible in well-typed
 * programs. *)
exception Can'tHappen of string

(* Evaluation, the heart of the interpreter: *)
let rec eval : value exp -> value = function
  | VarE var -> var
  | LetE(rhses, body) ->
      let vs = List.map ~f:eval rhses in
      eval (body vs)
  | IntE z ->
      IntV z
  | SubE(e1, e2) ->
      (match eval e1, eval e2 with
       | IntV z1, IntV z2 -> IntV (z1 - z2)
       | _ -> raise (Can'tHappen "ints expected"))
  | If0E(cond, zero, non_zero) ->
      (match eval cond with
       | IntV 0 -> eval zero
       | IntV _ -> eval non_zero
       | _ -> raise (Can'tHappen "int expected"))
  | TupE es ->
      let vs = List.map ~f:eval es in
        TupV vs
  | PrjE(i, e) ->
      (match eval e with
       | TupV vs -> List.nth_exn vs i
       | _ -> raise (Can'tHappen "tuple expected"))
  | LamE(_, body) ->
      FunV(fun vs -> body vs)
  | AppE(e0, es) ->
      let v0 = eval e0 in
      let vs = List.map ~f:eval es in
        (match v0 with
         | FunV(f) -> eval (f vs)
         | _ -> raise (Can'tHappen "closure expected"))
  | FixE(_, e) as e0 ->
      let v = FunV(fun vs -> AppE(e0, List.map ~f:(fun x -> VarE x) vs)) in
        eval (e v)
