open Core
open Syntax

(* Values are the result of evaluation. *)
type value =
         | IntV of int
         | TupV of value list
         | CloV of env * var list * exp
 and env = value Env.t

(* Value printing: *)
let rec string_of_value = function
  | IntV z -> string_of_int z
  | TupV vs ->
      let ss = List.map ~f:string_of_value vs in
        "(" ^ String.concat ~sep:" " ("tuple" :: ss) ^ ")"
  | CloV _ -> "#<function>"

(* Exception thrown in cases that should not be possible in well-typed
 * programs. *)
exception Can'tHappen of string

(* Evaluation, the heart of the interpreter: *)
let rec eval env = function
  | VarE var ->
      Env.lookup env var
  | LetE(bindings, body) ->
      let bindings' = List.map ~f:(fun (x, e) -> (x, eval env e)) bindings in
      let env' = Env.extend_list env bindings' in
        eval env' body
  | IntE z ->
      IntV z
  | SubE(e1, e2) ->
      (match eval env e1, eval env e2 with
       | IntV z1, IntV z2 -> IntV (z1 - z2)
       | _ -> raise (Can'tHappen "ints expected"))
  | If0E(cond, zero, non_zero) ->
      (match eval env cond with
       | IntV 0 -> eval env zero
       | IntV _ -> eval env non_zero
       | _ -> raise (Can'tHappen "int expected"))
  | TupE es ->
      let vs = List.map ~f:(eval env) es in
        TupV vs
  | PrjE(i, e) ->
      (match eval env e with
       | TupV vs -> List.nth_exn vs i
       | _ -> raise (Can'tHappen "tuple expected"))
  | LamE(bindings, body) ->
      CloV(env, List.map ~f:(fun (x, _) -> x) bindings, body)
  | AppE(e0, es) ->
      let v0 = eval env e0 in
      let vs = List.map ~f:(eval env) es in
        (match v0 with
         | CloV(env, xs, body) ->
            let env = Env.extend_lists env xs vs in
              eval env body
         | _ -> raise (Can'tHappen "closure expected"))
  | FixE(x, (ArrT(ts, _) as t), e) ->
      let ys = Var.fresh_n (List.length ts) (fv e) in
      let v = CloV(env, ys,
                   AppE(FixE(x, t, e), List.map ~f:(fun x -> VarE x) ys)) in
        eval (Env.extend env x v) e
  | FixE(_, _, _) ->
      raise (Can'tHappen "fix requires 1-arg function type")
