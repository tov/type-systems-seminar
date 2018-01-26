(* The simply-typed lambda calculus. *)

#require "sexplib";;

type typ = NatT
         | ArrT of typ list * typ
         | TupT of typ list

type var = string

type exp =
         | VarE of var
         | LetE of (var * exp) list * exp
         | ZeroE
         | SuccE of exp
         | If0E of {
             cond: exp;
             zero: exp;
             pred: var;
             succ: exp;
           }
         | TupE of exp list
         | PrjE of int * exp
         | LamE of (var * typ) list * exp
         | AppE of exp * exp list
         | FixE of var * typ * exp

type value =
         | NatV of int
         | TupV of value list
         | CloV of value env * var list * exp
 and 'a env = var -> 'a

(*
 * Environments
 *)

(* The empty environment *)
let env0: 'a env
  = fun v -> failwith ("unbound variable: " ^ v)

(* Extends an environment with one variable. *)
let extend (env: 'a env) x v: 'a env = fun y -> if x = y then v else env y

(* Extends an environment with a list of binding pairs. *)
let extend_list env = List.fold_left (fun env' (x, v) -> extend env' x v) env

(* Extends an environement given a list of variables and a list of
 * things to bind them to. *)
let extend_lists env = List.fold_left2 extend env

(*
 * Evaluation
 *)

let rec eval env = function
  | VarE var ->
      env var
  | LetE(bindings, body) ->
      let bindings' = List.map (fun (x, e) -> (x, eval env e)) bindings in
      let env' = extend_list env bindings' in
        eval env' body
  | ZeroE ->
      NatV 0
  | SuccE e ->
      (match eval env e with
       | NatV n -> NatV (n + 1)
       | _ -> failwith "nat expected")
  | If0E { cond; zero; pred; succ } ->
      (match eval env cond with
       | NatV 0 -> eval env zero
       | NatV n -> eval (extend env pred (NatV (n - 1))) succ
       | _ -> failwith "nat expected")
  | TupE es ->
      let vs = List.map (eval env) es in
        TupV vs
  | PrjE(i, e) ->
      (match eval env e with
       | TupV vs -> List.nth vs i
       | _ -> failwith "tuple expected")
  | LamE(bindings, body) ->
      CloV(env, List.map (fun (x, t) -> x) bindings, body)
  | AppE(e0, es) ->
      let v0 = eval env e0 in
      let vs = List.map (eval env) es in
        (match v0 with
         | CloV(env, xs, body) ->
            let env = extend_lists env xs vs in
              eval env body
         | _ -> failwith "closure expected")
