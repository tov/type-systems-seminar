(* The simply-typed lambda calculus. *)

type typ = Nat
         | Arr of typ list * typ
         | Tup of typ list

type var = string

type exp =
         | Var of var
         | Let of (var * exp) list * exp
         | Zero
         | Succ of exp
         | If0 of {
             cond: exp;
             zero: exp;
             pred: var;
             succ: exp;
           }
         | Tup of exp list
         | Prj of int * exp
         | Lam of (var * typ) list * exp
         | App of exp * exp list
         | Fix of exp

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
  | Var var ->
      env var
  | Let(bindings, body) ->
      let bindings' = List.map (fun (x, e) -> (x, eval env e)) bindings in
      let env' = extend_list env bindings' in
        eval env' body
  | Zero ->
      NatV 0
  | Succ e ->
      (match eval env e with
       | NatV n -> NatV (n + 1)
       | _ -> failwith "nat expected")
  | If0 { cond; zero; pred; succ } ->
      (match eval env cond with
       | NatV 0 -> eval env zero
       | NatV n -> eval (extend env pred (NatV (n - 1))) succ
       | _ -> failwith "nat expected")
  | Tup es ->
      let vs = List.map (eval env) es in
        TupV vs
  | Prj(i, e) ->
      (match eval env e with
       | TupV vs -> List.nth vs i
       | _ -> failwith "tuple expected")
  | Lam(bindings, body) ->
      CloV(env, List.map (fun (x, t) -> x) bindings, body)
  | App(e0, es) ->
      let v0 = eval env e0 in
      let vs = List.map (eval env) es in
        (match v0 with
         | CloV(env, xs, body) ->
            let env = extend_lists env xs vs in
              eval env body
         | _ -> failwith "closure expected")
        (*
  | Fix e ->
      match eval env e with
      | CloV
      *)
