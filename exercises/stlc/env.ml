open Core

(* Environments. See env.mli for interface. *)

type var = Var.t

type 'a t = (var * 'a) list

exception UnboundVariable of var

let empty = []

let rec lookup env x = match env with
  | [] -> raise (UnboundVariable x)
  | (y, v) :: _ when x = y -> v
  | _ :: env' -> lookup env' x

let extend env x v =
  (x, v) :: env

let extend_list env =
  List.fold ~f:(fun env' (x, v) -> extend env' x v) ~init:env

let extend_lists env =
  List.fold2_exn ~f:extend ~init:env
