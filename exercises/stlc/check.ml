open Core
open Syntax

exception Type_error of string

(* Throws a type error contrasting what we got and expected. *)
let got_exp got exp =
  raise (Type_error ("got " ^ Printer.type_to_string got ^
                     " where " ^ exp ^ " expected"))

(* Asserts that the given type is int. *)
let assert_int = function
  | IntT -> ()
  | t    -> got_exp t "int"

(* Asserts that two types are the same. *)
let assert_same_type t1 t2 =
  if t1 = t2
  then ()
  else raise (Type_error ("type mismatch: " ^
                          Printer.type_to_string t1 ^ " ≠ " ^
                          Printer.type_to_string t2))

(* Asserts that two lists of types are the same. *)
let assert_same_types = List.iter2_exn ~f:assert_same_type

(* Projects the `i`th element of a tuple type. *)
let prj_tup i = function
  | TupT ts as t ->
      (match List.nth ts i with
       | Some t -> t
       | None   ->
           got_exp t ("tuple of size at least " ^ string_of_int (i + 1)))
  | t -> got_exp t "tuple type"

(* Unpacks an arrow type of arity `i`. *)
let un_arr i = function
  | ArrT(ts, tr) as t ->
      if i = List.length ts
      then (ts, tr)
      else got_exp t ("arrow of arity " ^ string_of_int i)
  | t -> got_exp t "arrow type"

let rec tc = function
  | VarE x -> x
  | LetE(rhses, body) ->
      let ts  = List.map ~f:tc rhses in
        tc (body ts)
  | IntE _ -> IntT
  | SubE(e1, e2) ->
      assert_int (tc e1);
      assert_int (tc e2);
      IntT
  | If0E(e1, e2, e3) ->
      assert_int (tc e1);
      let t2 = tc e2 in
      let t3 = tc e3 in
      assert_same_type t2 t3;
      t2
  | TupE(es) ->
      TupT(List.map ~f:tc es)
  | PrjE(ix, e) ->
      prj_tup ix (tc e)
  | LamE(ts, body) ->
      tc (body ts)
  | AppE(e0, es) ->
      let (tas, tr) = un_arr (List.length es) (tc e0) in
      let ts        = List.map ~f:tc es in
      assert_same_types tas ts;
      tr
  | FixE(t, e) ->
      let t'   = tc (e t) in
      assert_same_type t t';
      t

let type_check = tc
