open Syntax

(* Thrown on type errors. *)
exception Type_error of string

(* Returns the type of an expression or throw Type_error. *)
val type_check : typ exp -> typ
