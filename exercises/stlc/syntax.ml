(* Types *)
type typ = IntT
         | ArrT of typ list * typ
         | TupT of typ list

(* Variables *)
type var = string

(* Expressions *)
type exp =
         | VarE of var
         | LetE of (var * exp) list * exp
         | IntE of int
         | SubE of exp * exp
         | If0E of exp * exp * exp
         | TupE of exp list
         | PrjE of int * exp
         | LamE of (var * typ) list * exp
         | AppE of exp * exp list
         | FixE of var * typ * exp

