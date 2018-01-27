open Core

(* Types *)
type typ = IntT
         | ArrT of typ list * typ
         | TupT of typ list

(* Variables *)
type var = Var.t

(* Expressions *)
type 'a exp =
         | VarE of 'a
         | LetE of 'a exp list * ('a list -> 'a exp)
         | IntE of int
         | SubE of 'a exp * 'a exp
         | If0E of 'a exp * 'a exp * 'a exp
         | TupE of 'a exp list
         | PrjE of int * 'a exp
         | LamE of typ list * ('a list -> 'a exp)
         | AppE of 'a exp * 'a exp list
         | FixE of typ * ('a -> 'a exp)

type any_exp = { exp : 'a . 'a exp }

(* Computes the free variables of an expression. *)
let fv =
  let module Set = Var.Set in
  let rec fv = function
  | VarE x -> Set.singleton x
  | LetE(ts, body) -> fv (body (List.map ~f:(fun _ -> "") ts))
  | IntE _ -> Set.empty
  | SubE(e1, e2) -> Set.union (fv e1) (fv e2)
  | If0E(e1, e2, e3) -> Set.union_list [fv e1; fv e2; fv e3]
  | TupE es -> Set.union_list (List.map ~f:fv es)
  | PrjE(_, e) -> fv e
  | LamE(ts, body) -> fv (body (List.map ~f:(fun _ -> "") ts))
  | AppE(e0, es) -> Set.union_list (List.map ~f:fv (e0 :: es))
  | FixE(_, e) -> fv (e "")
  in fun e -> Set.remove (fv e) ""

