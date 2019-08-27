
type id = string

type constant =
   | New
   | Meas
   | H | X | Y | Z

type term =
    Const of constant
  | Var of id
  | Tuple0
  | Abst of id * term
  | App of term * term
  | Pair of term * term
  | Let of id * id * term * term
  | InjL of term
  | InjR of term
  | Match of term * (id * term) * (id * term)
  | LetRec of id * id * term * term

type value =
  | Qbit of float * float  (* basis |0>, |1> *)
  | VConst of constant
  | VPair of value * value
  | VTuple0
  | VInjL of value
  | VInjR of value
  | VAbst of id * term * (id, value) Environment.t ref


(* =============================================================================
 * Types
 *)
type tyvar = int

type qtype =
    QTyQbit
  | QTySingleton       (* T *)
  | QTyExp of qtype       (* !A *)
  | QTyFun of qtype * qtype
  | QTyProd of qtype * qtype (* A * B *)
  | QTySum of qtype * qtype  (* disjoint union: A + B *)

let qtybit = QTySum (QTySingleton, QTySingleton)

let fresh_tyvar =
  let counter = ref 0 in
  let body () = counter := !counter + 1; !counter in
  body

(* intuitionistic types *)
type itype =
    ITyQbit
  | ITySingleton
  | ITyVar of tyvar
  | ITyFun of itype * itype
  | ITyProd of itype * itype
  | ITySum of itype * itype
  | ITyPair of itype * itype

let itybit = ITySum (ITySingleton, ITySingleton)

(* printing *)
let string_of_const = function
    New -> "new"
  | Meas -> "meas"
  | H -> "H"
  | X -> "X"
  | Y -> "Y"
  | Z -> "Z"

let rec string_of_term = function
    Const c -> string_of_const c
  | Var id -> id
  | Abst (id, t) -> Printf.sprintf "(lam %s . %s)" id (string_of_term t)
  | App (t1, t2) ->
      let add_paren t = (match t with
        | App _ -> "(" ^ (string_of_term t) ^ ")"
        | t -> string_of_term t) in
      Printf.sprintf "%s %s" (add_paren t1) (add_paren t2)
  | Pair (t1, t2) -> Printf.sprintf "<%s, %s>" (string_of_term t1) (string_of_term t2)
  | Tuple0 -> "*"
  | Let (id, para, t1, t2) -> Printf.sprintf "let %s %s = %s in %s" id para (string_of_term t1) (string_of_term t2)
  | InjL t ->
      (match t with
       | Tuple0 -> "1"
       | t -> Printf.sprintf "injl(%s)" (string_of_term t))
  | InjR t ->
      (match t with
       | Tuple0 -> "0"
       | t -> Printf.sprintf "injr(%s)" (string_of_term t))
  | Match (t, (x, t2), (y, t3)) ->
      Printf.sprintf "match %s with %s -> %s | %s -> %s"
                     (string_of_term t) x (string_of_term t2) y (string_of_term t3)
  | LetRec (id, para, t1, t2) ->
      Printf.sprintf "let rec %s %s = %s in %s" id para (string_of_term t1) (string_of_term t2)

let rec string_of_value = function
    Qbit (alpha, beta) -> Printf.sprintf "QBit<%f, %f>" alpha beta
  | VConst c -> string_of_const c
  | VPair (v1, v2) -> Printf.sprintf "(%s , %s)" (string_of_value v1) (string_of_value v2)
  | VTuple0 -> "*"
  | VInjL v -> Printf.sprintf "injl(%s)" (string_of_value v)
  | VInjR v -> Printf.sprintf "injr(%s)" (string_of_value v)
  | VAbst (id, body, _) -> Printf.sprintf "(lam %s . %s)" id (string_of_term body)


let rec string_of_itype ty =
  let need_paren = (function
    | ITyFun _
    | ITyProd _
    | ITySum _
    | ITyPair _ -> true
    | _ -> false) in
  match ty with
    ITyQbit -> "qbit"
  | ITySingleton -> "T"
  | ITyVar v -> Printf.sprintf "v%d" v
  | ITyFun (ty1, ty2) ->
      if need_paren ty1 then
        Printf.sprintf "(%s) -> %s" (string_of_itype ty1) (string_of_itype ty2)
      else
        Printf.sprintf "%s -> %s" (string_of_itype ty1) (string_of_itype ty2)
  | ITyProd (ty1, ty2) ->
      if need_paren ty1 then
        Printf.sprintf "(%s) * %s" (string_of_itype ty1) (string_of_itype ty2)
      else
        Printf.sprintf "%s * %s" (string_of_itype ty1) (string_of_itype ty2)
  | ITySum (ty1, ty2) ->
      if need_paren ty1 then
        Printf.sprintf "(%s) + %s" (string_of_itype ty1) (string_of_itype ty2)
      else
        Printf.sprintf "%s + %s" (string_of_itype ty1) (string_of_itype ty2)
  | ITyPair (ty1, ty2) -> Printf.sprintf "<%s, %s>" (string_of_itype ty1) (string_of_itype ty2)
