open Core

type ('a, 'b) t = ('a * 'b) list

exception Not_bound

let empty = []
let extend env x v = (x, v) :: env

let rec lookup env x = match env with
  | [] -> raise Not_bound
  | (id, v) :: _ when x = id -> v
  | _ :: tl -> lookup tl x

let rec map env f = match env with
    [] -> []
  | (id, v) :: tl -> (id, f v) :: map tl f

let rec fold_right f env a = match env with
    [] -> a
  | (_, v) :: tl -> f v (fold_right f tl a)

let domain env = List.map env ~f:(fun (id, _) -> id)
