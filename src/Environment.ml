type ('a, 'b) t = ('a * 'b) list

exception Not_bound

let empty = []
let extend env x v = (x, v) :: env

let rec lookup env x = match env with
  | [] -> raise Not_bound
  | (id, v) :: _ when x = id -> v
  | _ :: tl -> lookup tl x

let rec map f = function
    [] -> []
  | (id, v) :: tl -> (id, f v) :: map f tl

let rec fold_right f env a = match env with
    [] -> a
  | (_, v) :: tl -> f v (fold_right f tl a)

