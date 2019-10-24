open Core
open Syntax

module IM = Int.Map
module IS = Int.Set
module UF = Union_find

exception UnifyError
exception UnifyTypeError

let rec freevar_ty = function
    ITyVar v -> IS.singleton v
  | ITyQbit -> IS.empty
  | ITySingleton -> IS.empty
  | ITyFun (ty1, ty2)
  | ITyProd (ty1, ty2)
  | ITySum (ty1, ty2) -> IS.union (freevar_ty ty1) (freevar_ty ty2)


let rec unify subst eqs =
  let rec extend s = (function
    | ITyVar v ->
        if IM.mem s v then s else IM.add_exn s ~key:v ~data:(UF.create (ITyVar v))
    | ITyFun (ty1, ty2)
    | ITyProd (ty1, ty2)
    | ITySum (ty1, ty2) ->
        extend (extend s ty1) ty2
    | _ -> s)
  in
  match eqs with
  | [] -> subst
  | (ty1, ty2) :: rest ->
      let unify_root subst ty1 ty2 =
        let subst = extend (extend subst ty1) ty2 in
        (match ty1, ty2 with
        | ITyQbit, ITyQbit
        | ITySingleton, ITySingleton -> unify subst rest
        | ITyVar v1, ITyVar v2 ->
            UF.union (Map.find_exn subst v1) (Map.find_exn subst v2);
            unify subst rest
        | ITyVar v, t | t, ITyVar v ->
            if IS.mem (freevar_ty t) v then raise UnifyError;
            UF.set (Map.find_exn subst v) t;
            unify subst rest
        | ITyFun (ty1, ty2), ITyFun (ty3, ty4)
        | ITyProd (ty1, ty2), ITyProd (ty3, ty4)
        | ITySum (ty1, ty2), ITySum (ty3, ty4) ->
            unify subst ((ty1, ty3) :: (ty2, ty4) :: rest)
        | _ -> raise UnifyTypeError)
      in
      let subst = extend (extend subst ty1) ty2 in
      match ty1, ty2 with
      | ITyVar v1, ITyVar v2 ->
          let t1 = Map.find_exn subst v1 in
          let t2 = Map.find_exn subst v2 in
          let ty1, ty2 = UF.get t1, UF.get t2 in (* ! get types before union UF roots ! *)
          UF.union t1 t2;
          unify_root subst ty1 ty2
      | ITyVar v, t | t, ITyVar v ->
          unify_root subst (UF.get (Map.find_exn subst v)) t
      | ty1, ty2 -> unify_root subst ty1 ty2


(* Substitution *)

let empty_subst = IM.empty

let rec subst_type s = function
    ITyVar id ->
      (match Map.find s id with
         Some t ->
           let nty = UF.get t in
           if nty = ITyVar id then ITyVar id
           else begin
             UF.set t nty;
             subst_type s nty
           end
       | None -> ITyVar id)
  | ITyQbit -> ITyQbit
  | ITySingleton -> ITySingleton
  | ITyFun (ty1, ty2) ->ITyFun (subst_type s ty1, subst_type s ty2)
  | ITyProd (ty1, ty2) -> ITyProd (subst_type s ty1, subst_type s ty2)
  | ITySum (ty1, ty2) -> ITySum (subst_type s ty1, subst_type s ty2)

let rec merge_subst s1 s2 =
  Map.fold s1 ~init:s2
    ~f:(fun ~key:v ~data:t2 s ->
          if Map.mem s v then begin
            let t1 = Map.find_exn s v in
            let ty1 = UF.get t1 in
            let ty2 = UF.get t2 in
            UF.union t1 t2;
            unify s [(ty1, ty2)]
          end else
            Map.add_exn s ~key:v ~data:t2)

let print_subst s =
  Map.iteri s ~f:(fun ~key:k ~data:t -> Printf.printf "(%d, %s), " k (string_of_itype (UF.get t)))
