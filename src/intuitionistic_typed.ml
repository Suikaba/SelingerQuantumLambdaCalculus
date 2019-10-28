open Core
open Syntax
open Unify

exception ITypeError

type ityped_term =
    IConst of constant * itype
  | IVar of id * itype
  | ITuple0 of itype
  | IAbst of id * ityped_term * itype
  | IApp of ityped_term * ityped_term * itype
  | IPair of ityped_term * ityped_term * itype
  | ILet of id * id * ityped_term * ityped_term * itype
  | IInjL of ityped_term * itype
  | IInjR of ityped_term * itype
  | IMatch of ityped_term * (id * ityped_term) * (id * ityped_term) * itype
  | ILetRec of id * ityped_term * ityped_term * itype

let fresh_tyvar =
  let counter = ref 0 in
  let body () = counter := !counter + 1; !counter in
  body

let rec string_of_iterm = function
  | IConst (c, ty) -> Printf.sprintf "(%s : %s)" (string_of_const c) (string_of_itype ty)
  | IVar (id, ty) -> Printf.sprintf "(%s : %s)" id (string_of_itype ty)
  | ITuple0 ty -> Printf.sprintf "(* : %s)" (string_of_itype ty)
  | IAbst (id, t, ty) -> Printf.sprintf "((lam %s . %s) : %s)" id (string_of_iterm t) (string_of_itype ty)
  | IApp (t1, t2, ty) -> Printf.sprintf "(%s %s : %s)" (string_of_iterm t1) (string_of_iterm t2) (string_of_itype ty)
  | IPair (t1, t2, ty) -> Printf.sprintf "(<%s, %s> : %s)" (string_of_iterm t1) (string_of_iterm t2) (string_of_itype ty)
  | ILet (x, y, t1, t2, ty) ->
      Printf.sprintf "(let <%s, %s> = %s in %s) : %s" x y (string_of_iterm t1) (string_of_iterm t2) (string_of_itype ty)
  | IInjL (t, ty) ->
      (match t with
       | ITuple0 _ -> Printf.sprintf "(1 : %s)" (string_of_itype ty)
       | t -> Printf.sprintf "(injl(%s) : %s)" (string_of_iterm t) (string_of_itype ty))
  | IInjR (t, ty) ->
      (match t with
       | ITuple0 _ -> Printf.sprintf "(0 : %s)" (string_of_itype ty)
       | t -> Printf.sprintf "(injr(%s) : %s)" (string_of_iterm t) (string_of_itype ty))
  | IMatch (t1, (x, t2), (y, t3), ty) ->
      Printf.sprintf "(match %s with %s -> %s | %s -> %s) : %s"
                     (string_of_iterm t1) x (string_of_iterm t2) y (string_of_iterm t3) (string_of_itype ty)
  | ILetRec (f, t1, t2, ty) ->
      Printf.sprintf "(let rec %s = %s in %s) : %s"
                     f (string_of_iterm t1) (string_of_iterm t2) (string_of_itype ty)


(* type inference *)
let ity_const = function
  | New -> ITyFun (itybit, ITyQbit)
  | Meas -> ITyFun (ITyQbit, itybit)
  | H -> ITyFun (ITyQbit, ITyQbit) (* todo *)
  | _ -> failwith "Not implemented"

let rec ity_infer tyenv = function
  | Const c -> empty_subst, ity_const c, IConst (c, ity_const c)
  | Var id -> empty_subst, Environment.lookup tyenv id, IVar (id, Environment.lookup tyenv id)
  | Tuple0 -> empty_subst, ITySingleton, ITuple0 ITySingleton
  | Abst (id, body) ->
      let tyarg = ITyVar (fresh_tyvar ()) in
      let tyenv = Environment.extend tyenv id tyarg in
      let s, tybody, ibody = ity_infer tyenv body in
      let ty = ITyFun (subst_type s tyarg, tybody) in
      s, ty, IAbst (id, ibody, ty)
  | App (t1, t2) ->
      let s1, tyf, it1 = ity_infer tyenv t1 in
      let s2, tyarg, it2 = ity_infer tyenv t2 in
      let tybody = ITyVar (fresh_tyvar ()) in
      let s = unify (merge_subst s1 s2) [tyf, ITyFun (tyarg, tybody)] in
      let ty = subst_type s tybody in
      s, ty, IApp (it1, it2, ty)
  | Pair (t1, t2) ->
      let s1, ty1, it1 = ity_infer tyenv t1 in
      let s2, ty2, it2 = ity_infer tyenv t2 in
      merge_subst s1 s2, ITyProd (ty1, ty2), IPair (it1, it2, ITyProd (ty1, ty2))
  | Let (x, y, t1, t2) ->
      let s1, ty1, it1 = ity_infer tyenv t1 in
      (match ty1 with
       | ITyVar a ->
           let fst = ITyVar (fresh_tyvar ()) in
           let snd = ITyVar (fresh_tyvar ()) in
           let tyenv = Environment.extend (Environment.extend tyenv x fst) y snd in
           let s2, ty2, it2 = ity_infer tyenv t2 in
           let s = unify (merge_subst s1 s2) [ITyVar a, ITyProd (fst, snd)] in
           s, subst_type s ty2, ILet (x, y, it1, it2, subst_type s ty2)
       | ITyProd (ty1', ty2') ->
           let tyenv = Environment.extend tyenv x ty1' in
           let tyenv = Environment.extend tyenv y ty2' in
           let s2, ty2, it2 = ity_infer tyenv t2 in
           let s = merge_subst s1 s2 in
           s, subst_type s ty2, ILet (x, y, it1, it2, subst_type s ty2)
       | _ -> raise ITypeError)
  | InjL t ->
      let s, ty, it = ity_infer tyenv t in
      let ty = ITySum (ty, ITyVar (fresh_tyvar ())) in
      s, ty, IInjL (it, ty)
  | InjR t ->
      let s, ty, it = ity_infer tyenv t in
      let ty = ITySum (ITyVar (fresh_tyvar ()), ty) in
      s, ty, IInjR (it, ty)
  | Match (t1, (x, t2), (y, t3)) ->
      let s1, ty1, it1 = ity_infer tyenv t1 in
      let s1, xty, yty = (match ty1 with
                          | ITySum (xty, yty) -> s1, xty, yty
                          | ITyVar a ->
                              let xty = ITyVar (fresh_tyvar ()) in
                              let yty = ITyVar (fresh_tyvar ()) in
                              unify s1 [ITyVar a, ITySum (xty, yty)], xty, yty
                          | _ -> raise ITypeError)
       in
       let s2, ty2, it2 = ity_infer (Environment.extend tyenv x xty) t2 in
       let s3, ty3, it3 = ity_infer (Environment.extend tyenv y yty) t3 in
       let s = unify (merge_subst s1 (merge_subst s2 s3)) [ty2, ty3] in
       s, subst_type s ty2, IMatch (it1, (x, it2), (y, it3), subst_type s ty2)
  | LetRec (f, t1, t2) ->
      let tyenv = Environment.extend tyenv f (ITyVar (fresh_tyvar ())) in
      let s1, tyf, it1 = ity_infer tyenv t1 in
      let s2, ty2, it2 = ity_infer tyenv t2 in
      let s = unify (merge_subst s1 s2) [tyf, Environment.lookup tyenv f] in
      s, subst_type s ty2, ILetRec (f, it1, it2, subst_type s ty2)

(* create intuitionistic typed term *)
let ity_term tyenv t =
  let s, _, it = ity_infer tyenv t in
  let rec fix_with_singleton = (function
    | ITyVar _ -> ITySingleton (* replace with singleton *)
    | ITyQbit -> ITyQbit
    | ITySingleton -> ITySingleton
    | ITyFun (ty1, ty2) -> ITyFun (fix_with_singleton ty1, fix_with_singleton ty2)
    | ITyProd (ty1, ty2) -> ITyProd (fix_with_singleton ty1, fix_with_singleton ty2)
    | ITySum (ty1, ty2) -> ITySum (fix_with_singleton ty1, fix_with_singleton ty2))
  in
  let rec correct_type = (function
    | IConst (c, ty) -> IConst (c, fix_with_singleton (subst_type s ty))
    | IVar (id, ty) -> IVar (id, fix_with_singleton (subst_type s ty))
    | ITuple0 ty -> ITuple0 ty
    | IAbst (id, t, ty) -> IAbst (id, correct_type t, fix_with_singleton (subst_type s ty))
    | IApp (t1, t2, ty) -> IApp (correct_type t1, correct_type t2, fix_with_singleton (subst_type s ty))
    | IPair (t1, t2, ty) -> IPair (correct_type t1, correct_type t2, fix_with_singleton (subst_type s ty))
    | ILet (x, y, t1, t2, ty) -> ILet (x, y, correct_type t1, correct_type t2, fix_with_singleton (subst_type s ty))
    | IInjL (t, ty) -> IInjL (correct_type t, fix_with_singleton (subst_type s ty))
    | IInjR (t, ty) -> IInjR (correct_type t, fix_with_singleton (subst_type s ty))
    | IMatch (t1, (x, t2), (y, t3), ty) -> IMatch (correct_type t1, (x, correct_type t2), (y, correct_type t3), fix_with_singleton (subst_type s ty))
    | ILetRec (f, t1, t2, ty) -> ILetRec (f, correct_type t1, correct_type t2, fix_with_singleton (subst_type s ty)))
  in
  correct_type it
