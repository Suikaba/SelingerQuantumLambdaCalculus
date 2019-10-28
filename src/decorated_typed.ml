open Core
open Syntax
open Intuitionistic_typed

exception NotImplemented
exception QualMismatch
exception CannotFixQual

module SS = String.Set
module UF = Union_find

module Subst = Int.Map
module QEnv = String.Map

type qvar = int (* qual variable *)

let fresh_qvar =
  let counter = ref 0 in
  let body () = counter := !counter + 1; !counter in
  body

type dtyped_term =
    DConst of constant * dtype
  | DVar of id * dtype
  | DTuple0 of dtype
  | DAbst of id * dtyped_term * dtype
  | DApp of dtyped_term * dtyped_term * dtype
  | DPair of dtyped_term * dtyped_term * dtype
  | DLet of id * id * dtyped_term * dtyped_term * dtype
  | DInjL of dtyped_term * dtype
  | DInjR of dtyped_term * dtype
  | DMatch of dtyped_term * (id * dtyped_term) * (id * dtyped_term) * dtype
  | DLetRec of id * dtyped_term * dtyped_term * dtype

let const_strs = ["new"; "meas"; "H"; "cnot"; "X"; "Y"; "Z"]

(* =============================================================================
 * Print
 *)
let rec string_of_dterm = function
    DConst (c, ty) -> Printf.sprintf "(%s : %s)" (string_of_const c) (string_of_dtype ty)
  | DVar (id, ty) -> Printf.sprintf "(%s : %s)" id (string_of_dtype ty)
  | DTuple0 ty -> Printf.sprintf "(* : %s)" (string_of_dtype ty)
  | DAbst (id, t, ty) -> Printf.sprintf "((lam %s . %s) : %s)" id (string_of_dterm t) (string_of_dtype ty)
  | DApp (t1, t2, ty) -> Printf.sprintf "(%s %s : %s)" (string_of_dterm t1) (string_of_dterm t2) (string_of_dtype ty)
  | DPair (t1, t2, ty) -> Printf.sprintf "(<%s, %s> : %s)" (string_of_dterm t1) (string_of_dterm t2) (string_of_dtype ty)
  | DLet (x, y, t1, t2, ty) ->
      Printf.sprintf "(let <%s, %s> = %s in %s) : %s" x y (string_of_dterm t1) (string_of_dterm t2) (string_of_dtype ty)
  | DInjL (t, ty) ->
      (match t with
       | DTuple0 _ -> Printf.sprintf "(1 : %s)" (string_of_dtype ty)
       | t -> Printf.sprintf "(injl(%s) : %s)" (string_of_dterm t) (string_of_dtype ty))
  | DInjR (t, ty) ->
      (match t with
       | DTuple0 _ -> Printf.sprintf "(0 : %s)" (string_of_dtype ty)
       | t -> Printf.sprintf "(injr(%s) : %s)" (string_of_dterm t) (string_of_dtype ty))
  | DMatch (t1, (x, t2), (y, t3), ty) ->
      Printf.sprintf "(match %s with %s -> %s | %s -> %s) : %s"
                     (string_of_dterm t1) x (string_of_dterm t2) y (string_of_dterm t3) (string_of_dtype ty)
  | DLetRec (f, t1, t2, ty) ->
      Printf.sprintf "(let rec %s = %s in %s) : %s"
                     f (string_of_dterm t1) (string_of_dterm t2) (string_of_dtype ty)


let rec free_variables = function
  | IConst _ -> SS.empty
  | IVar (id, _) -> SS.singleton id
  | ITuple0 _ -> SS.empty
  | IAbst (id, t, _) -> SS.remove (free_variables t) id
  | IApp (t1, t2, _) -> SS.union (free_variables t1) (free_variables t2)
  | IPair (t1, t2, _) -> SS.union (free_variables t1) (free_variables t2)
  | ILet (x, y, t1, t2, _) ->
      let s1 = free_variables t1 in
      let s2 = SS.remove (SS.remove (free_variables t2) x) y in
      SS.union s1 s2
  | IInjL (t, _) | IInjR (t, _) -> free_variables t
  | IMatch (t1, (x, t2), (y, t3), _) ->
      let s1 = free_variables t1 in
      let s2 = SS.remove (free_variables t2) x in
      let s3 = SS.remove (free_variables t3) y in
      SS.union (SS.union s1 s2) s3
  | ILetRec (f, t1, t2, _) ->
      SS.union (SS.remove (free_variables t1) f) (SS.remove (free_variables t2) f)

let rec free_variables_d = function
  | DConst _ -> SS.empty
  | DVar (id, _) -> SS.singleton id
  | DTuple0 _ -> SS.empty
  | DAbst (id, t, _) -> SS.remove (free_variables_d t) id
  | DApp (t1, t2, _) -> SS.union (free_variables_d t1) (free_variables_d t2)
  | DPair (t1, t2, _) -> SS.union (free_variables_d t1) (free_variables_d t2)
  | DLet (x, y, t1, t2, _) ->
      let s1 = free_variables_d t1 in
      let s2 = SS.remove (SS.remove (free_variables_d t2) x) y in
      SS.union s1 s2
  | DInjL (t, _) | DInjR (t, _) -> free_variables_d t
  | DMatch (t1, (x, t2), (y, t3), _) ->
      let s1 = free_variables_d t1 in
      let s2 = SS.remove (free_variables_d t2) x in
      let s3 = SS.remove (free_variables_d t3) y in
      SS.union (SS.union s1 s2) s3
  | DLetRec (f, t1, t2, _) ->
      SS.union (SS.remove (free_variables_d t1) f) (SS.remove (free_variables_d t2) f)


let get_qual = function
    TyQBit -> Linear
  | TySingleton q
  | TyFun (q, _, _)
  | TyProd (q, _, _)
  | TySum (q, _, _) -> q

let get_type = function
    DConst (_, ty)
  | DVar (_, ty)
  | DTuple0 ty
  | DAbst (_, _, ty)
  | DApp (_, _, ty)
  | DPair (_, _, ty)
  | DLet (_, _, _, _, ty)
  | DInjL (_, ty)
  | DInjR (_, ty)
  | DMatch (_, _, _, ty)
  | DLetRec (_, _, _, ty) -> ty

(* =============================================================================
 * Unification
 *)

(* if subst have qv, this proc do nothing *)
let extend_subst s qv =
  if Subst.mem s qv then s
  else Subst.add_exn s ~key:qv ~data:(UF.create (QVar qv))

let rec unify subst eqs =
  let merge_qual q1 q2 = (match q1, q2 with
      Linear, Linear | NonLinear, NonLinear -> subst
    | QVar v, Linear | Linear, QVar v ->
        let subst = extend_subst subst v in
        let t = Subst.find_exn subst v in
        (match UF.get t with
           Linear -> ()
         | NonLinear -> raise QualMismatch
         | QVar _ -> UF.set t Linear);
        subst
    | QVar v, NonLinear | NonLinear, QVar v ->
        let subst = extend_subst subst v in
        let t = Subst.find_exn subst v in
        (match UF.get t with
           Linear -> raise QualMismatch
         | NonLinear -> ()
         | QVar _ -> UF.set t NonLinear);
        subst
    | QVar v1, QVar v2 ->
        let subst = extend_subst (extend_subst subst v1) v2 in
        let t1 = Subst.find_exn subst v1 in
        let t2 = Subst.find_exn subst v2 in
        let q1 = UF.get t1 in
        let q2 = UF.get t2 in
        UF.union t1 t2;
        (match q1, q2 with
           Linear, NonLinear -> raise QualMismatch
         | Linear, _ | _, Linear -> UF.set t1 Linear; subst
         | NonLinear, _ | _, NonLinear -> UF.set t1 NonLinear; subst
         | QVar _, QVar _ -> subst)
    | _ -> raise QualMismatch)
  in
  match eqs with
    [] -> subst
  | (ty1, ty2) :: tl ->
      match ty1, ty2 with
        TyQBit, TyQBit -> unify subst tl
      | TySingleton q1, TySingleton q2 ->
          let subst = merge_qual q1 q2 in
          unify subst tl
      | TyFun (q1, ty11, ty12), TyFun (q2, ty21, ty22)
      | TyProd (q1, ty11, ty12), TyProd (q2, ty21, ty22)
      | TySum (q1, ty11, ty12), TySum (q2, ty21, ty22) ->
          let subst = merge_qual q1 q2 in
          unify subst ((ty11, ty21) :: (ty12, ty22) :: tl)
      | _ -> failwith "unify: Fatal error"

let rec subst_qual subst q = match q with
    Linear -> Linear
  | NonLinear -> NonLinear
  | QVar v ->
      if Subst.mem subst v then
        let t = Subst.find_exn subst v in
        let nq = UF.get t in
        if nq = QVar v then nq
        else begin
          UF.set t nq;
          subst_qual subst nq
        end
      else QVar v

let rec subst_qual_ty subst ty = match ty with
    TyQBit -> TyQBit
  | TySingleton q -> TySingleton (subst_qual subst q)
  | TyFun (q, ty1, ty2) -> TyFun (subst_qual subst q, subst_qual_ty subst ty1, subst_qual_ty subst ty2)
  | TyProd (q, ty1, ty2) -> TyProd (subst_qual subst q, subst_qual_ty subst ty1, subst_qual_ty subst ty2)
  | TySum (q, ty1, ty2) -> TySum (subst_qual subst q, subst_qual_ty subst ty1, subst_qual_ty subst ty2)

let rec subst_qual_term subst t = match t with
    DConst (c, ty) -> DConst (c, subst_qual_ty subst ty)
  | DVar (id, ty) -> DVar (id, subst_qual_ty subst ty)
  | DTuple0 ty -> DTuple0 (subst_qual_ty subst ty)
  | DAbst (id, t, ty) -> DAbst (id, subst_qual_term subst t, subst_qual_ty subst ty)
  | DApp (t1, t2, ty) -> DApp (subst_qual_term subst t1, subst_qual_term subst t2, subst_qual_ty subst ty)
  | DPair (t1, t2, ty) -> DPair (subst_qual_term subst t1, subst_qual_term subst t2, subst_qual_ty subst ty)
  | DLet (id1, id2, t1, t2, ty) -> DLet (id1, id2, subst_qual_term subst t1, subst_qual_term subst t2, subst_qual_ty subst ty)
  | DInjL (t, ty) -> DInjL (subst_qual_term subst t, subst_qual_ty subst ty)
  | DInjR (t, ty) -> DInjR (subst_qual_term subst t, subst_qual_ty subst ty)
  | DMatch (t1, (id2, t2), (id3, t3), ty) ->
      DMatch (subst_qual_term subst t1, (id2, subst_qual_term subst t2), (id3, subst_qual_term subst t3), subst_qual_ty subst ty)
  | DLetRec (f, t1, t2, ty) ->
      DLetRec (f, subst_qual_term subst t1, subst_qual_term subst t2, subst_qual_ty subst ty)

let merge_subst s1 s2 =
  Subst.fold s1 ~init:s2
    ~f:(fun ~key:v ~data:t2 s ->
          if Subst.mem s v then
            (* todo *)
            let t1 = Subst.find_exn s v in
            UF.union t1 t2;
            s
          else
            Subst.add_exn s ~key:v ~data:t2)


let rec add_qualifier = function
    ITyQbit -> TyQBit
  | ITySingleton -> TySingleton (QVar (fresh_qvar ()))
  | ITyVar _ -> failwith "Todo: Error message"
  | ITyFun (ty1, ty2) -> TyFun (QVar (fresh_qvar ()), add_qualifier ty1, add_qualifier ty2)
  | ITyProd (ty1, ty2) -> TyProd (QVar (fresh_qvar ()), add_qualifier ty1, add_qualifier ty2)
  | ITySum (ty1, ty2) -> TySum (QVar (fresh_qvar ()), add_qualifier ty1, add_qualifier ty2)

(* fix q with q' *)
let fix_qual subst q q' =
  let get_root_q s = (function
      Linear -> s, Linear
    | NonLinear -> s, NonLinear
    | QVar v ->
        let s = extend_subst s v in
        s, UF.get (Subst.find_exn s v))
  in
  let subst, q = get_root_q subst q in
  match q, q' with
    NonLinear, NonLinear
  | Linear, Linear -> subst
  | QVar v, NonLinear ->
      let t = Subst.find_exn subst v in
      UF.set t NonLinear;
      subst
  | QVar v, Linear ->
      let t = Subst.find_exn subst v in
      UF.set t Linear;
      subst
  | _ -> raise CannotFixQual

let fix_nonlinear_ids subst qenv t1 t2 =
  SS.fold ~init:subst (SS.diff (SS.inter (free_variables t1) (free_variables t2)) (SS.of_list const_strs))
    ~f:(fun s id ->
          let q = get_qual (Environment.lookup qenv id) in
          fix_qual s q NonLinear)

let rec subtyping subst rels =
  let subty_qual subst q1 q2 = (match q1, q2 with
    | Linear, _ -> fix_qual subst q2 Linear
    | _, NonLinear -> fix_qual subst q1 NonLinear
    | _ -> subst)
  in
  match rels with
    [] -> subst
  | (ty1, ty2) :: tl ->
      match ty1, ty2 with
        TyQBit, TyQBit -> subtyping subst tl
      | TySingleton q1, TySingleton q2 -> subtyping (subty_qual subst (subst_qual subst q1) (subst_qual subst q2)) tl
      | TyFun (q1, ty11, ty12), TyFun (q2, ty21, ty22) ->
          let subst = subty_qual subst q1 q2 in
          let rels = (ty21, ty11) :: (ty12, ty22) :: tl in
          subtyping subst rels
      | TyProd (q1, ty11, ty12), TyProd (q2, ty21, ty22)
      | TySum (q1, ty11, ty12), TySum (q2, ty21, ty22) ->
          let subst = subty_qual subst q1 q2 in
          let rels = (ty11, ty21) :: (ty12, ty22) :: tl in
          subtyping subst rels
      | _ -> failwith "subtyping: Fatal error"

(*
 * @return (subst, subty_rels, dterm)
 * @note : collect eqs and subtype relations
 *)
let rec dterm_of_iterm qenv = function
  | IConst (c, ty) -> Subst.empty, [], DConst (c, add_qualifier ty) (* todo: subtyping *)
  | IVar (id, ty) ->
      let ty' = add_qualifier ty in
      Subst.empty, [(Environment.lookup qenv id), ty'], DVar (id, ty')
  | ITuple0 ty -> Subst.empty, [], DTuple0 (add_qualifier ty)
  | IAbst (id, body, ITyFun (tyarg, _)) ->
      let tyarg' = add_qualifier tyarg in
      let qenv = Environment.extend qenv id tyarg' in
      let s, rels, body' = dterm_of_iterm qenv body in
      s, rels, DAbst (id, body', TyFun (QVar (fresh_qvar ()), tyarg', get_type body'))
  | IApp (t1, t2, _) ->
      let s1, rels1, dt1 = dterm_of_iterm qenv t1 in
      let s2, rels2, dt2 = dterm_of_iterm qenv t2 in
      let ty1 = get_type dt1 in
      let ty2 = get_type dt2 in
      (match ty1 with
         TyFun (_, tyarg, tybody) ->
           let s = unify (merge_subst s1 s2) [tyarg, ty2] in
           let s = fix_qual s (get_qual ty1) Linear in
           let s = fix_nonlinear_ids s qenv t1 t2 in
           s, rels1 @ rels2, DApp (dt1, dt2, subst_qual_ty s tybody)
       | _ -> failwith "dterm_of_iterm:IApp: Fatal error")
  | IPair (t1, t2, _) ->
      let s1, rels1, dt1 = dterm_of_iterm qenv t1 in
      let s2, rels2, dt2 = dterm_of_iterm qenv t2 in
      let ty1 = get_type dt1 in
      let ty2 = get_type dt2 in
      let s = merge_subst s1 s2 in
      let s = fix_nonlinear_ids s qenv t1 t2 in
      s, rels1 @ rels2, DPair (dt1, dt2, TyProd (QVar (fresh_qvar ()), subst_qual_ty s ty1, subst_qual_ty s ty2))
  | ILet (x, y, t1, t2, _) ->
      let s1, rels1, dt1 = dterm_of_iterm qenv t1 in
      let ty1 = get_type dt1 in
      (match ty1 with
         TyProd (q, xty, yty) -> (* todo: must use q as qual of xty and yty *)
            let qenv = Environment.extend (Environment.extend qenv x xty) y yty in
            let s2, rels2, dt2 = dterm_of_iterm qenv t2 in
            let s = merge_subst s1 s2 in
            let nonlin_ids = SS.diff (SS.inter (free_variables t1) (free_variables t2)) (SS.of_list [x; y]) in
            let s = SS.fold ~init:s nonlin_ids
                      ~f:(fun s id ->
                            let q = get_qual (Environment.lookup qenv id) in
                            fix_qual s q NonLinear) in
            s, rels1 @ rels2, DLet (x, y, dt1, dt2, subst_qual_ty s (get_type dt2))
       | _ -> failwith "dterm_of_iterm:ILet: Fatal error"
)
  | IInjL (t, ty) ->
      let s, rels, dt = dterm_of_iterm qenv t in
      let ty1 = get_type dt in
      (match ty with
         ITySum (_, ty2) ->
           let ty2 = add_qualifier ty2 in
           s, rels, DInjL (dt, TySum (QVar (fresh_qvar ()), ty1, ty2))
       | _ -> failwith "dterm_of_iterm:IInjL: Fatal error")
  | IInjR (t, ty) ->
      let s, rels, dt = dterm_of_iterm qenv t in
      let ty2 = get_type dt in
      (match ty with
         ITySum (ty1, _) ->
           let ty1 = add_qualifier ty1 in
           s, rels, DInjR (dt, TySum (QVar (fresh_qvar ()), ty1, ty2))
       | _ -> failwith "dterm_of_iterm:IInjR: Fatal error")
  | IMatch (t1, (x, t2), (y, t3), _) ->
      let s1, rels1, dt1 = dterm_of_iterm qenv t1 in
      let s2, rels2, dt2 = dterm_of_iterm (Environment.extend qenv x (get_type dt1)) t2 in
      let s3, rels3, dt3 = dterm_of_iterm (Environment.extend qenv y (get_type dt1)) t3 in
      let s = unify (merge_subst (merge_subst s1 s2) s3) [get_type dt2, get_type dt3] in
      s, rels1 @ rels2 @ rels3, DMatch (dt1, (x, dt2), (y, dt3), subst_qual_ty s (get_type dt2))
  | ILetRec (f, t1, t2, _) ->
      (match t1 with
         IAbst (_, _, ITyFun (tyarg, tybody)) ->
           let tyf = TyFun (NonLinear, add_qualifier tyarg, add_qualifier tybody) in
           let qenv = Environment.extend qenv f tyf in
           let s1, rels1, dt1 = dterm_of_iterm qenv t1 in
           let s2, rels2, dt2 = dterm_of_iterm qenv t2 in
           let s = unify (merge_subst s1 s2) [tyf, get_type dt1] in
           s, rels1 @ rels2, DLetRec (f, subst_qual_term s dt1, subst_qual_term s dt2, subst_qual_ty s (get_type dt2))
       | _ -> failwith "dterm_of_iterm:ILetRec: Fatal error")
  | _ -> failwith "Fatal error"

let rec check_abst_pair_sum subst qenv t = match t with
  | DAbst (id, body, TyFun (q, tyarg, _)) ->
      let fvs = SS.diff (free_variables_d body) (SS.of_list (id :: const_strs)) in
      let qfvs = SS.to_list fvs |> List.map ~f:(fun id -> Environment.lookup qenv id) in
      let have_lin = List.exists qfvs ~f:(fun q -> q = Linear) in
      let subst = if have_lin then fix_qual subst q Linear else subst in
      let subst = if NonLinear = q then
                    List.fold ~init:subst qfvs ~f:(fun s q -> fix_qual s q NonLinear)
                  else subst in
      let qenv = Environment.extend qenv id (get_qual tyarg) in
      check_abst_pair_sum subst qenv body
  | DApp (t1, t2, _) ->
      check_abst_pair_sum (check_abst_pair_sum subst qenv t1) qenv t2
  | DPair (t1, t2, TyProd (q, _, _)) ->
      let s = check_abst_pair_sum subst qenv t1 in
      let s = check_abst_pair_sum s qenv t2 in
      let q1, q2 = subst_qual s (get_qual (get_type t1)), subst_qual s (get_qual (get_type t2)) in
      (match q1, q2 with
         NonLinear, _ | _, NonLinear -> fix_qual s q NonLinear
       | _ -> s)
  | DInjL (t, _) | DInjR (t, _) -> check_abst_pair_sum subst qenv t
  | _ -> subst

(* -----------------------------------------------------------------------------
 * final step
 *)
let subst_linear_q = function
    Linear -> Linear
  | NonLinear -> NonLinear
  | QVar _ -> Linear

let rec subst_linear_ty = function
    TyQBit -> TyQBit
  | TySingleton q -> TySingleton (subst_linear_q q)
  | TyFun (q, ty1, ty2) -> TyFun (subst_linear_q q, subst_linear_ty ty1, subst_linear_ty ty2)
  | TyProd (q, ty1, ty2) -> TyProd (subst_linear_q q, subst_linear_ty ty1, subst_linear_ty ty2)
  | TySum (q, ty1, ty2) -> TySum (subst_linear_q q, subst_linear_ty ty1, subst_linear_ty ty2)

let rec subst_linear_term = function
    DConst (c, ty) -> DConst (c, subst_linear_ty ty)
  | DVar (id, ty) -> DVar (id, subst_linear_ty ty)
  | DTuple0 ty -> DTuple0 (subst_linear_ty ty)
  | DAbst (id, t, ty) -> DAbst (id, subst_linear_term t, subst_linear_ty ty)
  | DApp (t1, t2, ty) -> DApp (subst_linear_term t1, subst_linear_term t2, subst_linear_ty ty)
  | DPair (t1, t2, ty) -> DPair (subst_linear_term t1, subst_linear_term t2, subst_linear_ty ty)
  | DLet (x, y, t1, t2, ty) -> DLet (x, y, subst_linear_term t1, subst_linear_term t2, subst_linear_ty ty)
  | DInjL (t, ty) -> DInjL (subst_linear_term t, subst_linear_ty ty)
  | DInjR (t, ty) -> DInjR (subst_linear_term t, subst_linear_ty ty)
  | DMatch (t1, (x, t2), (y, t3), ty) -> DMatch (subst_linear_term t1, (x, subst_linear_term t2), (y, subst_linear_term t3), subst_linear_ty ty)
  | DLetRec (f, t1, t2, ty) -> DLetRec (f, subst_linear_term t1, subst_linear_term t2, subst_linear_ty ty)


let bit_ty = TySum (Linear, TySingleton Linear, TySingleton Linear)
let new_ty = TyFun (Linear, bit_ty, TyQBit)
let meas_ty = TyFun (Linear, TyQBit, bit_ty)
let h_ty = TyFun (Linear, TyQBit, TyQBit)
let cnot_ty = TyFun (Linear, TyProd (Linear, TyQBit, TyQBit), TyProd (Linear, TyQBit, TyQBit))
let x_ty = TyFun (Linear, TyQBit, TyQBit)
let z_ty = TyFun (Linear, TyQBit, TyQBit)
let initial_qenv =
  List.fold [("new", new_ty); ("meas", meas_ty); ("H", h_ty); ("cnot", cnot_ty); ("X", x_ty); ("Z", z_ty)]
    ~init:Environment.empty
    ~f:(fun env (id, ty) -> Environment.extend env id ty)

let ty_dterm iterm =
  let s, rels, dterm = dterm_of_iterm initial_qenv iterm in
  let s = check_abst_pair_sum s Environment.empty dterm in
  let s = subtyping s rels in
  subst_linear_term (subst_qual_term s dterm)
