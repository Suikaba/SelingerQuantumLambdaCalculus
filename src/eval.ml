open Core
open Syntax

exception ExpectedPair
exception ExpectedConstOrAbst
exception ApplyConstError
exception EvalMatchingError
exception NotImplemented

let apply_const c v = match c, v with
  | New, (VInjR VTuple0) -> Qbit (1.0, 0.0) (* injr * -> |0> *)
  | New, (VInjL VTuple0) -> Qbit (0.0, 1.0) (* injl * -> |1> *)
  | Meas, Qbit (alpha, beta) ->
      assert (Float.abs (1.0 -. alpha *. alpha -. beta *. beta) <=. 0.000000001);
      let r = Random.float 1.0 in
      if alpha *. alpha <=. r then VInjR (VTuple0)
      else                VInjL (VTuple0)
  | H, Qbit (a, b) ->
      let na = (a +. b) /. Float.sqrt (2.) in
      let nb = (a -. b) /. Float.sqrt (2.) in
      Qbit (na, nb)
  | X, _ | Y, _ | Z, _ -> raise NotImplemented
  | _ -> raise ApplyConstError

let rec eval_term env = function
    Const c -> VConst c
  | Var id -> Environment.lookup env id
  | Abst (id, t) -> VAbst (id, t, ref env)
  | App (t1, t2) ->
      let v1 = eval_term env t1 in
      let v2 = eval_term env t2 in
      (match v1 with
         VConst c -> apply_const c v2
       | VAbst (id, body, env) ->
           let env = Environment.extend !env id v2 in
           eval_term env body
       | _ -> raise ExpectedConstOrAbst)
  | Pair (t1, t2) -> VPair (eval_term env t1, eval_term env t2)
  | Tuple0 -> VTuple0
  | InjL t -> VInjL (eval_term env t)
  | InjR t -> VInjR (eval_term env t)
  | Match (t, (x, t2), (y, t3)) ->
      (match eval_term env t with
         VInjL v ->
           let env = Environment.extend env x v in
           eval_term env t2
       | VInjR v ->
           let env = Environment.extend env y v in
           eval_term env t3
       | _ -> raise EvalMatchingError)
  | Let (x, y, t1, t2) -> (* let <x, y> = M in N *)
      (match eval_term env t1 with
         VPair (v1, v2) ->
           let env = Environment.extend env x v1 in
           let env = Environment.extend env y v2 in
           eval_term env t2
       | _ -> raise ExpectedPair)
  | LetRec (id, para, t1, t2) ->
      let dummy = ref Environment.empty in
      let env = Environment.extend env id (VAbst (para, t1, dummy)) in
      dummy := env;
      eval_term env t2

