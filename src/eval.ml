open Core
open Syntax

type vector = float Array.t
type quantumClosure = vector * int * term (* quantum closure has L as length but not list *)

exception ExpectedPair
exception ExpectedConstOrAbst
exception ApplyConstError
exception EvalMatchingError
exception NotImplemented


let extend_states states alpha beta =
  if Array.length states = 0 then
    Array.of_list [alpha; beta]
  else
    let fst = Array.map states ~f:(fun x -> x *. alpha) in
    let snd = Array.map states ~f:(fun x -> x *. beta) in
    Array.append fst snd

let apply_const c (states, qs, v) = match c, v with
  | New, (VInjR VTuple0) ->
      let states = extend_states states 1.0 0.0 in
      (states, qs + 1, Qbit qs)
  | New, (VInjL VTuple0) ->
      let states = extend_states states 0.0 1.0 in
      (states, qs + 1, Qbit qs)
  | Meas, Qbit i ->
      let alpha =
        Array.foldi ~init:0. states
          ~f:(fun idx a b ->
                if idx land (1 lsl i) = 0 then a +. b
                else a) in
      let r = Random.float 1. in
      if alpha *. alpha <=. r then begin
        let states =
          Array.mapi states
            ~f:(fun idx a ->
                  if idx land (1 lsl i) = 0 then a /. alpha
                  else 0.)
        in
        states, qs, VInjR VTuple0
      end else begin
        let beta = 1. -. alpha in
        let states =
          Array.mapi states
            ~f:(fun idx a ->
                  if idx land (1 lsl i) = 0 then a /. beta
                  else 0.)
        in
        states, qs, VInjL VTuple0
      end
  | H, Qbit i ->
      let states =
        Array.mapi states
          ~f:(fun idx a ->
                let idx' = idx lxor (1 lsl i) in
                if idx land (1 lsl i) = 0 then
                  let b = Array.get states idx' in
                  (a +. b) /. Float.sqrt(2.)
                else
                  let b = Array.get states idx' in
                  (b -. a) /. Float.sqrt(2.))
      in states, qs, Qbit i
  | CNOT, VPair (Qbit q0, Qbit q1) ->
      let states =
        Array.mapi states
          ~f:(fun idx a ->
                if idx land (1 lsl q0) <> 0 then Array.get states (idx lxor (1 lsl q1))
                else a)
      in
      states, qs, VPair (Qbit q0, Qbit q1)
  | _ -> raise ApplyConstError

let rec eval_term env (states, qs, term) = match term with
    Const _ -> raise NotImplemented
  | Var id -> (states, qs, Environment.lookup env id)
  | Tuple0 -> (states, qs, VTuple0)
  | Abst (x, t) -> states, qs, VAbst (x, t, ref env)
  | App (t1, t2) ->
      let states, qs, v2 = eval_term env (states, qs, t2) in
      let states, qs, v1 = eval_term env (states, qs, t1) in
      (match v1 with
         VConst c -> apply_const c (states, qs, v2)
       | VAbst (x, body, env) ->
           let env = Environment.extend !env x v2 in
           eval_term env (states, qs, body)
       | _ -> raise ExpectedConstOrAbst)
  | Pair (t1, t2) ->
      let states, qs, v2 = eval_term env (states, qs, t2) in
      let states, qs, v1 = eval_term env (states, qs, t1) in
      states, qs, VPair (v1, v2)
  | Let (x, y, t1, t2) ->
      let states, qs, v1 = eval_term env (states, qs, t1) in
      (match v1 with
         VPair (vp1, vp2) ->
           let env = Environment.extend (Environment.extend env x vp1) y vp2 in
           eval_term env (states, qs, t2)
       | _ -> raise ExpectedPair)
  | InjL t ->
      let states, qs, v = eval_term env (states, qs, t) in
      states, qs, VInjL v
  | InjR t ->
      let states, qs, v = eval_term env (states, qs, t) in
      states, qs, VInjR v
  | Match (t1, (x, t2), (y, t3)) ->
      let states, qs, v1 = eval_term env (states, qs, t1) in
      (match v1 with
         VInjL v ->
           let env = Environment.extend env x v in
           eval_term env (states, qs, t2)
       | VInjR v ->
           let env = Environment.extend env y v in
           eval_term env (states, qs, t3)
       | _ -> raise EvalMatchingError)
  | LetRec (f, t1, t2) ->
      let dummy = ref Environment.empty in
      (match t1 with
         Abst (x, body) ->
           let env = Environment.extend env f (VAbst (x, body, dummy)) in
           dummy := env;
           eval_term env (states, qs, t2)
       | _ -> failwith "Fatal error")
