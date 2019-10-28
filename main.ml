open Core
open Qlambda
open Qlambda.Cui
open Qlambda.Syntax

let bit_ty = ITySum (ITySingleton, ITySingleton)
let new_ty = ITyFun (bit_ty, ITyQbit)
let meas_ty = ITyFun (ITyQbit, bit_ty)
let h_ty = ITyFun (ITyQbit, ITyQbit)
let cnot_ty = ITyFun (ITyProd (ITyQbit, ITyQbit), ITyProd (ITyQbit, ITyQbit))

let initial_env =
  List.fold [("new", New); ("meas", Meas); ("H", H); ("cnot", CNOT)] ~init:Environment.empty
    ~f:(fun env (id, c) -> Environment.extend env id (VConst c))
let initial_tyenv =
  List.fold [("new", new_ty); ("meas", meas_ty); ("H", h_ty); ("cnot", cnot_ty)] ~init:Environment.empty
    ~f:(fun env (id, ty) -> Environment.extend env id ty)


let () =
  Random.self_init ();
  read_eval_print initial_env initial_tyenv
