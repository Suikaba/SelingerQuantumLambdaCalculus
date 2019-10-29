open OUnit2
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

let entangle_easy _ =
  let _, _, (_, _, v) = read_string_eval (  "let (q1, q0) = (H (new 0), new 0) in\n"
                                           ^ "let (q1, q0) = cnot (q1, q0) in\n"
                                           ^ "(meas q1, meas q0);;")
                                           initial_env initial_tyenv in
  (match v with
     VPair (VInjR VTuple0, VInjR VTuple0) | VPair (VInjL VTuple0, VInjL VTuple0) -> ()
   | _ -> assert_equal true false)

let suite =
  "suite">:::["entangle_easy">:: entangle_easy;]

let () = run_test_tt_main suite
