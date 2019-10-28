open OUnit2
open Core
open Qlambda
open Qlambda.Cui
open Qlambda.Syntax
open Qlambda.Decorated_typed

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

let const_test _ =
  let bit_ty = TySum (Linear, TySingleton Linear, TySingleton Linear) in

  let _, dt, _ = read_string_eval "new;;" initial_env initial_tyenv in
  assert_equal (get_type dt) (TyFun (Linear, bit_ty, TyQBit));
  let _, dt, _ = read_string_eval "meas;;" initial_env initial_tyenv in
  assert_equal (get_type dt) (TyFun (Linear, TyQBit, bit_ty));
  let _, dt, _ = read_string_eval "H;;" initial_env initial_tyenv in
  assert_equal (get_type dt) (TyFun (Linear, TyQBit, TyQBit));
  let _, dt, _ = read_string_eval "cnot;;" initial_env initial_tyenv in
  assert_equal (get_type dt) (TyFun (Linear, TyProd (Linear, TyQBit, TyQBit), TyProd (Linear, TyQBit, TyQBit)))

let aster_test _ =
  let _, dt, _ = read_string_eval "*;;" initial_env initial_tyenv in
  assert_equal (get_type dt) (TySingleton Linear)

let zero_one_test _ =
  let _, dt, _ = read_string_eval "0;;" initial_env initial_tyenv in
  assert_equal (get_type dt) (TySum (Linear, TySingleton Linear, TySingleton Linear));
  let _, dt, _ = read_string_eval "1;;" initial_env initial_tyenv in
  assert_equal (get_type dt) (TySum (Linear, TySingleton Linear, TySingleton Linear))

let suite =
  "suite">:::["const_test">:: const_test;
              "aster_test">:: aster_test;
              "zero_one_test">:: zero_one_test]

let () = run_test_tt_main suite
