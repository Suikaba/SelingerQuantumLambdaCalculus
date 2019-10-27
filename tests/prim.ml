open OUnit2
open Qlambda
open Qlambda.Cui
open Qlambda.Syntax
open Qlambda.Decorated_typed

let bit_ty = ITySum (ITySingleton, ITySingleton)
let new_ty = ITyFun (bit_ty, ITyQbit)
let meas_ty = ITyFun (ITyQbit, bit_ty)
let h_ty = ITyFun (ITyQbit, ITyQbit)

let initial_env = Environment.extend (Environment.extend (Environment.extend Environment.empty "new" (VConst New)) "meas" (VConst Meas)) "H" (VConst H)
let initial_tyenv = Environment.extend (Environment.extend (Environment.extend Environment.empty "new" new_ty) "meas" meas_ty) "H" h_ty

let const_test _ =
  let bit_ty = TySum (Linear, TySingleton Linear, TySingleton Linear) in

  let _, dt, _ = read_string_eval "new;;" initial_env initial_tyenv in
  assert_equal (get_type dt) (TyFun (Linear, bit_ty, TyQBit));
  let _, dt, _ = read_string_eval "meas;;" initial_env initial_tyenv in
  assert_equal (get_type dt) (TyFun (Linear, TyQBit, bit_ty));
  let _, dt, _ = read_string_eval "H;;" initial_env initial_tyenv in
  assert_equal (get_type dt) (TyFun (Linear, TyQBit, TyQBit))

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
