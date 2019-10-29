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

let duplicate_qbit _ =
  try
    let _ = read_string_eval "let f q = (q, q) in let q = new 0 in f q;;" initial_env initial_tyenv in
    assert_equal true false
  with _ -> ()

let duplicate_top _ =
  let top = TySingleton Linear in
  let dup_top = TySingleton NonLinear in
  let _, dt, _ = read_string_eval "let f x = (x, x) in f;;" initial_env initial_tyenv in
  assert_equal (get_type dt) (TyFun (Linear, dup_top, TyProd (Linear, top, top)))

let duplicate_abst_with_free_qubit _ =
  let exp = "let q = new 0 in let f = fun * -> q in (f, f);;" in
  try
    let _, _, _ = read_string_eval exp initial_env initial_tyenv in
    assert_equal true false
  with   CannotFixQual -> ()
       | _ -> assert_equal true false

let coin _ =
  let bit_ty = TySum (Linear, TySingleton Linear, TySingleton Linear) in
  let exp = "fun * -> meas (H (new 0));;" in
  let _, dt, _ = read_string_eval exp initial_env initial_tyenv in
  assert_equal (get_type dt) (TyFun (Linear, TySingleton Linear, bit_ty))

let suite =
  "suite">:::["duplicate_qbit">:: duplicate_qbit;
              "duplicate_top">:: duplicate_top;
              "duplicate_abst_with_free_qubit">:: duplicate_abst_with_free_qubit;
              "coin">:: coin;]

let () = run_test_tt_main suite
