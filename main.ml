open Core
open Qlambda
open Qlambda.Cui
open Qlambda.Syntax

let bit_ty = ITySum (ITySingleton, ITySingleton)
let new_ty = ITyFun (bit_ty, ITyQbit)
let meas_ty = ITyFun (ITyQbit, bit_ty)
let h_ty = ITyFun (ITyQbit, ITyQbit)

let initial_env = Environment.extend (Environment.extend (Environment.extend Environment.empty "new" (VConst New)) "meas" (VConst Meas)) "H" (VConst H)
let initial_tyenv = Environment.extend (Environment.extend (Environment.extend Environment.empty "new" new_ty) "meas" meas_ty) "H" h_ty

let () =
  Random.self_init ();
  read_eval_print initial_env initial_tyenv
