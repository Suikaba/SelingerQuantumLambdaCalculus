open Core
open Qlambda
open Qlambda.Syntax
open Qlambda.Eval

let () =
  Random.self_init ();
  let coin = Abst ("z", App (Const Meas, App (Const H, (App (Const New, InjR Tuple0))))) in
  let res = eval_term Environment.empty coin in
  print_endline (string_of_value res);
  let use_coin = App (coin, InjR Tuple0) in
  let res = eval_term Environment.empty use_coin in
  print_endline (string_of_value res)
