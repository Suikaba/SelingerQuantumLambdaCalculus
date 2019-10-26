open Core
open Qlambda
open Qlambda.Cui
open Qlambda.Syntax

let initial_env = Environment.empty
let initial_tyenv = Environment.empty

let () =
  Random.self_init ();
  let coin = Abst ("z", App (Const Meas, App (Const H, (App (Const New, InjR Tuple0))))) in
  read_term_eval initial_env initial_tyenv coin;
  let use_coin = App (coin, InjR Tuple0) in
  read_term_eval initial_env initial_tyenv use_coin;
  let test = Abst ("x", App (Const Meas, Var "x")) in
  read_term_eval initial_env initial_tyenv test;

  let t = Abst ("x", Pair (Var "x", Var "x")) in
  read_term_eval initial_env initial_tyenv t;

  let f = Abst ("f", App (Var "f", InjR Tuple0)) in
  let f2 = Abst ("z", App (Const Meas, Var "q")) in
  let t = Abst ("q", App (f, f2)) in
  read_term_eval initial_env initial_tyenv t;
