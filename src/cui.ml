open Core
open Syntax
open Intuitionistic_typed
open Decorated_typed
open Eval

let read_eval_print env tyenv =
  print_string "# "; Out_channel.flush stdout;
  let t = Parser.toplevel Lexer.main (Lexing.from_channel In_channel.stdin) in

  (* simply typed *)
  let typed_t = ity_term tyenv t in
  Printf.printf "\nIntuitionistic typed term : \n %s\n\n" (string_of_iterm typed_t);

  (* decorated type *)
  let typed_t = ty_dterm typed_t in
  Printf.printf "\nDecorated typed term : \n %s\n\n" (string_of_dterm typed_t);

  (* evaluation *)
  let v = eval_term env t in
  Printf.printf "\nvalue = %s\n\n" (string_of_value v)
