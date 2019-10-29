open Core
open Syntax
open Intuitionistic_typed
open Decorated_typed
open Eval

let string_of_qs qs =
  let rec inner n =
    if n = 0 then []
    else (Printf.sprintf "q%d" (n - 1)) :: inner (n - 1)
  in
  "|" ^ (String.concat ~sep:"," (inner qs)) ^ ">"

let binary_of_int i n =
  let rec inner j =
    (if i land (1 lsl j) <> 0 then "1" else "0")
    ^
    if j = 0 then "" else inner (j - 1)
  in inner (n - 1)

let print_results (states, qs, v) =
  Printf.printf "Results:\n Q =\n";
  List.iteri states ~f:(fun i a -> Printf.printf "  |%s> with %f\n" (binary_of_int i qs) a);
  Printf.printf " L = %s\n" (string_of_qs qs);
  Printf.printf " value = %s\n\n" (string_of_value v)

let read_eval_print env tyenv =
  print_string "# "; Out_channel.flush stdout;
  let t = Parser.toplevel Lexer.main (Lexing.from_channel In_channel.stdin) in

  (* simply typed *)
  let typed_t = ity_term tyenv t in
  Printf.printf "\nIntuitionistic typed term : \n %s\n\n" (string_of_iterm typed_t);

  (* decorated type *)
  let typed_t = ty_dterm typed_t in
  Printf.printf "Decorated typed term : \n %s\n\n" (string_of_dterm typed_t);

  (* evaluation *)
  let states, qs, v = eval_term env (Array.create ~len:0 0., 0, t) in
  print_results (Array.to_list states, qs, v)


(* for test *)
let read_string_eval str env tyenv =
  let t = Parser.toplevel Lexer.main (Lexing.from_string str) in
  let ityped_t = ity_term tyenv t in
  let dtyped_t = ty_dterm ityped_t in
  let qc = eval_term env (Array.create ~len:0 0., 0, t) in
  ityped_t, dtyped_t, qc

