open Syntax
open Intuitionistic_typed
open Eval

let read_term_eval env tyenv t =
  Printf.printf "Input = %s\n\n" (string_of_term t);
  let typed_t = ity_term tyenv t in
  let v = eval_term env t in
  Printf.printf "Intuitionistic typed term : \n %s\n\n" (string_of_iterm typed_t);
  Printf.printf "value = %s\n\n" (string_of_value v)
