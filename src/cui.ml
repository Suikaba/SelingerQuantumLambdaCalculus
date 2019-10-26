open Syntax
open Intuitionistic_typed
open Decorated_typed
open Eval

let read_term_eval env tyenv t =
  Printf.printf "Input = %s\n\n" (string_of_term t);

  (* Simply typed *)
  let typed_t = ity_term tyenv t in
  Printf.printf "Intuitionistic typed term : \n %s\n\n" (string_of_iterm typed_t);

  (* decorate qualifier *)
  let typed_t = ty_dterm typed_t in
  Printf.printf "Decorated typed term : \n %s\n\n" (string_of_dterm typed_t);

  let v = eval_term env t in
  Printf.printf "value = %s\n\n" (string_of_value v)
