{
let reservedWords = [
  (* Keywords *)
  ("else", Parser.ELSE);
  ("if", Parser.IF);
  ("then", Parser.THEN);
  ("in", Parser.IN);
  ("let", Parser.LET);
  ("fun", Parser.FUN);
  ("rec", Parser.REC);
  ("match", Parser.MATCH);
  ("with", Parser.WITH);
  ("injl", Parser.INJL);
  ("injr", Parser.INJR);
]
}

rule main = parse
  (* ignore spacing and newline characters *)
  [' ' '\009' '\012' '\n']+     { main lexbuf }

| '0' { Parser.ZERO }
| '1' { Parser.ONE }
| '*' { Parser.ASTER }

| "(" { Parser.LPAREN }
| ")" { Parser.RPAREN }
| ";;" { Parser.SEMISEMI }
| "=" { Parser.EQ }
| "->" { Parser.RARROW }
| "," { Parser.COMMA }
| "|" { Parser.BAR }

| "(*" { comment lexbuf; main lexbuf }

| ['a'-'z' 'A'-'Z'] ['A'-'Z' 'a'-'z' '0'-'9' '_' '\'']*
    { let id = Lexing.lexeme lexbuf in
      try
        List.assoc id reservedWords
      with
      _ -> Parser.ID id
     }
| eof { exit 0 }

and comment = parse
| "(*" { comment lexbuf; comment lexbuf }
| "*)" { () }
| _ { comment lexbuf }
| eof { () }

