%{
open Syntax
%}

%token LPAREN RPAREN SEMISEMI
%token IF THEN ELSE
%token LET EQ IN REC
%token FUN RARROW
%token COMMA
%token BAR
%token MATCH WITH
%token INJL INJR
%token ASTER
%token ZERO ONE

%token <Syntax.id> ID

%start toplevel
%type <Syntax.term> toplevel
%%

toplevel :
  | e=Expr SEMISEMI { e }

Expr :
  | e=LetExpr { e }
  | e=FunExpr { e }
  | e=AppExpr { e }

LetExpr :
  | LET LPAREN x=ID COMMA y=ID RPAREN EQ e1=Expr IN e2=Expr { Let (x, y, e1, e2) }

FunExpr :
  | FUN x=ID RARROW e=Expr { Abst (x, e) }

AppExpr :
    e1=AppExpr e2=AExpr { App (e1, e2) }
  | e=AExpr { e }

AExpr :
    ZERO { InjR Tuple0 }
  | ONE { InjL Tuple0 }
  | ASTER { Tuple0 }
  | i=ID { Var i }
  | INJL LPAREN e=Expr RPAREN { InjL e }
  | INJR LPAREN e=Expr RPAREN { InjR e }
  | LPAREN e=Expr RPAREN { e }
