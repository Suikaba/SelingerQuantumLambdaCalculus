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
  | e=IfExpr { e }
  | e=MatchExpr { e }

LetExpr :
  | LET f=ID e=LetFunArgsAndBody IN e2=Expr { App (Abst (f, e2), e) }
  | LET LPAREN x=ID COMMA y=ID RPAREN EQ e1=Expr IN e2=Expr { Let (x, y, e1, e2) }
  | LET x=ID EQ e1=Expr IN e2=Expr { App (Abst (x, e2), e1) }
  | LET ASTER EQ e1=Expr IN e2=Expr { App (Abst (fresh_var (), e2), e1) }
  | LET REC f=ID x=ID e1=LetFunArgsAndBody IN e2=Expr { LetRec (f, x, e1, e2) }

LetFunArgsAndBody :
  | x=ID EQ e=Expr { Abst (x, e) }
  | x=ID e=LetFunArgsAndBody { Abst (x, e) }

FunExpr :
  | FUN e=FunArgsAndBody { e }
  | FUN ASTER RARROW e=Expr { Abst ("_z", e) }
  | FUN LPAREN x=ID COMMA y=ID RPAREN RARROW e=Expr { Abst ("_z", Let (x, y, Var "_z", e)) }
FunArgsAndBody :
  | x=ID RARROW e=Expr { Abst (x, e) }
  | x=ID e=FunArgsAndBody { Abst (x, e) }

IfExpr :
  | IF e1=Expr THEN e2=Expr ELSE e3=Expr { Match (e1, (fresh_var (), e2), (fresh_var (), e3)) }
  | e=TupleExpr { e }

TupleExpr :
  | e=AppExpr { e }
  | e1=TupleExpr COMMA e2=AppExpr { Pair (e1, e2) }

AppExpr :
  | e1=AppExpr e2=AExpr { App (e1, e2) }
  | e=AExpr { e }

AExpr :
    ZERO { InjR Tuple0 }
  | ONE { InjL Tuple0 }
  | ASTER { Tuple0 }
  | i=ID { Var i }
  | INJL LPAREN e=Expr RPAREN { InjL e }
  | INJR LPAREN e=Expr RPAREN { InjR e }
  | LPAREN e=Expr RPAREN { e }

MatchExpr :
  | MATCH e1=Expr WITH x=ID RARROW e2=Expr BAR y=ID RARROW e3=Expr { Match (e1, (x, e2), (y, e3)) }
