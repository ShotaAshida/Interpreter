%{
open Syntax
%}

%token LPAREN RPAREN SEMISEMI
%token PLUS MULT LT MINUS
%token IF THEN ELSE TRUE FALSE
%token LET IN EQ
%token RARROW FUN
%token REC
%token AND OR

%token <int> INTV
%token <Syntax.id> ID

%start toplevel
%type <Syntax.program> toplevel
%%

toplevel :
    e=Expr SEMISEMI { Exp e }
  | LET x=ID EQ e=Expr SEMISEMI { Decl (x, e) }
  | LET x=ID EQ e1=Expr e2 = LetLetExpr SEMISEMI { DeclDecl (x, e1, e2) }
  | LET REC x=ID EQ FUN n=ID RARROW e=Expr SEMISEMI { RecDecl (x, n, e) }
  | LET REC x=ID n=ID EQ e=Expr SEMISEMI { RecDecl (x, n, e) }
  
LetLetExpr :
    LET x = ID EQ e = Expr { Decl (x, e) }
  | LET x = ID EQ e1 = Expr e2 = LetLetExpr { DeclDecl (x, e1, e2) }

Expr :
    e=IfExpr { e }
  | e=LetRecExpr { e }
  | e=LetExpr { e }
  | e=ORExpr { e }
  | e=FunExpr { e }

ORExpr :
    l=ORExpr OR r=ANDExpr {BinOp (Or, l, r)}
  | e=ANDExpr {e}

ANDExpr :
    l=ANDExpr AND r=LTExpr {BinOp (And, l, r)}
  | e=LTExpr {e}


LTExpr :
    l=PExpr LT r=PExpr { BinOp (Lt, l, r) }
  | l=PExpr EQ r=PExpr { BinOp (Equal, l, r)}
  | e=PExpr { e }

PExpr :
    l=PExpr PLUS r=MExpr { BinOp (Plus, l, r) }
  | l=PExpr MINUS r=MExpr {BinOp (Minus, l, r)}
  | e=MExpr { e }

MExpr :
    e1=MExpr MULT e2=AppExpr { BinOp (Mult, e1, e2) }
  | e=AppExpr { e }

 AppExpr :
    e1=AppExpr e2=AExpr { AppExp (e1, e2) }
  | e=AExpr { e }

AExpr :
    i=INTV { ILit i }
  | TRUE   { BLit true }
  | FALSE  { BLit false }
  | i=ID   { Var i }
  | LPAREN e=Expr RPAREN { e }

IfExpr :
    IF c=Expr THEN t=Expr ELSE e=Expr { IfExp (c, t, e) }

LetExpr :
    LET x=ID EQ e1=Expr IN e2=Expr { LetExp (x, e1, e2) }

FunExpr :
    FUN x = ID RARROW e = Expr { FunExp (x, e) }

LetRecExpr :
    LET REC x=ID EQ FUN n=ID RARROW e1=Expr IN e2=Expr { LetRecExp (x, n, e1, e2) }
