

%{
	open Ast

%}

/* Déclaration des tokens */

%token EOF PLUS MINUS DIV TIMES LPAR RPAR MODULO
%token <int> INTEGER
%token <string> IDENT


/* Priorités et associativités des tokens */

%left PLUS MINUS 
%left TIMES DIV MODULO
%nonassoc UMINUS

/* Point d'entrée de la grammaire */
%start prog 

/* Type des valeurs renvoyées par l'analyseur syntaxique */
%type <Ast.fichier> prog

%%

/* Règles de grammaire */

expr :
  |i= INTEGER {Eint i}
  |ident = IDENT {Eident ident}
  |MINUS; e=expr %prec UMINUS {Eunop (Minus, e)}
  |e1= expr ; PLUS ; e2= expr {Ebinop (e1,Plus,e2)}
  |e1= expr ; MINUS ; e2= expr {Ebinop (e1, Minus,e2)}
  |e1= expr ; TIMES ; e2= expr {Ebinop (e1, Times,e2)}
  |e1= expr ; DIV ; e2= expr {Ebinop (e1, Div,e2)}
  |e1= expr ; MODULO ; e2= expr {Ebinop (e1, Modulo,e2)}
  |LPAR; e=expr; RPAR {e}

prog :
	EOF {[]}
