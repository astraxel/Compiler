

%{
	open Ast

%}

/* Déclaration des tokens */

%token EOF PLUS MINUS DIV TIMES MODULO
%token LPAR RPAR
%token EQUAL DIFFERENT SUPERIOR SUPERIOR_EQUAL INFERIOR INFERIOR_EQUAL AMPERSAND_AMPERSAND OR_LOGICAL
%token TRUE FALSE
%token <int> INTEGER
%token <string> IDENT
%token DOT

/* Priorités et associativités des tokens */

%left OR
%left AND
%nonassoc EQUAL_EQUAL DIFFERENT SUPERIOR SUPERIOR_EQUAL INFERIOR INFERIOR_EQUAL
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
  |Ebool = FALSE {Ebool false}
  |Ebool = TRUE  {Ebool true}
  |e1=expr , DOT , i=ident {Eattribute (e1,i)} 
  |MINUS, e=expr {Eunop (Minus, e)} %prec UMINUS 
  |e1= expr , OR , e2= expr {Ebinop (e1,Or,e2)}
  |e1= expr , AND , e2= expr {Ebinop (e1,And,e2)}
  |e1= expr , INFERIOR_EQUAL , e2= expr {Ebinop (e1,Less_or_equal,e2)}
  |e1= expr , INFERIOR , e2= expr {Ebinop (e1,Less,e2)}
  |e1= expr , SUPERIOR_EQUAL , e2= expr {Ebinop (e1,Greater_or_equal,e2)}
  |e1= expr , SUPERIOR , e2= expr {Ebinop (e1,Greater,e2)}
  |e1= expr , DIFFERENT , e2= expr {Ebinop (e1,Not_equal,e2)}
  |e1= expr , EQUAL_EQUAL , e2= expr {Ebinop (e1,Equal,e2)}
  |e1= expr , PLUS , e2= expr {Ebinop (e1,Plus,e2)}
  |e1= expr , MINUS , e2= expr {Ebinop (e1, Minus,e2)}
  |e1= expr , TIMES , e2= expr {Ebinop (e1, Times,e2)}
  |e1= expr , DIV , e2= expr {Ebinop (e1, Divide,e2)}
  |e1= expr , MODULO , e2= expr {Ebinop (e1, Modulo,e2)}
  |LPAR , e=expr, RPAR {e} ;

prog :
	EOF {[]}
