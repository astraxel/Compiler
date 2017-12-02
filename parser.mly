

%{
	open Ast

%}

/* Déclaration des tokens */
%token EOF ENDSTMT LET MUT COLON WHILE RETURN IF
%token LCB RCB LPAR RPAR
%token PLUS MINUS DIV TIMES MODULO  
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
  |MINUS, e=expr {Eunop (Minus, e)} %prec UMINUS 
  |e1= expr , PLUS , e2= expr {Ebinop (e1,Plus,e2)}
  |e1= expr , MINUS , e2= expr {Ebinop (e1, Minus,e2)}
  |e1= expr , TIMES , e2= expr {Ebinop (e1, Times,e2)}
  |e1= expr , DIV , e2= expr {Ebinop (e1, Divide,e2)}
  |e1= expr , MODULO , e2= expr {Ebinop (e1, Modulo,e2)}
  |LPAR, e=expr, RPAR {e}
  ;

stmt:
	|ENDSTMT {()}
	|e=expr, ENDSTMT {Sexpr e}
	|LET, m=boption(MUT), ident=IDENT, EQUAL, e=expr, ENDSTMT {Saff (m,ident,e}
	|LET, m=boption(MUT), name=IDENT, EQUAL, structure=IDENT, LCB, l=affect_attributes, ENDSTMT {Sobj (m,name,structure,l)}
	|WHILE, e=expr, b=bloc {Swhile (e,b)}
	|RETURN, r=return_value, ENDSTMT {Sreturn r}
	|{rule_if}
	;
	
rule_if:
	|IF,e=expr,b1=bloc,b2=bloc {Bif (e,b1,b2}
	|IF,e=expr,b=bloc {Aif (e,b)}
	|IF,e=expr,b=bloc,pif=rule_if {Iif (e,b,pif}
	;

return:
	|e=expr {Some e}
	|				{None}
	
affect_attributes:
	|RCB {[]}
	|ident=i, COLON, e=expr, v=affect_attributes {(i,e)::v}
	;
	
	
prog :
	EOF {[]}
