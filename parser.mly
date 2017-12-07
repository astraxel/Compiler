

%{
	open Ast
	exception Parsing_error of string

%}

/* Déclaration des tokens */
%token EOF LET MUT WHILE RETURN IF FN STRUCT
%token LCB RCB LPAR RPAR DOT ENDSTMT AMPERSAND COMMA ARROW COLON
%token PLUS MINUS DIV TIMES MODULO
%token EQUAL DIFFERENT SUPERIOR OR
%token <bool> BOOL
%token <int> INTEGER
%token <string> IDENT

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
  |b=BOOL {Ebool b}
  |e1=expr , DOT , i=ident {Eattribute (e1,i)} 
  |MINUS, e=expr {Eunop (Minus, e)} %prec UMINUS 
  |e1= expr , OR , e2= expr {Ebinop (e1,Or,e2)}
  |e1= expr , AND , e2= expr {Ebinop (e1,And,e2)}
  |e1= expr , INFERIOR, EQUAL , e2= expr {Ebinop (e1,Less_or_equal,e2)}
  |e1= expr , INFERIOR , e2= expr {Ebinop (e1,Less,e2)}
  |e1= expr , SUPERIOR, EQUAL , e2= expr {Ebinop (e1,Greater_or_equal,e2)}
  |e1= expr , SUPERIOR , e2= expr {Ebinop (e1,Greater,e2)}
  |e1= expr , DIFFERENT , e2= expr {Ebinop (e1,Not_equal,e2)}
  |e1= expr , AMPERSAND, AMPERSAND , e2= expr {Ebinop (e1,Equal,e2)}
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


return:
	|e=expr {Some e}
	|				{None}
;
	
affect_attributes:
	|RCB {[]}
	|ident=i, COLON, e=expr, COMMA, v=affect_attributes {(i,e)::v}
;
	
rule_if:
	|IF,e=expr,b1=bloc,b2=bloc {Bif (e,b1,b2}
	|IF,e=expr,b=bloc {Aif (e,b)}
	|IF,e=expr,b=bloc,pif=rule_if {Iif (e,b,pif}
;

bloc:
	|LCB, l=l_stmt, RCB {Ubloc l}
	|LCB, l=l_stmt, e=expr, RCB {Vbloc (l,e)}
;

l_stmt:
	|s=stmt, l=l_stmt {s::l}
	|									{[]}
;

typ:
	|i=IDENT, INFERIOR, t=typ, SUPERIOR {Tcons (i,t)}
	|AMPERSAND, m=boption(MUT), t=typ {Tesp (b,t)}
	|i=IDENT {Tid i}
;

argument:
	|boption(MUT), i=IDENT, COLON, t=typ {(b,i,t)}
;

decl_fun:
	|FN, i=IDENT, LPAR, l=l_arg, RPAR, t=dec_typ, b=bloc {{name = i;
																												arguments = l;
																												body=b;
																												typ=t;}}
;

l_arg:
	|a=argument, COMMA, l=l_arg {a::l}
	|														{[]}
;

dec_typ:
	|LPAR, ARROW, t=typ, RPAR {Some t}
	|													{None}
;

dec_struct:
	|STRUCT, i=IDENT, LCB, l=dec_attributes, RCB {{name=i;
																								 attributes = l;}}
;

dec_attributes:
	|i=IDENT, COLON, t=typ, COMMA, l=dec_attributes {(i,t)::l}
	|																								{[]}
;
	
dec:
	|s = dec_struct {s}
	|f = dec_fun {f}
;
	
prog :
	|d = dec, p=prog {d::p}
	|EOF {[]}
