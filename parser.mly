

%{
	open Ast
	exception Parsing_error of string

%}

/* Déclaration des tokens */
%token EOF LET MUT WHILE RETURN IF FN STRUCT ELSE
%token LCB RCB LPAR RPAR DOT ENDSTMT AMPERSAND COMMA ARROWFIRST COLON EM LB RB
%token PLUS MINUS DIV TIMES MODULO
%token EQUAL SUPERIOR OR INFERIOR
%token <bool> BOOL
%token <int> INTEGER
%token <string> IDENT
%token <string> CHAIN

/* Priorités et associativités des tokens */


%nonassoc ERROR
%left EQUAL
%left OR
%left AND
%nonassoc EQUAL_EQUAL DIFFERENT SUPERIOR SUPERIOR_EQUAL INFERIOR INFERIOR_EQUAL
%left PLUS MINUS 
%left TIMES DIV MODULO
%nonassoc UMINUS AMPERSAND EM UTIMES
%nonassoc ELEMENT
%nonassoc DOT

/* Point d'entrée de la grammaire */
%start prog 

/* Type des valeurs renvoyées par l'analyseur syntaxique */
%type <Ast.fichier> prog

%%

/* Règles de grammaire */

expr :
  |e1=expr ; DOT ; i=IDENT {Eattribute (e1,i)} 
  |MINUS; e=expr {Eunop (Minus, e)} %prec UMINUS 
  |e1= expr; EQUAL; e2=expr {Ebinop (e1,Equal,e2)}
  |e1= expr ; OR; OR; e2= expr {Ebinop (e1,Or,e2)}
  |e1= expr ; AMPERSAND; AMPERSAND; e2= expr {Ebinop (e1,And,e2)} %prec AND
  |e1= expr ; INFERIOR; EQUAL ; e2= expr {Ebinop (e1,Less_or_equal,e2)} %prec INFERIOR_EQUAL
  |e1= expr ; INFERIOR ; e2= expr {Ebinop (e1,Less,e2)}
  |e1= expr ; SUPERIOR; EQUAL ; e2= expr {Ebinop (e1,Greater_or_equal,e2)} %prec SUPERIOR_EQUAL
  |e1= expr ; SUPERIOR ; e2= expr {Ebinop (e1,Greater,e2)}
  |e1= expr ; EM; EQUAL ; e2= expr {Ebinop (e1,Not_equal,e2)} %prec DIFFERENT
  |e1= expr ; EQUAL; EQUAL ; e2= expr {Ebinop (e1,Equal,e2)} %prec EQUAL_EQUAL
  |e1= expr ; PLUS ; e2= expr {Ebinop (e1,Plus,e2)}
  |e1= expr ; MINUS ; e2= expr {Ebinop (e1, Minus,e2)}
  |e1= expr ; TIMES ; e2= expr {Ebinop (e1, Times,e2)}
  |e1= expr ; DIV ; e2= expr {Ebinop (e1, Divide,e2)}
  |e1= expr ; MODULO ; e2= expr {Ebinop (e1, Modulo,e2)}
  |LPAR; e=expr; RPAR {e}
  
  |e1= expr ; DOT ; i=IDENT; LPAR ; RPAR  {if i="len" then Elen (e1) else raise (Parsing_error "error")} /*
rajouter les erreurs en temps voulu */
	|e1=expr; DOT; i=IDENT {Eattribute (e,i)}
  |e1= expr ; LB ; e2=expr ; RB {Eselect (e1, e2)}
  |i= IDENT ; LPAR ; e=l_expr ; RPAR  {Ecall (i, e)}
  |b= bloc {Ebloc b}
  |i=IDENT ; EM ; LB ; e=l_expr ; RB {if i="vec" then Evect (e) else raise (Parsing_error "error")}
	|i=IDENT ; EM ; LPAR ; c=CHAIN ; RPAR {if i="print" then Eprint (c) else raise (Parsing_error "error")}
	
  |i= INTEGER {Eint i}
  |ident = IDENT {Eident ident}
  |b=BOOL {Ebool b}
  
	|s = stmt {raise (Parsing_error "Expected an expression, not a statement. Maybe you forgot {}")} %prec ERROR
	|d= dec {raise (Parsing_error "Cannot declare a function or a structure within a declaration.")} %prec ERROR
	| {raise (Parsing_error "expected an expression")}
	
l_expr:
  |e=expr; COMMA; l=l_expr {e::l}
  |e=expr									 {[e]}
  |                 			 {[]}



stmt:
	|ENDSTMT {Unit}
	|e=expr; ENDSTMT {Sexpr e}
	|LET; m=boption(MUT); ident=IDENT; EQUAL; e=expr; ENDSTMT {Saff (m,ident,e)}
	|LET; m=boption(MUT); name=IDENT; EQUAL; structure=IDENT; LCB; l=affect_attributes; ENDSTMT {Sobj (m,name,structure,l)}
	|WHILE; e=expr; b=bloc {Swhile (e,b)}
	|RETURN; r=return; ENDSTMT {Sreturn r}
	|i = rule_if {Sif i}
	|d= dec {raise (Parsing_error "Cannot declare a function or a structure within a declaration.")} %prec ERROR
	| {raise (Parsing_error "expected a statement")}



return:
	|e=expr {Some e}
	|				{None}

	
affect_attributes:
	|RCB {[]}
	|i=IDENT; COLON; e=expr; COMMA; v=affect_attributes {(i,e)::v}
	| {raise (Parsing_error "} missing after structure attributes assignement")}

	
rule_if:
	|IF; e=expr; b1=bloc; ELSE; b2=bloc {Bif (e,b1,b2)}
	|IF; e=expr; b=bloc {Aif (e,b)}
	|IF; e=expr; b=bloc;  ELSE; pif=rule_if {Iif (e,b,pif)}
	|d= dec {raise (Parsing_error "Cannot declare a function or a structure within a declaration.")} %prec ERROR
	| {raise (Parsing_error "expected a string")}


bloc:
	|LCB; r=l_stmt {let l,t=r in match t with
												|None -> Ubloc l
												|Some e -> Vbloc (l,e)}
	|d= dec {raise (Parsing_error "Cannot declare a function or a structure within a declaration.")} %prec ERROR
	| {raise (Parsing_error "expected a bloc")} %prec ERROR


l_stmt:
	|s=stmt; r=l_stmt {let l,t=r in s::l,t}
	|RCB							{[], None}
	|e=expr; RCB 			{[], Some e}


typ:
	|i=IDENT; INFERIOR; t=typ; SUPERIOR {Tcons (i,t)}
	|AMPERSAND; m=boption(MUT); t=typ {Tesp (m,t)}
	|i=IDENT {Tid i}


argument:
	|m=boption(MUT); i=IDENT; COLON; t=typ {(m,i,t)}


dec_fun:
	|FN; i=IDENT; LPAR; l=l_arg; RPAR; t=dec_typ; b=bloc {{name = i;
																												arguments = l;
																												body=b;
																												typ=t;}}
	| {raise (Parsing_error "expected a declaration")}

l_arg:
	|a=argument; COMMA; l=l_arg {a::l}
	|														{[]}


dec_typ:
	|LPAR; ARROWFIRST; SUPERIOR; t=typ; RPAR {Some t}
	|																				{None}


dec_struct:
	|STRUCT; i=IDENT; LCB; l=dec_attributes; RCB {{name=i;
																								 attributes = l;}}
	| {raise (Parsing_error "expected a declaration")}


dec_attributes:
	|i=IDENT; COLON; t=typ; COMMA; l=dec_attributes {(i,t)::l}
	|																								{[]}

	
dec:
	|s = dec_struct {Ddecl_struct s}
	|f = dec_fun {Ddecl_fun f}
	| {raise (Parsing_error "expected a declaration")}

	
prog :
	|d = dec; p=prog {d::p}
	|EOF {[]}
