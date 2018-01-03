

%{
	open Ast
	exception Parsing_error of string

%}

/* Déclaration des tokens */
%token EOF LET MUT WHILE RETURN IF FN STRUCT ELSE
%token LCB RCB LPAR RPAR DOT ENDSTMT COMMA ARROW COLON LB RB
%token BORROW EM
%token PLUS MINUS DIV TIMES MODULO
%token OR AND
%token EQUAL SUPERIOR INFERIOR SUPERIOR_EQUAL INFERIOR_EQUAL DIFFERENT
%token AFFECT
%token <bool> BOOL
%token <int> INTEGER
%token <string> IDENT
%token <string> CHAIN

/* Priorités et associativités des tokens */


%left AFFECT
%left OR
%left AND
%nonassoc EQUAL SUPERIOR INFERIOR SUPERIOR_EQUAL INFERIOR_EQUAL DIFFERENT
%left PLUS MINUS 
%left TIMES DIV MODULO
%nonassoc UMINUS EM DEREF BORROW
%nonassoc LB
%nonassoc DOT

/* Point d'entrée de la grammaire */
%start prog 

/* Type des valeurs renvoyées par l'analyseur syntaxique */
%type <Ast.fichier> prog

%%

/* Règles de grammaire */

expr :   
  |MINUS; e=expr {Eunop (UMinus, e)} %prec UMINUS
  |EM; e=expr {Eunop (Not, e)}
  |TIMES; e=expr {Eunop (Deref,e)} %prec DEREF
  |BORROW; m=boption(MUT); e=expr {Eunop ((if m then MutBorrow else SharedBorrow), e)}
   
  |e1= expr; b=binop; e2=expr {Ebinop (e1,b,e2)}

  |LPAR; e=expr; RPAR {e}
  
	|e=expr; DOT; i=IDENT {Eattribute (e,i)}
  |e1= expr ; DOT ; i=IDENT; LPAR ; RPAR  {if i="len" then Elen (e1) else raise (Parsing_error "error")} /*
rajouter les erreurs en temps voulu */ 
  |e1= expr ; LB ; e2=expr ; RB {Eselect (e1, e2)} 
  |i= IDENT ; LPAR ; e=l_expr ; RPAR  {Ecall (i, e)}
  |b= bloc {Ebloc b}
  |i=IDENT ; EM ; LB ; e=l_expr ; RB {if i="vec" then Evect (e) else raise (Parsing_error "error")}
	|i=IDENT ; EM ; LPAR ; c=CHAIN ; RPAR {if i="print" then Eprint (c) else raise (Parsing_error "error")}
	
  |i= INTEGER {Eint i}
  |ident = IDENT {Eident ident}
  |b=BOOL {Ebool b}
  
	
%inline binop:
	|AFFECT {Affect}
	|OR {Or}
	|AND {And} 
	|INFERIOR_EQUAL {Less_or_equal} 
	|INFERIOR {Less} 
	|SUPERIOR_EQUAL {Greater_or_equal} 
	|SUPERIOR {Greater}
	|DIFFERENT {Not_equal} 
	|EQUAL {Equal}
	|PLUS {Plus}
	|MINUS {Minus}
	|TIMES {Times}
	|DIV {Divide}
	|MODULO {Modulo}	
	
l_expr:
  |e=expr; COMMA; l=l_expr {e::l}
  |e=expr									 {[e]}
  |                 			 {[]}



stmt:
	|ENDSTMT {Unit}
	|e=expr; ENDSTMT {Sexpr e}
	|LET; m=boption(MUT); ident=IDENT; AFFECT; e=expr; ENDSTMT {Saff (m,ident,e)} 
	|LET; m=boption(MUT); name=IDENT; AFFECT; structure=IDENT; LCB; l=affect_attributes; ENDSTMT {Sobj (m,name,structure,l)} 
	|WHILE; e=expr; b=bloc {Swhile (e,b)}
	|RETURN; r=return; ENDSTMT {Sreturn r}
	|i = rule_if {Sif i}



return:
	|e=expr {Some e}
	|				{None}

	
affect_attributes:
	|RCB {[]}
	|i=IDENT; COLON; e=expr; COMMA; v=affect_attributes {(i,e)::v}

	
rule_if:
	|IF; e=expr; b1=bloc; ELSE; b2=bloc {Bif (e,b1,b2)}
	|IF; e=expr; b=bloc {Aif (e,b)}
	|IF; e=expr; b=bloc;  ELSE; pif=rule_if {Iif (e,b,pif)}


bloc:
	|LCB; r=l_stmt {let l,t=r in match t with
												|None -> Ubloc l
												|Some e -> Vbloc (l,e)}


l_stmt:
	|s=stmt; r=l_stmt {let l,t=r in s::l,t}
	|RCB							{[], None}
	|e=expr; RCB 			{[], Some e}


typ:
	|i=IDENT; INFERIOR; t=typ; SUPERIOR {Tcons (i,t)}
	|BORROW; m=boption(MUT); t=typ {Tesp (m,t)}
	|i=IDENT {Tid i}


argument:
	|m=boption(MUT); i=IDENT; COLON; t=typ {(m,i,t)}


dec_fun:
	|FN; i=IDENT; LPAR; l=l_arg; RPAR; t=dec_typ; b=bloc {{name = i;
																												arguments = l;
																												body=b;
																												typ=t;}}

l_arg:
	|a=argument; COMMA; l=l_arg {a::l}
	|														{[]}


dec_typ:
	|LPAR; ARROW; t=typ; RPAR {Some t}
	|												  {None}


dec_struct:
	|STRUCT; i=IDENT; LCB; l=dec_attributes; RCB {{name=i;
																								 attributes = l;}}


dec_attributes:
	|i=IDENT; COLON; t=typ; COMMA; l=dec_attributes {(i,t)::l}
	|i=IDENT; COLON; t=typ                          {[(i,t)]}
	|																								{[]}

	
dec:
	|s = dec_struct {Ddecl_struct s}
	|f = dec_fun {Ddecl_fun f}

	
prog :
	|d = dec; p=prog {d::p}
	|EOF {[]}
