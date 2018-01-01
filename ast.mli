type binop = Equal | Not_equal | Less | Greater | Less_or_equal | Greater_or_equal | And | Or |Plus | Minus | Times | Divide | Modulo
                                                                                                                             
type unop = Not | Minus

type ident = string

type mut = bool

type typ =
  |Tid of ident
  |Tcons of ident*typ
  |Tesp of mut * typ
         
type argument = mut * ident * typ

                    
type expr =
  |Eint of int
  |Ebool of bool
  |Eident of ident
  |Ebinop of expr * binop * expr
  |Eunop of unop * expr
  |Eattribute of expr * ident
  |Elen of expr
  |Eselect of expr * expr
  |Ecall of ident * expr list
  |Evect of expr array
  |Eprint of string
  |Ebloc of bloc

 and bloc =
   |Ubloc of stmt list
   |Vbloc of stmt list * expr
                   

 and stmt =
   |Unit
   |Sexpr of expr
   |Saff of mut * ident * expr
   |Sobj of mut * ident * ident * (ident*expr) list
   |Swhile of expr * bloc
   |Sreturn of expr option
   |Sif of pif (*pif = if, mais c'est réservé*)

 and pif =
   |Aif of expr*bloc (* if expr then bloc *)
   |Bif of expr*bloc*bloc (* if expr then bloc else bloc *)
   |Iif of expr*bloc*pif (* if expr then bloc else pif *)

type decl_struct = {
    name : ident;
    attributes : (ident*typ) list;}

type decl_fun = {
  name    : ident;
  arguments : argument list;
  body    : bloc;
  typ : typ option}                     

type decl =
   |Ddecl_fun of decl_fun
   |Ddecl_struct of decl_struct

type fichier = decl list

(* deuxieme partie de L'AST *)

type tident = ident * int 

and typ = 
   Tbool | Tint | Tunit | Tstruct | Tvec of typ * list | Tborrow
(*  J ai remplacé i32 par int,
 * je sais pas quoi faire et où utiliser Tstruct 
 * Je ne sais pas comment définir T borrow 
 *)
 
and tdecl =
   | TDdecl_fun of tdecl_fun
   | TDdecl_struct of tdecl_struct

and tstmt =
   | TUnit of unit
   | TSexpr of texpr
   | TSaff of tborrow * ident * texpr (* pas sur de moi *)
   | TSobj of tborrow * ident * (ident*texpr) list (*pas sur de moi *)
   | TSwhile of texpr * tbloc 
   | TSreturn of texpr option
   | TSif of tpif (* pif = if, mais c'est réservé *)
   
and tpif =
   |TAif of texpr * tbloc (* if expr then bloc *)
   |TBif of texpr * tbloc * tbloc (* if expr then bloc else bloc *)
   |TIif of texpr * tbloc * tpif (* if expr then bloc else pif *)

and texpr =
   |TEint of int
   |TEbool of bool
   |TEident of tident
   |TEbinop of texpr * binop * texpr
   |TEunop of unop * texpr
   |TEattribute of texpr * ident (* pas sur de moi*)
   |TElen of texpr
   |TEselect of texpr * texpr
   |TEcall of tident * texpr list
   |TEvect of tvec   (* pas sur de moi *)
   |TEprint of string
   |TEbloc of tbloc

and tbloc =
   |TUbloc of tstmt list
   |TVbloc of tstmt list * texpr

and targument = tborrow * ident * typ

and ttype = 
   |TTid of ident * typ (* pas sur de moi *)
   |TTcons of ident * typ
   |TTesp of mut * typ
   |typ

and tfichier =  tdecl list

and tdecl_struct = {
   name : ident ;
   attributes : (tident*typ) list;
}

and tdecl_fun = {
   name : ident ;
   arguments : targument list ;
   body : tbloc ;
   typ : typ option
}
