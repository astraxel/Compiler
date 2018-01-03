

type binop = Equal | Not_equal | Less | Greater | Less_or_equal
             | Greater_or_equal | And | Or |Plus | Minus | Times | Divide | Modulo | Affect
                                                                                                                             
type unop = Not | UMinus | Deref | SharedBorrow | MutBorrow

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
  |Evect of expr list
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
