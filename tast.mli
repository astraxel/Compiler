open Ast
           
type tident = ident * int
            
type mut = bool

type ttyp = 
   Tbool | Tint | Tunit | Tstruct of ident | Tvec of ttyp | Tref of mut*ttyp

 
type tdecl =
   | TDdecl_fun of tdecl_fun
   | TDdecl_struct of tdecl_struct

and tstmt =
   | TSUnit
   | TSexpr of texpr
   | TSaff of mut * tident * texpr (* pas sur de moi *)
   | TSobj of mut * tident * ident * (ident*texpr) list (*pas sur de moi *)
   | TSwhile of texpr * tbloc 
   | TSreturn of texpr option
   | TSif of tpif (* pif = if, mais c'est réservé *)
   
and tpif =
   |TAif of texpr * tbloc (* if expr then bloc *)
   |TBif of texpr * tbloc * tbloc (* if expr then bloc else bloc *)
   |TIif of texpr * tbloc * tpif (* if expr then bloc else pif *)

and texpr = utexpr * ttyp (*utexpr = untyped expression*)

and utexpr =
   |TEint of int
   |TEbool of bool
   |TEident of tident
   |TEbinop of texpr * binop * texpr
   |TEunop of unop * texpr
   |TEattribute of texpr * ident (* pas sur de moi*)
   |TElen of texpr
   |TEselect of texpr * texpr
   |TEcall of ident * texpr list
   |TEvect of texpr list  (* pas sur de moi *)
   |TEprint of string
   |TEbloc of tbloc

and tbloc =
   |TUbloc of tstmt list
   |TVbloc of tstmt list * texpr

and targument = mut * tident * ttyp

and tfichier =  tdecl list

and tdecl_struct = {
   name : ident ;
   attributes : (ident*ttyp) list;
}

and tdecl_fun = {
   name : ident ;
   arguments : targument list ;
   body : tbloc ;
   typ : ttyp;
}
