(* pretty printer *)

open Ast

let print_binop b=
  print_string (match b with
                |Equal -> "=="
                |Not_equal -> "!="
                |Less -> "<"
                |Greater -> ">"
                |Less_or_equal -> "<="
                |Greater_or_equal -> ">="
                |And -> "&&"
                |Or -> "||"
                |Plus -> "+"
                |Minus -> "-"
                |Times -> "*"
                |Divide -> "/"
                |Modulo -> "%"
                |Affect -> "="
               )

let print_unop u=
  print_string (match u with
                |Not -> "!"
                |UMinus -> "-"
                |Deref -> "*"
                |SharedBorrow -> "& mut"
                |MutBorrow -> "&"
               )

let print_mut = function
  |false -> ()
  |true -> print_string "mut "

let rec print_typ = function
  |Tid t -> print_string t
  |Tcons (c,t) -> print_string "c < ";
                  print_typ t; print_string " >"
  |Tesp (m,t) -> print_string "& ";
                 print_mut m;
                 print_typ t

let print_arg a=
  let m,i,t=a in
  print_mut m;
  print_string i;
  print_string " : ";
  print_typ t

let rec print_expr_list = function
  |[] -> ()
  |[a] -> print_expr a
  |a::q -> print_expr a;
           print_string ", ";
           print_expr_list q
          
and print_expr e = match e.expr with
  |Eint n -> print_int n
  |Ebool b -> print_string (if b then "true" else "false")
  |Eident i -> print_string i
  |Ebinop (e1,b,e2) -> print_expr e1;
                       print_binop b;
                       print_expr e2
  |Eunop (u,e1) -> print_unop u;
                   print_expr e1
  |Eattribute (e1,i) -> print_expr e1;
                        print_string ".";
                        print_string i
  |Elen e1 -> print_expr e1;
              print_string ".len()"
  |Eselect (e1,e2) -> print_expr e1;
                      print_string "[";
                      print_expr e2;
                      print_string "]"
  |Ecall (i,l) -> print_string i;
                  print_string "(";
                  print_expr_list l;
                  print_string ")";
  |Evect l -> print_string "vect ! [";
              print_expr_list l;
              print_string "]"
  |Eprint s -> print_string "print ! (\"";
               print_string s;
               print_string "\")";
  |Ebloc b -> print_bloc b

and print_bloc b =
  print_string "{";
  begin
    match b with
    |Ubloc l -> print_stmt_list l
    |Vbloc (l,e) -> print_stmt_list l; print_expr e; print_string "\n"
  end;
  print_string "}\n"
                    

and print_stmt_list = function
  |[] -> ()
  |s::q -> print_stmt s; print_stmt_list q

and print_stmt s = match s with
  |Unit -> print_string ";\n"
  |Sexpr e -> print_expr e;
              print_string ";\n"
  |Saff (m,i,e) -> print_string "let ";
                   print_mut m;
                   print_string i;
                   print_string " = ";
                   print_expr e;
                   print_string ";\n"
  |Sobj (m,name,structure,attributes) -> print_string "let ";
                                         print_mut m;
                                         print_string name;
                                         print_string " = {";
                                         print_att_list attributes;
                                         print_string ";\n"
  |Swhile (e,b) -> print_string "while ";
                   print_expr e;
                   print_string "\n";
                   print_bloc b;
                   print_string "\n"
  |Sreturn a -> print_string "return ";
                begin
                  match a with
                  |Some e -> print_expr e
                  |None -> ()
                end;
                print_string ";\n"
  |Sif p -> print_if p

and print_att_list = function
  |[] -> print_string "}"
  |(i,e)::q -> print_string i;
              print_string " : ";
              print_expr e;
              if q <> [] then print_string ", ";
              print_att_list q

and print_if = function
  |Aif (e,b) -> print_string "if ";
                print_expr e;
                print_string "\n";
                print_bloc b
  |Bif (e,b1,b2) ->  print_string "if ";
                     print_expr e;
                     print_string "\n";
                     print_bloc b1;
                     print_string "\nelse";
                     print_bloc b2
  |Iif (e,b1,p) ->  print_string "if ";
                    print_expr e;
                    print_string "\n";
                    print_bloc b1;
                    print_string "\nelse";
                    print_if p

let rec print_att_dec = function
  |[] -> print_string "}"
  |(i,t)::q -> print_string i;
               print_string " : ";
               print_typ t;
               if q <> [] then print_string ", ";
               print_att_dec q
                              
let print_dec_struct (s:Ast.decl_struct) =
  print_string "struct ";
  print_string s.name;
  print_string "{";
  print_att_dec s.attributes;
  print_string "\n"

let rec print_args_list = function
  |[] -> print_string ")"
  |a::q -> print_arg a;
           if q <> [] then print_string ", ";
           print_args_list q
  
let print_dec_fun f=
  print_string "fn ";
  print_string f.name;
  print_string "(";
  print_args_list f.arguments;
  begin
    match f.typ with
    |None -> ()
    |Some t -> print_string " -> ";
               print_typ t
  end;
  print_string "\n";
  print_bloc f.body

let print_dec = function
  |Ddecl_fun f -> print_dec_fun f
  |Ddecl_struct s-> print_dec_struct s

let rec print_prog = function
  |[] -> ()
  |(d::q) -> print_dec d;
             print_prog q
             

(* Appels au parser et lexer *)

open Format
open Lexing
   

let parse_only = ref false
               

let parse source =
  let c = open_in source in
  let lb = Lexing.from_channel c in
  try
    let p = Parser.prog Lexer.token lb in
    close_in c;
    print_prog p;
    exit 0
  with
  |Lexer.Lexing_error s -> print_string "Lexing error : ";
                           print_string s;
                           print_string "\n";
                           exit 1
  |Parser.Error -> print_string "File \"";
                   print_string source;
                   print_string "\", line ";
                   print_int lb.lex_curr_p.pos_lnum;
                   print_string ", character ";
                   print_int (lb.lex_curr_p.pos_cnum -lb.lex_curr_p.pos_bol);
                   print_string ":\nsyntax error\n";
                   exit 1
  
  
             
let main () =
  Arg.parse
    ["--parse-only", Arg.Set parse_only, "Option for parsing only";
    ]
    parse  
    ""  
;;
  
main ()

       
