
{
	open Lexing
	open Parser

	exception Lexing_error of string
	
	exception EndOfFile
	
	let keywords = Hashtbl.create 10
	List.iter (fun x -> Hashtbl.add (k,t) -> Hashtbl.add keywords k t) [("else", ELSE);
																																			("false", BOOL false)
																																			(*TODO*)]
	
}

let new_line = '\n'

let digit = ['0'-'9']
let number = digit+
let letter = ['a'-'z' 'A'-'Z']
let ident = letter (letter | digit | '_')*

let character = [^  '"'] | '\\' | '\"' | '\n'

let chain = '"' character* '"'

rule token = parse
	|[' ' '\t']* {token lexbuf}
	|new_line {Lexing.new_line lexbuf; token lexbuf}
	
	|"//" {try line_comment lexbuf; token lexbuf
					with EndOfFile -> EOF}
	|"/*" {try comment lexbuf; token lexbuf
					with EndOfFile -> EOF}
					
	|ident as i {try Hashtbl.find keywords i with Not_found -> IDENT i)}
	
	|number as n {INTEGER (int_of_string n)}
	
	|eof {EOF}
	
	|_ as c {raise (Lexing_error ("Caractère interdit : "^(String.make 1 c)))}
					
and line_comment = parse
	|new_line {Lexing.new_line lexbuf}
	|eof {raise EndOfFile}
	|[^ '\n']* {line_comment lexbuf}	
	
and comment = parse
	|"*/" {()}
	|"/*" {comment lexbuf; comment lexbuf }
	|new_line {Lexing.new_line lexbuf; comment n lexbuf}
	|eof {raise (Lexing_error "Commentaire non fermé")}
	|_ {comment lexbuf}
					

