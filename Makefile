GENRATED = ast.cmi parser.mli parser.ml lexer.ml

all: main clean

main : main.ml lexer.ml parser.ml
	ocamlopt -o main main.ml

ast.cmi: ast.mli
	ocamlc -c ast.mli

parser.mli parser.ml: parser.mly ast.cmi
	menhir --infer --explain parser.mly


lexer.ml: lexer.mll parser.mli
	ocamllex lexer.mll

.PHONY: clean mrproper

clean:
	rm -rf parser.mli parser.ml lexer.ml *.o *.cmi *.cmx

mrproper: clean 
	rm -rf main
