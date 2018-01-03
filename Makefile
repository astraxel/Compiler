CMO=lexer.cmo parser.cmo main.cmo
GENERATED = lexer.ml parser.ml parser.mli
FLAGS=-annot -g

all: main
	./main "test.rs"

main: $(CMO)
	ocamlc $(FLAGS) -o main nums.cma $(CMO)

lexer.cmo: lexer.ml
	ocamlc $(FLAGS) -c lexer.ml

parser.cmo: parser.ml
	ocamlc $(FLAGS) -c parser.ml

main.cmo: main.ml
	ocamlc $(FLAGS) -c main.ml


lexer.ml: lexer.mll parser.cmi
	ocamllex lexer.mll


parser.mli parser.ml: parser.mly ast.cmi
	menhir -v --infer parser.mly


ast.cmi : ast.mli
	ocamlc $(FLAGS) -c ast.mli

parser.cmi : parser.mli
	ocamlc $(FLAGS) -c parser.mli


clean:
	rm -f *.cm[io] *.o *.annot *~  $(GENERATED)
	rm -f parser.output parser.automaton

