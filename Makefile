all: main
	mv main.byte prustc

main: main.ml
	ocamlbuild -use-menhir main.byte
