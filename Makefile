check: parse.cmo
	./check

parse.cmo:
	ocamlc -c parse.ml
