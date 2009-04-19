check: parse.cmo exprparse.cmo
	./check

%.cmo: %.ml
	ocamlc -c $<

clean:
	rm -f *.cmo *.cmi
