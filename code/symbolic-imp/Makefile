.PHONY: why3-extract symbolic-imp.zip VERSION

interp.native: why3-extract interp.ml
	ocamlbuild -pkg zarith -pkg dynlink -pkg str -pkg alt-ergo -I why3-extract $@

why3-extract: Makefile dict.mlw imp.drv imp.mlw
	rm -rf why3-extract
	mkdir why3-extract
	why3 extract --modular --recursive -L . \
    -o why3-extract \
    -D ocaml64 -D imp.drv \
		imp.ConcreteInterpreter \
		imp.SymbolicInterpreter

clean:
	rm -rf why3-extract
	ocamlbuild -clean

replay:
	why3 replay -L . imp

doc:
	why3 doc -L . imp.mlw

symbolic-imp.zip: VERSION
	rm -f $@
	zip $@ $(shell git ls-files .) VERSION

VERSION:
	echo -n git-commit: $(shell git rev-parse --short HEAD) > $@
