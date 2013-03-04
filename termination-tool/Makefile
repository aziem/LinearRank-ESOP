OCAMLBUILD = ocamlbuild
BUILDFLAGS = -use-ocamlfind -package cil
BUILDTYPE = native

MAIN = analysis.$(BUILDTYPE)

all : $(MAIN)

$(MAIN) :
	$(OCAMLBUILD) $(BUILDFLAGS) $@

clean :
	$(OCAMLBUILD) -clean
