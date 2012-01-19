OCAMLMAKEFILE=OCamlMakefile

INCDIRS = cil/obj/x86_LINUX/ z3/ocaml
LIBDIRS = cil/obj/x86_LINUX/ /usr/lib/ocaml z3/ocaml z3/lib
SOURCES = cil/src/cil.mli config.ml config.mli error.ml error.mli  ident.ml ident.mli sil.ml sil.mli prop.ml prop.mli simp.ml simp.mli prover.ml prover.mli propset.ml propset.mli rankfinder.ml rankfinder.mli symExec.ml symExec.mli abs.ml abs.mli trans.ml trans.mli dotty.ml dotty.mli analysis.ml main.ml

LIBS = unix str nums cil z3 
RESULTDEPS = cil/obj/x86_LINUX/cil.cmxa  /
CLIBS=camlidl z3 z3stubs 

LDFLAGS= -fopenmp

RESULT = terminationanalyser

all: native-code

include $(OCAMLMAKEFILE)
