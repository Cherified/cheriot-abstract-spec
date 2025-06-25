.DEFAULT_GOAL := all
.PHONY: all clean force

all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: force
	$(COQBIN)rocq makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm Makefile.coq
