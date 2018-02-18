all: Makefile.coq
	$(MAKE) -f $<

clean:
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq clean; fi

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@
