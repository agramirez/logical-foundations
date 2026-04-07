all: Makefile.coq
	$(MAKE) -f Makefile.coq
	./encrypt_exercises.sh

Makefile.coq: _CoqProject
	rocq makefile -f _CoqProject -o Makefile.coq

clean:
	if [ -f Makefile.coq ]; then $(MAKE) -f Makefile.coq clean; fi
	rm -f Makefile.coq
