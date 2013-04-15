ROOT    := ..
MODULES := TimeAbstract \
	   Conditional Lambda \
           AutoSepExt PreAutoSep \
           Wrap \
           AutoSep \
           LemmaTests \
           Baby TrivialMem TrivialMem2 Arr \
           ConditionalTest LambdaTest \
           Indir Factorial Swap \
           Pair SinglyLinkedList \
           Malloc \
           Sets ListSet TreeSet \
           Bags Queue
#           Memoize
#StreamParse ArrayQuery StreamParseTest ArrayQueryTest TrivialArray 
VS      := $(MODULES:%=%.v)

.PHONY: coq clean

coq: Makefile.coq
	COQC='time coqc' $(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile -R $(ROOT)/src Bedrock \
		     $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend
