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
R :=-R $(ROOT)/coq-ext-lib/theories ExtLib \
    -R $(ROOT)/mirror-shard/src MirrorShard \
    -R $(ROOT)/src Bedrock

.PHONY: coq clean

coq: Makefile.coq
	COQC='time coqc' $(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile $(R) $(VS) \
          | sed -re 's/-R ([^ ]+) ExtLib/-I \1 -as ExtLib/g' \
          | sed -re 's/-R ([^ ]+) MirrorShard/-I \1 -as MirrorShard/g' \
	  > Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend
