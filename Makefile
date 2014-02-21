#MODULES := Rules Cache Channel Compatible DataTypes Hier L1 LatestValue MsiState StoreAtomicity Tree Useful Top L1Axioms LatestValueAxioms ChannelAxiom ChannelAxiomHelp CompatBehavior ChannelAxiomHelp HierProperties BehaviorAxioms BaseTree Case
#VS      := $(MODULES:%=%.v)

IGNORE:=

VS:=$(wildcard *.v)
VS:=$(filter-out $(IGNORE:%=%.v),$(VS))

.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
