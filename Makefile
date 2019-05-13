COQARGS := $(shell cat "_CoqProject")

todo :
	@echo "TODOs:\n--------------------------------------------------------------------------------"
	@grep "TODO\|FIXME" -n *.v

machine : registers
	coqc $(COQARGS) Machine.v

registers : types
	coqc $(COQARGS) Registers.v

types : 
	coqc $(COQARGS) Types.v
