# KNOWNTARGETS will not be passed along to CoqMakefile
KNOWNTARGETS := CoqMakefile
# KNOWNFILES will not get implicit targets from the final rule, and so depending on them won’t invoke the submake
# Warning: These files get declared as PHONY, so any targets depending on them always get rebuilt
KNOWNFILES := Makefile _CoqProject
# COQLIBS?=-I . -R /nix/store/rzg5hi5mvca56c85jqzc0h0l29axqy2s-coq8.15-alea/lib/coq/8.15/user-contrib/ALEA/ ALEA
.DEFAULT_GOAL := invoke-coqmakefile

CoqMakefile: Makefile _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o CoqMakefile

invoke-coqmakefile: CoqMakefile
	$(MAKE) --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: invoke-coqmakefile $(KNOWNFILES)

# This should be the last rule, to handle any targets not declared above
%: invoke-coqmakefile
	@true
