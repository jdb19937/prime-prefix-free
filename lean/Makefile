verify:
	lake build
	lake env lean AxiomCheck.lean
	lake env lean PPF/TreeTest.lean
	@echo "VERIFIED: build green; audited declarations depend only on propext, Classical.choice, Quot.sound; PrimePrefixFree matches OEIS A287117 on [1, 535]"

.PHONY: verify
