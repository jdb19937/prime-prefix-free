verify:
	lake build
	lake env lean AxiomCheck.lean
	lake env lean PPF/TreeTest.lean
	lake env lean --run scripts/ReplayClosure.lean
	@echo "VERIFIED: build green; audited declarations depend only on propext, Classical.choice, Quot.sound; PrimePrefixFree matches OEIS A287117 on [1, 535]; kernel replay of the main theorem's closure passed"

.PHONY: verify
