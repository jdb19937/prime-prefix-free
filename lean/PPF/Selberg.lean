import PPF.RH.Ledger

/-!
# Primes in almost all short intervals under RH

Selberg's mean-square bound, in the weak form `SelbergMeanSquare`. The proof is
the Phase 5 ledger (`PPF/RH/Ledger.lean`).
-/

namespace PPF

theorem selbergMeanSquare_of_RH (hRH : RiemannHypothesis) : SelbergMeanSquare :=
  RH.selbergMeanSquare_assembly hRH

end PPF
