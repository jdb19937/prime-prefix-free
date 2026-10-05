import PPF.Explicit.Recurrence
import PPF.Explicit.Final

/-!
# Explicit bound: assembly

Assuming RH, `∑_{n ∈ A287117} 1/n ≤ F_72 ≈ 5·10^14`.
-/

namespace PPF.Explicit

theorem tsum_le_of_RH (hRH : RiemannHypothesis) :
    ∑' n : ℕ, (if PPF.PrimePrefixFree n then (1 : ℝ) / n else 0) ≤ (Nat.fib 72 : ℝ) :=
  tsum_le_of_partial_sum_r _ (partial_sum_r_le (rec_explicit hRH))

end PPF.Explicit
