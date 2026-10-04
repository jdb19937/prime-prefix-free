import PPF.Conditional
import PPF.Sieve
import PPF.Selberg

/-!
# Main theorem

Assuming the Riemann Hypothesis, the reciprocals of OEIS A287117 have a finite sum.

This file holds the complete statement: apart from Mathlib (`RiemannHypothesis`,
`Nat.Prime`, `Summable`) it uses only the definition below.
-/

/-- OEIS A287117: no proper binary prefix `⌊n / 2^k⌋` (`k ≥ 1`) of `n` is an odd prime. -/
def PrimePrefixFree (n : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ¬ ((n / 2 ^ k).Prime ∧ n / 2 ^ k ≠ 2)

open Classical in
theorem ppf_summable_of_RH (hRH : RiemannHypothesis) :
    Summable (fun n : ℕ => if PrimePrefixFree n then (1 : ℝ) / n else 0) :=
  (PPF.summable_of_inputs (PPF.selbergMeanSquare_of_RH hRH) PPF.pairSieve).congr
    fun _ => if_congr Iff.rfl rfl rfl
