import PPF.Conditional
import PPF.Sieve
import PPF.Selberg
import PPF.Explicit.Main

/-!
# Main theorem

Assuming the Riemann Hypothesis, the reciprocals of OEIS A287117 have a finite sum,
and that sum is at most `Nat.fib 72 ≈ 5·10^14`.

This file holds the complete statement: apart from Mathlib (`RiemannHypothesis`,
`Nat.Prime`, `HasSum`, `Nat.fib`) it uses only the definition below.
-/

/-- OEIS A287117: no proper binary prefix `⌊n / 2^k⌋` (`k ≥ 1`) of `n` is an odd prime. -/
def PrimePrefixFree (n : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ¬ ((n / 2 ^ k).Prime ∧ n / 2 ^ k ≠ 2)

open Classical in
theorem ppf_hasSum_of_RH (hRH : RiemannHypothesis) :
    ∃ s : ℝ, HasSum (fun n : ℕ => if PrimePrefixFree n then (1 : ℝ) / n else 0) s ∧
      s ≤ Nat.fib 72 := by
  have hs : Summable (fun n : ℕ => if PrimePrefixFree n then (1 : ℝ) / n else 0) :=
    (PPF.summable_of_inputs (PPF.selbergMeanSquare_of_RH hRH) PPF.pairSieve).congr
      fun _ => if_congr Iff.rfl rfl rfl
  refine ⟨_, hs.hasSum, ?_⟩
  convert PPF.Explicit.tsum_le_of_RH hRH using 4
  exact Iff.rfl
