import Mathlib

/-!
# Statement-level definitions

* `PrimePrefixFree`: OEIS A287117, the integers with no odd prime among their
  proper binary prefixes `⌊n / 2^k⌋`, `k ≥ 1`.
* `SelbergMeanSquare`: primes in almost all short intervals, in the weak form
  consumed by the proof (window lengths `h ∈ [X^θ, √X]` for each fixed `θ > 0`).
  Selberg (1943) proved the stronger statement for all `1 ≤ h ≤ X` under RH.
* `PairSieve`: the upper-bound sieve for prime pairs `n, a n + t` in an
  arbitrary interval, uniform in the coefficients.
-/

namespace PPF

open Finset

/-- OEIS A287117: no proper binary prefix `⌊n / 2^k⌋` (`k ≥ 1`) of `n` is an odd prime. -/
def PrimePrefixFree (n : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ¬ ((n / 2 ^ k).Prime ∧ n / 2 ^ k ≠ 2)

/-- Mean square of `θ(n + h) − θ(n) − h` over `n ∈ [X, 2X)`, for windows
`X^θ ≤ h ≤ √X`. -/
def SelbergMeanSquare : Prop :=
  ∀ θ : ℝ, 0 < θ → ∃ C : ℝ, ∀ X h : ℕ, 2 ≤ X → (X : ℝ) ^ θ ≤ h → h ^ 2 ≤ X →
    ∑ n ∈ Finset.Ico X (2 * X),
      (Chebyshev.theta ((n + h : ℕ) : ℝ) - Chebyshev.theta n - h) ^ 2
      ≤ C * h * X * Real.log X ^ 2

/-- Upper-bound sieve for prime pairs `n, a n + t` in `[Y, Y + H)`. -/
def PairSieve : Prop :=
  ∃ C : ℝ, ∀ Y H a t : ℕ, 2 ≤ H → 1 ≤ a → 1 ≤ t → Nat.Coprime a t →
    (#((Finset.Ico Y (Y + H)).filter (fun n => n.Prime ∧ (a * n + t).Prime)) : ℝ)
      ≤ C * ((a * t : ℕ) / (Nat.totient (a * t) : ℝ)) ^ 2 * H / Real.log H ^ 2

end PPF
