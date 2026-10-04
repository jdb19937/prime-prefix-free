import PPF.RH.KZ.Bump

/-!
# K1: the polynomial weight `bump X` and its Mellin-type integrals

`bump X u = ((u − X/2)(4X − u)/X²)²` vanishes with its derivative at `X/2` and
`4X`, so two integrations by parts give
`∫_{X/2}^{4X} bump(u) u^{α+iτ} du = ∫ bump″(u) u^{α+2+iτ} du / ((α+1+iτ)(α+2+iτ))`
with `|bump″| ≤ 40/X²`; for small `|τ|` use the trivial bound.
-/

namespace PPF.RH

open Complex

theorem bump_nonneg (X u : ℝ) : 0 ≤ bump X u := by
  unfold bump
  positivity

theorem one_le_bump {X u : ℝ} (hX : 0 < X) (h1 : X ≤ u) (h2 : u ≤ 3 * X) :
    1 ≤ bump X u :=
  KZ.one_le_bump' hX h1 h2

/-- K1. -/
theorem norm_integral_bump_cpow_le (α : ℝ) (hα : -1 ≤ α) :
    ∃ C : ℝ, ∀ X : ℝ, 1 ≤ X → ∀ τ : ℝ,
      ‖∫ u in (X / 2)..(4 * X), ((bump X u : ℝ) : ℂ) * ((u : ℂ) ^ ((α : ℂ) + τ * I))‖
        ≤ C * X ^ (α + 1) / (1 + τ ^ 2) :=
  KZ.norm_integral_bump_cpow_le' α hα

end PPF.RH
