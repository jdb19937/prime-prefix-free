import PPF.Interfaces

/-!
# Phase 5 definitions

* `zetaZeros T`: the zeros of `ζ` in the open critical strip with `|Im ρ| ≤ T`
  (a `Finset` once finiteness is known; see `PPF.RH.zetaZeros_finite`).
* `mult ρ`: the multiplicity `analyticOrderNatAt riemannZeta ρ`.
* `bump X u`: the polynomial weight `((u − X/2)(4X − u)/X²)²`, which vanishes to
  second order at `u = X/2` and `u = 4X` and is `≥ 1` on `[X, 3X]`.
-/

namespace PPF.RH

open Complex

/-- The zero set of `ζ` in `0 < Re < 1`, `|Im| ≤ T`. -/
def zeroSet (T : ℝ) : Set ℂ :=
  {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T ∧ riemannZeta ρ = 0}

open Classical in
/-- `zeroSet T` as a `Finset` (empty if it were infinite; it is finite). -/
noncomputable def zetaZeros (T : ℝ) : Finset ℂ :=
  if h : (zeroSet T).Finite then h.toFinset else ∅

/-- Multiplicity of a zero of `ζ`. -/
noncomputable abbrev mult (ρ : ℂ) : ℕ := analyticOrderNatAt riemannZeta ρ

/-- Smooth (polynomial) majorant of `1_{[X, 3X]}` supported on `[X/2, 4X]`. -/
noncomputable def bump (X u : ℝ) : ℝ := ((u - X / 2) * (4 * X - u) / X ^ 2) ^ 2

end PPF.RH
