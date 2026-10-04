import PPF.RH.GoodHeights
import PPF.RH.Residue
import PPF.RH.ExplicitFormula.Core

/-!
# E3: the truncated explicit formula for `ψ` under RH, error `O(y log²(Ty)/T + log²(Ty))`

Assembly, with `c = 1 + 1/log y` and `t ∈ [T, T+1]` from D4 (proof in
`PPF.RH.ExplicitFormula.Core`):
* right edge: `Carmichael.EF.integral_right_edge` (χ = trivial character mod 1,
  `DirichletCharacter.LFunction_modOne_eq`) and `perronSum_sub_psiChi_le`;
* RT for the rectangle `[−1/2, c] × [−t, t]`;
* left edge `Re = −1/2`: D3 gives `≪ log²(T+2)`;
* horizontal edges: D4 gives `≪ y log²(T+4)/T`;
* zeros with `T < |Im ρ| ≤ t`: `sum_mult_window_le`, each `|y^ρ/ρ| ≤ √y/T`;
* the constant `ζ′/ζ(0)`.
-/

namespace PPF.RH

open Complex

/-- E3. -/
theorem explicit_formula_RH (hRH : RiemannHypothesis) :
    ∃ C : ℝ, ∀ y T : ℝ, 100 ≤ y → 2 ≤ T →
      ‖((Chebyshev.psi y : ℝ) : ℂ) - y
          + ∑ ρ ∈ zetaZeros T, (mult ρ : ℂ) * ((y : ℂ) ^ ρ / ρ)‖
        ≤ C * (y * Real.log (T * y) ^ 2 / T + Real.log (T * y) ^ 2) :=
  EFA.explicit_formula_core hRH (left_line_bound hRH) (exists_good_height_zeta hRH)
    (fun hy hc ht hedge => rectInt_logDeriv_zeta hRH hy hc ht hedge)

end PPF.RH
