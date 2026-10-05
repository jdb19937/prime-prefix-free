import PPF.RH.ExplicitFormula
import PPF.Explicit.Analytic
import PPF.Explicit.Zeros
import PPF.Explicit.EF.Core

/-!
# Explicit bound: the truncated explicit formula under RH

Explicit version of E3 (`PPF.RH.EFA.explicit_formula_core` with explicit inputs):
`920 + log 2π + 12·1010032 + 8·100 + 2·224 ≤ 13·10^6`; `‖ζ′(0)/ζ(0)‖ = log 2π` by
Mathlib's `deriv_riemannZeta_zero` and `riemannZeta_zero`.
-/

namespace PPF.Explicit

open Complex PPF.RH

theorem explicit_formula_explicit (hRH : RiemannHypothesis) :
    ∀ y T : ℝ, 100 ≤ y → 2 ≤ T →
      ‖((Chebyshev.psi y : ℝ) : ℂ) - y
          + ∑ ρ ∈ zetaZeros T, (mult ρ : ℂ) * ((y : ℂ) ^ ρ / ρ)‖
        ≤ 13000000 * (y * Real.log (T * y) ^ 2 / T + Real.log (T * y) ^ 2) := by
  intro y T hy hT
  have hcore := EFx.explicit_formula_core_explicit hRH 100 1010032 224
    (left_line_explicit hRH) (good_height_explicit hRH) (by norm_num)
    (sum_mult_window_explicit hRH)
    (fun hy hc ht hedge => rectInt_logDeriv_zeta hRH hy hc ht hedge) y T hy hT
  have hK0 : ‖deriv riemannZeta 0 / riemannZeta 0‖ ≤ 2 := by
    rw [deriv_riemannZeta_zero, riemannZeta_zero]
    have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
    have heq : -Complex.log (2 * (Real.pi : ℂ)) / 2 / (-1 / 2) = ((Real.log (2 * Real.pi) : ℝ) : ℂ) := by
      rw [Complex.ofReal_log h2pi.le]
      push_cast
      ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs]
    have hlog0 : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
    rw [abs_of_nonneg hlog0]
    have hpi : Real.pi < 3.15 := Real.pi_lt_d2
    have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have hexp2 : 2 * Real.pi < Real.exp 2 := by
      have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      rw [this]
      nlinarith
    have := Real.log_lt_log h2pi hexp2
    rw [Real.log_exp] at this
    linarith
  have hnn : 0 ≤ y * Real.log (T * y) ^ 2 / T + Real.log (T * y) ^ 2 := by
    have hT0 : (0 : ℝ) < T := by linarith
    have hy0 : (0 : ℝ) < y := by linarith
    positivity
  calc _ ≤ _ := hcore
    _ ≤ 13000000 * (y * Real.log (T * y) ^ 2 / T + Real.log (T * y) ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ hnn
        linarith

end PPF.Explicit
