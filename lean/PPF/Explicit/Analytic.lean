import PPF.RH.Reflection
import PPF.RH.GoodHeights

/-!
# Explicit bound: ζ′/ζ estimates with explicit constants

Explicit versions of D2 (`PPF.RH.norm_logDeriv_zeta_reflect_le`, constant
`26 + log 2π + π ≤ 32`), D3 (`PPF.RH.left_line_bound`; the `|t| < 2` range, proved
there by compactness, is replaced by reflection along `Re w = 3/2`, where
`|tan(πw/2)| = 1` and the digamma function is bounded), and D4
(`PPF.RH.exists_good_height_zeta`, constant `1010000 + 32`).
-/

namespace PPF.Explicit

open Complex
open scoped Real

namespace An

/-- On `Re z = 3π/4`, `cos z ≠ 0` and `‖sin z‖ = ‖cos z‖`. -/
lemma sin_cos_three_quarter (y : ℝ) :
    cos (((3 * π / 4 : ℝ) : ℂ) + (y : ℂ) * I) ≠ 0 ∧
    ‖sin (((3 * π / 4 : ℝ) : ℂ) + (y : ℂ) * I)‖ = ‖cos (((3 * π / 4 : ℝ) : ℂ) + (y : ℂ) * I)‖ := by
  have hx : (3 * π / 4 : ℝ) = π - π / 4 := by ring
  have hs : Real.sin (3 * π / 4) = √2 / 2 := by rw [hx, Real.sin_pi_sub, Real.sin_pi_div_four]
  have hc : Real.cos (3 * π / 4) = -(√2 / 2) := by rw [hx, Real.cos_pi_sub, Real.cos_pi_div_four]
  have h2 : (√2 / 2) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have esin : sin (((3 * π / 4 : ℝ) : ℂ) + (y : ℂ) * I)
      = ((Real.sin (3 * π / 4) * Real.cosh y : ℝ) : ℂ)
        + ((Real.cos (3 * π / 4) * Real.sinh y : ℝ) : ℂ) * I := by
    rw [sin_add_mul_I]; push_cast; ring
  have ecos : cos (((3 * π / 4 : ℝ) : ℂ) + (y : ℂ) * I)
      = ((Real.cos (3 * π / 4) * Real.cosh y : ℝ) : ℂ)
        + ((-(Real.sin (3 * π / 4) * Real.sinh y) : ℝ) : ℂ) * I := by
    rw [cos_add_mul_I]; push_cast; ring
  have hch : 1 ≤ Real.cosh y := Real.one_le_cosh y
  rw [esin, ecos, norm_add_mul_I, norm_add_mul_I, hs, hc]
  refine ⟨?_, ?_⟩
  · intro h0
    have := congrArg (fun z => ‖z‖) h0
    simp only [norm_zero] at this
    rw [norm_add_mul_I, Real.sqrt_eq_zero (by positivity)] at this
    have e1 : (-(√2 / 2) * Real.cosh y) ^ 2 = 1 / 2 * Real.cosh y ^ 2 := by
      rw [mul_pow, neg_sq, h2]
    have e2 : (-(√2 / 2 * Real.sinh y)) ^ 2 = 1 / 2 * Real.sinh y ^ 2 := by
      rw [neg_sq, mul_pow, h2]
    rw [e1, e2] at this
    nlinarith [sq_nonneg (Real.sinh y)]
  · congr 1
    ring_nf

lemma log_two_pi_le : Real.log (2 * π) ≤ 2 := by
  rw [Real.log_le_iff_le_exp (by positivity)]
  have he := Real.exp_one_gt_d9
  have hpi := Real.pi_lt_d2
  have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  nlinarith

lemma norm_log_two_pi : ‖Complex.log (2 * π)‖ = Real.log (2 * π) := by
  have h : (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
  rw [h, ← Complex.ofReal_log (by positivity), Complex.norm_real, Real.norm_of_nonneg]
  exact Real.log_nonneg (by nlinarith [Real.pi_gt_three])

/-- D1 with its explicit constant `26`. -/
lemma digamma_le_26 (w : ℂ) (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 2) (h3 : 1 ≤ |w.im|) :
    ‖Complex.digamma w‖ ≤ 26 * Real.log (|w.im| + 2) := by
  have hw : 0 < w.re := by linarith
  have hb : ‖Complex.digamma w‖ ≤ 25 + Real.log (|w.im| + 1) := by
    refine le_of_tendsto (PPF.RH.Dg.tendsto_digamma hw).norm ?_
    filter_upwards [Filter.eventually_ge_atTop ⌈|w.im| + 1⌉₊] with n hn
    exact PPF.RH.Dg.partial_bound h1 h2 h3 (Nat.ceil_le.mp hn)
  have hlog3 : 1 ≤ Real.log (|w.im| + 2) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  have hmono : Real.log (|w.im| + 1) ≤ Real.log (|w.im| + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  linarith

/-- Partial-sum bound for `ψ` on `1 ≤ Re w ≤ 2`, any height (`A = |Im w| + 2`). -/
lemma partial_bound_right {w : ℂ} (h1 : 1 ≤ w.re) (h2 : w.re ≤ 2)
    {n : ℕ} (hn : |w.im| + 2 ≤ n) :
    ‖(Real.log n : ℂ) - ∑ j ∈ Finset.range (n + 1), 1 / (w + j)‖
      ≤ 25 + Real.log (|w.im| + 2) := by
  set A : ℝ := |w.im| + 2 with hA
  have him0 : 0 ≤ |w.im| := abs_nonneg _
  have hA2 : 2 ≤ A := by linarith
  have hnpos : (0 : ℝ) < n := by linarith
  set R : ℝ := ∑ j ∈ Finset.range (n + 1), 1 / ((j : ℝ) + A) with hR
  have hterm : ∀ j : ℕ, ‖1 / (((j : ℝ) + A : ℝ) : ℂ) - 1 / (w + j)‖ ≤ 12 * A / ((j : ℝ) + A) ^ 2 := by
    intro j
    have hjA : (0 : ℝ) < (j : ℝ) + A := by positivity
    have hwj : w + (j : ℂ) ≠ 0 := by
      intro h
      have := congrArg re h
      simp at this
      linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    have hlow : ((j : ℝ) + A) / 4 ≤ ‖w + (j : ℂ)‖ := by
      have hre : (j : ℝ) + w.re ≤ ‖w + (j : ℂ)‖ := by
        have := Complex.abs_re_le_norm (w + (j : ℂ))
        simp only [add_re, natCast_re] at this
        rw [abs_of_nonneg (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])] at this
        linarith
      have him : |w.im| ≤ ‖w + (j : ℂ)‖ := by
        have := Complex.abs_im_le_norm (w + (j : ℂ))
        simpa using this
      linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    have hnum : ‖w - (((j : ℝ) + A : ℝ) : ℂ) + (j : ℂ)‖ ≤ 3 * A := by
      have : w - (((j : ℝ) + A : ℝ) : ℂ) + (j : ℂ) = w - (A : ℂ) := by push_cast; ring
      rw [this]
      calc ‖w - (A : ℂ)‖ ≤ ‖w‖ + ‖(A : ℂ)‖ := norm_sub_le _ _
        _ ≤ (|w.re| + |w.im|) + A := by
            gcongr
            · exact Complex.norm_le_abs_re_add_abs_im w
            · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        _ ≤ 3 * A := by rw [abs_of_nonneg (by linarith)]; linarith
    have hc : (((j : ℝ) + A : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hjA.ne'
    rw [div_sub_div _ _ hc hwj, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hjA, one_mul, mul_one]
    have : w + (j : ℂ) - (((j : ℝ) + A : ℝ) : ℂ) = w - (((j : ℝ) + A : ℝ) : ℂ) + (j : ℂ) := by ring
    rw [this]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc ‖w - (((j : ℝ) + A : ℝ) : ℂ) + (j : ℂ)‖ * ((j : ℝ) + A) ^ 2
        ≤ (3 * A) * ((j : ℝ) + A) ^ 2 := by gcongr
      _ = 12 * A * (((j : ℝ) + A) * (((j : ℝ) + A) / 4)) := by ring
      _ ≤ 12 * A * (((j : ℝ) + A) * ‖w + (j : ℂ)‖) := by gcongr
  have hsq : ∀ j : ℕ, 1 / ((j : ℝ) + A) ^ 2
      ≤ 1 / ((j : ℝ) + A - 1) - 1 / (((j + 1 : ℕ) : ℝ) + A - 1) := by
    intro j
    have h0 : (0 : ℝ) < (j : ℝ) + A - 1 := by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    push_cast
    rw [show (j : ℝ) + 1 + A - 1 = (j : ℝ) + A by ring, div_sub_div _ _ h0.ne' (by linarith),
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hsum1 : ‖((R : ℝ) : ℂ) - ∑ j ∈ Finset.range (n + 1), 1 / (w + j)‖ ≤ 24 := by
    have e : ((R : ℝ) : ℂ) - ∑ j ∈ Finset.range (n + 1), 1 / (w + j)
        = ∑ j ∈ Finset.range (n + 1), (1 / (((j : ℝ) + A : ℝ) : ℂ) - 1 / (w + j)) := by
      rw [hR, Finset.sum_sub_distrib]
      push_cast
      rfl
    rw [e]
    calc ‖∑ j ∈ Finset.range (n + 1), (1 / (((j : ℝ) + A : ℝ) : ℂ) - 1 / (w + j))‖
        ≤ ∑ j ∈ Finset.range (n + 1), ‖1 / (((j : ℝ) + A : ℝ) : ℂ) - 1 / (w + j)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range (n + 1), 12 * A / ((j : ℝ) + A) ^ 2 :=
          Finset.sum_le_sum fun j _ => hterm j
      _ = 12 * A * ∑ j ∈ Finset.range (n + 1), 1 / ((j : ℝ) + A) ^ 2 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
      _ ≤ 12 * A * ∑ j ∈ Finset.range (n + 1),
            (1 / ((j : ℝ) + A - 1) - 1 / (((j + 1 : ℕ) : ℝ) + A - 1)) := by
          gcongr with j _; exact hsq j
      _ = 12 * A * (1 / ((0 : ℕ) + A - 1) - 1 / (((n + 1 : ℕ) : ℝ) + A - 1)) := by
          rw [Finset.sum_range_sub' (fun j : ℕ => 1 / ((j : ℝ) + A - 1))]
      _ ≤ 12 * A * (1 / (A - 1)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have : (0 : ℝ) ≤ 1 / (((n + 1 : ℕ) : ℝ) + A - 1) := by
            apply div_nonneg zero_le_one; push_cast; linarith [hnpos]
          simp only [Nat.cast_zero, zero_add]; linarith
      _ ≤ 24 := by
          rw [mul_one_div, div_le_iff₀ (by linarith)]; linarith
  have hRup : R ≤ Real.log ((n : ℝ) + A) := by
    have hle : ∀ j : ℕ, 1 / ((j : ℝ) + A)
        ≤ Real.log (((j + 1 : ℕ) : ℝ) + A - 1) - Real.log ((j : ℝ) + A - 1) := by
      intro j
      have h0 : (0 : ℝ) < (j : ℝ) + A - 1 := by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
      have := PPF.RH.Dg.le_log_succ_sub_log h0
      push_cast
      rw [show (j : ℝ) + 1 + A - 1 = (j : ℝ) + A - 1 + 1 by ring]
      rwa [show (j : ℝ) + A - 1 + 1 = (j : ℝ) + A by ring] at this ⊢
    calc R ≤ ∑ j ∈ Finset.range (n + 1),
          (Real.log (((j + 1 : ℕ) : ℝ) + A - 1) - Real.log ((j : ℝ) + A - 1)) :=
          Finset.sum_le_sum fun j _ => hle j
      _ = Real.log (((n + 1 : ℕ) : ℝ) + A - 1) - Real.log (((0 : ℕ) : ℝ) + A - 1) :=
          Finset.sum_range_sub (fun j : ℕ => Real.log ((j : ℝ) + A - 1)) (n + 1)
      _ ≤ Real.log ((n : ℝ) + A) := by
          have : 0 ≤ Real.log (((0 : ℕ) : ℝ) + A - 1) := Real.log_nonneg (by push_cast; linarith)
          have e : ((n + 1 : ℕ) : ℝ) + A - 1 = (n : ℝ) + A := by push_cast; ring
          rw [e]; linarith
  have hRlow : Real.log ((n : ℝ) + 1 + A) - Real.log A ≤ R := by
    have hle : ∀ j : ℕ, Real.log (((j + 1 : ℕ) : ℝ) + A) - Real.log ((j : ℝ) + A)
        ≤ 1 / ((j : ℝ) + A) := by
      intro j
      have h0 : (0 : ℝ) < (j : ℝ) + A := by positivity
      have := PPF.RH.Dg.log_succ_sub_log_le h0
      push_cast
      rwa [show (j : ℝ) + 1 + A = (j : ℝ) + A + 1 by ring]
    calc Real.log ((n : ℝ) + 1 + A) - Real.log A
        = Real.log (((n + 1 : ℕ) : ℝ) + A) - Real.log (((0 : ℕ) : ℝ) + A) := by push_cast; ring_nf
      _ = ∑ j ∈ Finset.range (n + 1),
          (Real.log (((j + 1 : ℕ) : ℝ) + A) - Real.log ((j : ℝ) + A)) :=
          (Finset.sum_range_sub (fun j : ℕ => Real.log ((j : ℝ) + A)) (n + 1)).symm
      _ ≤ R := Finset.sum_le_sum fun j _ => hle j
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg (by linarith)
  have hR1 : R - Real.log n ≤ 1 := by
    have : Real.log ((n : ℝ) + A) - Real.log n ≤ A / n := by
      rw [← Real.log_div (by positivity) hnpos.ne']
      have h := Real.log_le_sub_one_of_pos (show 0 < ((n : ℝ) + A) / n by positivity)
      have e : ((n : ℝ) + A) / n - 1 = A / n := by field_simp; ring
      linarith
    have : A / n ≤ 1 := (div_le_one hnpos).mpr hn
    linarith
  have hR2 : Real.log n - R ≤ Real.log A := by
    have : Real.log n ≤ Real.log ((n : ℝ) + 1 + A) :=
      Real.log_le_log hnpos (by linarith)
    linarith
  have hsum2 : ‖(Real.log n : ℂ) - ((R : ℝ) : ℂ)‖ ≤ 1 + Real.log A := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  calc ‖(Real.log n : ℂ) - ∑ j ∈ Finset.range (n + 1), 1 / (w + j)‖
      = ‖((Real.log n : ℂ) - ((R : ℝ) : ℂ))
          + (((R : ℝ) : ℂ) - ∑ j ∈ Finset.range (n + 1), 1 / (w + j))‖ := by ring_nf
    _ ≤ ‖(Real.log n : ℂ) - ((R : ℝ) : ℂ)‖
          + ‖((R : ℝ) : ℂ) - ∑ j ∈ Finset.range (n + 1), 1 / (w + j)‖ := norm_add_le _ _
    _ ≤ (1 + Real.log A) + 24 := add_le_add hsum2 hsum1
    _ = 25 + Real.log A := by ring

/-- `‖ψ(w)‖ ≤ 25 + log(|Im w| + 2)` on `1 ≤ Re w ≤ 2`, at every height. -/
lemma digamma_right {w : ℂ} (h1 : 1 ≤ w.re) (h2 : w.re ≤ 2) :
    ‖Complex.digamma w‖ ≤ 25 + Real.log (|w.im| + 2) := by
  have hw : 0 < w.re := by linarith
  refine le_of_tendsto (PPF.RH.Dg.tendsto_digamma hw).norm ?_
  filter_upwards [Filter.eventually_ge_atTop ⌈|w.im| + 2⌉₊] with n hn
  exact partial_bound_right h1 h2 (Nat.ceil_le.mp hn)

/-- Reflection identity for `ζ′/ζ` at points with `Re w > 1` and `cos(πw/2) ≠ 0`. -/
lemma reflect_identity_right {w : ℂ} (hre : 1 < w.re) (hcosw : cos ((π : ℂ) * w / 2) ≠ 0)
    (hz : riemannZeta w ≠ 0) :
    riemannZeta (1 - w) ≠ 0 ∧
    deriv riemannZeta (1 - w) / riemannZeta (1 - w) + deriv riemannZeta w / riemannZeta w
      = -(logDeriv PPF.RH.Refl.expFac w + Complex.digamma w
          + (-sin ((π : ℂ) * w / 2) * ((π : ℂ) / 2)) / cos ((π : ℂ) * w / 2)) := by
  have hnotnat : ∀ s : ℂ, 1 < s.re → ∀ n : ℕ, s ≠ -n := by
    intro s hs n h
    rw [h] at hs
    simp at hs
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hnot1 : ∀ s : ℂ, 1 < s.re → s ≠ 1 := by
    intro s hs h; rw [h] at hs; simp at hs
  have hG : Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  set F : ℂ → ℂ := fun s => riemannZeta (1 - s) with hF
  set G : ℂ → ℂ := fun s => PPF.RH.Refl.expFac s * Gamma s * cos ((π : ℂ) * s / 2)
    * riemannZeta s with hGdef
  have hFG : F =ᶠ[nhds w] G := by
    have hopen : IsOpen {s : ℂ | 1 < s.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds hre] with s hs
    simp only [hF, hGdef, PPF.RH.Refl.expFac]
    exact riemannZeta_one_sub (hnotnat s hs) (hnot1 s hs)
  have hFw : F w = G w := hFG.eq_of_nhds
  have hGw : G w ≠ 0 := by
    simp only [hGdef]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (PPF.RH.Refl.expFac_ne_zero w) hG) hcosw) hz
  have hzeta1 : riemannZeta (1 - w) ≠ 0 := by
    have : F w = riemannZeta (1 - w) := rfl
    rw [← this, hFw]; exact hGw
  refine ⟨hzeta1, ?_⟩
  have hw1 : 1 - w ≠ 1 := by
    intro h
    have : w = 0 := by linear_combination -h
    rw [this] at hre; simp at hre; linarith
  have hFderiv : HasDerivAt F (deriv riemannZeta (1 - w) * (-1)) w := by
    have h1 : HasDerivAt (fun s : ℂ => 1 - s) (-1) w := by
      simpa using (hasDerivAt_id w).const_sub 1
    exact (differentiableAt_riemannZeta hw1).hasDerivAt.comp w h1
  have hlogF : logDeriv F w = -(deriv riemannZeta (1 - w) / riemannZeta (1 - w)) := by
    rw [logDeriv_apply, hFderiv.deriv]
    show deriv riemannZeta (1 - w) * (-1) / riemannZeta (1 - w) = _
    ring
  have hlogFG : logDeriv F w = logDeriv G w := by
    rw [logDeriv_apply, logDeriv_apply, hFG.deriv_eq, hFw]
  have dE : DifferentiableAt ℂ PPF.RH.Refl.expFac w :=
    (PPF.RH.Refl.hasDerivAt_expFac w).differentiableAt
  have dΓ : DifferentiableAt ℂ Gamma w := Complex.differentiableAt_Gamma w (hnotnat w hre)
  have dC : DifferentiableAt ℂ (fun s : ℂ => cos ((π : ℂ) * s / 2)) w :=
    (PPF.RH.Refl.hasDerivAt_cosFac w).differentiableAt
  have dZ : DifferentiableAt ℂ riemannZeta w := differentiableAt_riemannZeta (hnot1 w hre)
  have l1 : logDeriv (fun s => PPF.RH.Refl.expFac s * Gamma s) w
      = logDeriv PPF.RH.Refl.expFac w + logDeriv Gamma w :=
    logDeriv_mul w (PPF.RH.Refl.expFac_ne_zero w) hG dE dΓ
  have l2 : logDeriv (fun s => PPF.RH.Refl.expFac s * Gamma s * cos ((π : ℂ) * s / 2)) w
      = logDeriv (fun s => PPF.RH.Refl.expFac s * Gamma s) w
        + logDeriv (fun s : ℂ => cos ((π : ℂ) * s / 2)) w :=
    logDeriv_mul (f := fun s => PPF.RH.Refl.expFac s * Gamma s)
      (g := fun s : ℂ => cos ((π : ℂ) * s / 2)) w
      (mul_ne_zero (PPF.RH.Refl.expFac_ne_zero w) hG) hcosw (dE.mul dΓ) dC
  have l3 : logDeriv G w
      = logDeriv (fun s => PPF.RH.Refl.expFac s * Gamma s * cos ((π : ℂ) * s / 2)) w
        + logDeriv riemannZeta w :=
    logDeriv_mul (f := fun s => PPF.RH.Refl.expFac s * Gamma s * cos ((π : ℂ) * s / 2))
      (g := riemannZeta) w
      (mul_ne_zero (mul_ne_zero (PPF.RH.Refl.expFac_ne_zero w) hG) hcosw) hz
      ((dE.mul dΓ).mul dC) dZ
  have lC : logDeriv (fun s : ℂ => cos ((π : ℂ) * s / 2)) w
      = (-sin ((π : ℂ) * w / 2) * ((π : ℂ) / 2)) / cos ((π : ℂ) * w / 2) := by
    rw [logDeriv_apply, (PPF.RH.Refl.hasDerivAt_cosFac w).deriv]
  have hdig : logDeriv Gamma w = Complex.digamma w := rfl
  have hZ : logDeriv riemannZeta w = deriv riemannZeta w / riemannZeta w := logDeriv_apply _ _
  have key : -(deriv riemannZeta (1 - w) / riemannZeta (1 - w))
      = logDeriv PPF.RH.Refl.expFac w + Complex.digamma w
        + (-sin ((π : ℂ) * w / 2) * ((π : ℂ) / 2)) / cos ((π : ℂ) * w / 2)
        + deriv riemannZeta w / riemannZeta w := by
    rw [← hlogF, hlogFG, l3, l2, l1, lC, hdig, hZ]
  linear_combination -key

end An

theorem reflect_explicit :
    ∀ w : ℂ, 1 / 2 ≤ w.re → w.re ≤ 3 / 2 → 2 ≤ |w.im| → riemannZeta w ≠ 0 →
      riemannZeta (1 - w) ≠ 0 ∧
      ‖deriv riemannZeta (1 - w) / riemannZeta (1 - w) + deriv riemannZeta w / riemannZeta w‖
        ≤ 32 * Real.log (|w.im| + 2) := by
  intro w hre1 hre2 him hz
  obtain ⟨hz1, hid⟩ := PPF.RH.Refl.reflect_identity him hz
  refine ⟨hz1, ?_⟩
  rw [hid, norm_neg]
  have hlog1 : 1 ≤ Real.log (|w.im| + 2) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  have hψ : ‖Complex.digamma w‖ ≤ 26 * Real.log (|w.im| + 2) :=
    An.digamma_le_26 w hre1 (by linarith) (by linarith)
  have htan : ‖(-sin ((π : ℂ) * w / 2) * ((π : ℂ) / 2)) / cos ((π : ℂ) * w / 2)‖ ≤ π := by
    have hz' : 1 ≤ |((π : ℂ) * w / 2).im| := by
      rw [PPF.RH.Refl.im_pi_mul_div_two, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_two]
      have : 2 * 1 ≤ π * |w.im| := by nlinarith [Real.pi_gt_three]
      linarith
    obtain ⟨hc0, hsc⟩ := PPF.RH.Refl.norm_sin_le_two_mul_norm_cos hz'
    have hcpos : 0 < ‖cos ((π : ℂ) * w / 2)‖ := norm_pos_iff.mpr hc0
    rw [norm_div, norm_mul, norm_neg, div_le_iff₀ hcpos]
    have hpi : ‖(π : ℂ) / 2‖ = π / 2 := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]; norm_num
    rw [hpi]
    nlinarith [Real.pi_pos]
  rw [PPF.RH.Refl.logDeriv_expFac w]
  have hK := An.log_two_pi_le
  have hpi := Real.pi_lt_d2
  calc ‖-Complex.log (2 * π) + Complex.digamma w
          + (-sin ((π : ℂ) * w / 2) * ((π : ℂ) / 2)) / cos ((π : ℂ) * w / 2)‖
      ≤ ‖-Complex.log (2 * π)‖ + ‖Complex.digamma w‖
          + ‖(-sin ((π : ℂ) * w / 2) * ((π : ℂ) / 2)) / cos ((π : ℂ) * w / 2)‖ :=
        norm_add₃_le
    _ ≤ Real.log (2 * π) + 26 * Real.log (|w.im| + 2) + π := by
        rw [norm_neg, An.norm_log_two_pi]; gcongr
    _ ≤ 32 * Real.log (|w.im| + 2) := by nlinarith

theorem left_line_explicit (hRH : RiemannHypothesis) :
    ∀ t : ℝ,
      riemannZeta ((-1 / 2 : ℝ) + t * I) ≠ 0 ∧
      ‖deriv riemannZeta ((-1 / 2 : ℝ) + t * I) / riemannZeta ((-1 / 2 : ℝ) + t * I)‖
        ≤ 100 * Real.log (|t| + 2) := by
  intro t
  set s : ℂ := ((-1 / 2 : ℝ) : ℂ) + t * I with hs
  have hsre : s.re = -1 / 2 := by simp [hs]
  have hs1 : s ≠ 1 := by
    intro h; rw [h] at hsre; norm_num at hsre
  have hnz : riemannZeta s ≠ 0 := by
    intro h0
    have htriv : ¬∃ n : ℕ, s = -2 * (n + 1) := by
      rintro ⟨n, hn⟩
      have h1 := congrArg Complex.re hn
      rw [hsre] at h1
      simp at h1
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have := hRH s h0 htriv hs1
    rw [hsre] at this; norm_num at this
  refine ⟨hnz, ?_⟩
  -- reflect to `w = 3/2 − t i`
  set w : ℂ := ((3 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I with hw
  have hwre : w.re = 3 / 2 := by simp [hw]
  have hwim : w.im = -t := by simp [hw]
  have hzw : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by rw [hwre]; norm_num)
  have hzpt : (π : ℂ) * w / 2 = ((3 * π / 4 : ℝ) : ℂ) + ((-(π * t / 2) : ℝ) : ℂ) * I := by
    rw [hw]; push_cast; ring
  obtain ⟨hcos, hsc⟩ := An.sin_cos_three_quarter (-(π * t / 2))
  rw [← hzpt] at hcos hsc
  obtain ⟨-, hid⟩ := An.reflect_identity_right (by rw [hwre]; norm_num) hcos hzw
  have h1w : 1 - w = s := by simp only [hw, hs]; push_cast; ring
  rw [h1w] at hid
  -- the three pieces
  have hright : ‖deriv riemannZeta w / riemannZeta w‖ ≤ 24 := by
    have := Carmichael.EF.norm_logDeriv_LFunction_le (N := 1) (1 : DirichletCharacter ℂ 1)
      (c := 3 / 2) (by norm_num) (by norm_num) (-t)
    rw [DirichletCharacter.LFunction_modOne_eq] at this
    have hw' : ((3 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I = w := rfl
    rw [hw'] at this
    norm_num at this ⊢
    exact this
  have hψ : ‖Complex.digamma w‖ ≤ 25 + Real.log (|t| + 2) := by
    have := An.digamma_right (w := w) (by rw [hwre]; norm_num) (by rw [hwre]; norm_num)
    rwa [hwim, abs_neg] at this
  have htan : ‖(-sin ((π : ℂ) * w / 2) * ((π : ℂ) / 2)) / cos ((π : ℂ) * w / 2)‖ = π / 2 := by
    have hcpos : 0 < ‖cos ((π : ℂ) * w / 2)‖ := norm_pos_iff.mpr hcos
    rw [norm_div, norm_mul, norm_neg, hsc]
    have hpi : ‖(π : ℂ) / 2‖ = π / 2 := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]; norm_num
    rw [hpi]
    field_simp
  have hK := An.log_two_pi_le
  have hpi := Real.pi_lt_d2
  have hlog2 : Real.log 2 ≤ Real.log (|t| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hl2 := Real.log_two_gt_d9
  have hsum : ‖deriv riemannZeta s / riemannZeta s + deriv riemannZeta w / riemannZeta w‖
      ≤ Real.log (2 * π) + (25 + Real.log (|t| + 2)) + π / 2 := by
    rw [hid, norm_neg, PPF.RH.Refl.logDeriv_expFac w]
    calc ‖-Complex.log (2 * π) + Complex.digamma w
            + (-sin ((π : ℂ) * w / 2) * ((π : ℂ) / 2)) / cos ((π : ℂ) * w / 2)‖
        ≤ ‖-Complex.log (2 * π)‖ + ‖Complex.digamma w‖
            + ‖(-sin ((π : ℂ) * w / 2) * ((π : ℂ) / 2)) / cos ((π : ℂ) * w / 2)‖ :=
          norm_add₃_le
      _ ≤ Real.log (2 * π) + (25 + Real.log (|t| + 2)) + π / 2 := by
          rw [norm_neg, An.norm_log_two_pi, htan]; gcongr
  show ‖deriv riemannZeta s / riemannZeta s‖ ≤ 100 * Real.log (|t| + 2)
  calc ‖deriv riemannZeta s / riemannZeta s‖
      = ‖(deriv riemannZeta s / riemannZeta s + deriv riemannZeta w / riemannZeta w)
          - deriv riemannZeta w / riemannZeta w‖ := by ring_nf
    _ ≤ ‖deriv riemannZeta s / riemannZeta s + deriv riemannZeta w / riemannZeta w‖
          + ‖deriv riemannZeta w / riemannZeta w‖ := norm_sub_le _ _
    _ ≤ (Real.log (2 * π) + (25 + Real.log (|t| + 2)) + π / 2) + 24 := add_le_add hsum hright
    _ ≤ 100 * Real.log (|t| + 2) := by nlinarith

-- `hRH` is part of the frozen interface; reflection through D2 makes D4 unconditional.
set_option linter.unusedVariables false in
open Carmichael Carmichael.EF PPF.RH.GH in
theorem good_height_explicit (hRH : RiemannHypothesis) :
    ∀ T : ℝ, 2 ≤ T → ∃ t : ℝ, T ≤ t ∧ t ≤ T + 1 ∧
      ∀ σ : ℝ, -1 / 2 ≤ σ → σ ≤ 2 →
        riemannZeta ((σ : ℂ) + t * I) ≠ 0 ∧ riemannZeta ((σ : ℂ) - t * I) ≠ 0 ∧
        ‖deriv riemannZeta ((σ : ℂ) + t * I) / riemannZeta ((σ : ℂ) + t * I)‖
          ≤ 1010032 * Real.log (T + 4) ^ 2 ∧
        ‖deriv riemannZeta ((σ : ℂ) - t * I) / riemannZeta ((σ : ℂ) - t * I)‖
          ≤ 1010032 * Real.log (T + 4) ^ 2 := by
  intro T hT
  have hDD : DiskData etaFun 1 := diskData_etaFun
  set L : ℝ := Real.log (T + 4) with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hL0 : 0 < L := by linarith
  have hL1' : Real.log ((1:ℝ) * (T + 4)) = L := by rw [one_mul]
  set Γex : Finset ℝ :=
    {((round (T / (π / Real.log 2)) - 1 : ℤ) : ℝ) * (π / Real.log 2),
      ((round (T / (π / Real.log 2)) : ℤ) : ℝ) * (π / Real.log 2),
      ((round (T / (π / Real.log 2)) + 1 : ℤ) : ℝ) * (π / Real.log 2)} with hΓexdef
  have hΓexcard : (Γex.card : ℝ) ≤ 16 * Real.log ((1:ℝ) * (T + 4)) := by
    have h1 : Γex.card ≤ 3 := Finset.card_le_three
    have h3 : (Γex.card : ℝ) ≤ 3 := by exact_mod_cast h1
    rw [hL1']
    linarith
  obtain ⟨t, ht1, ht2, htgap, hgood⟩ := exists_good_height hDD hT Γex hΓexcard
  rw [hL1'] at htgap hgood
  have ht2' : (2:ℝ) ≤ t := by linarith
  set δ₀ : ℝ := 1 / (2000 * L) with hδ₀def
  have hδ₀0 : 0 < δ₀ := by positivity
  have hsin : δ₀ / 4 ≤ |Real.sin (t * Real.log 2)| := by
    apply abs_sin_log_two_ge hT ht1 ht2 hδ₀0
    intro j hj
    apply htgap
    rw [hΓexdef]
    rcases hj with rfl | rfl | rfl <;> simp
  have hδ5 : δ₀ / 5 ≤ 1 / 10 := by
    rw [hδ₀def]
    rw [div_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hR : ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 2 →
      riemannZeta ((σ:ℂ) + t * I) ≠ 0 ∧
      ‖deriv riemannZeta ((σ:ℂ) + t * I) / riemannZeta ((σ:ℂ) + t * I)‖
        ≤ 1010000 * L ^ 2 := by
    intro σ h1 h2
    set s : ℂ := (σ:ℂ) + t * I with hsdef
    have hsre : s.re = σ := by simp [hsdef]
    have hsim : s.im = t := by simp [hsdef]
    have hs0 : 0 < s.re := by rw [hsre]; linarith
    have hs1 : s ≠ 1 := by
      intro h
      have := congrArg Complex.im h
      rw [hsim, Complex.one_im] at this
      linarith
    have hg : δ₀ / 5 ≤ ‖gFun s‖ :=
      norm_gFun_ge hδ5 (by linarith)
    have hg0 : gFun s ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hg
      linarith
    obtain ⟨hη, hηb⟩ := hgood σ h1 (by linarith)
    have hz : riemannZeta s ≠ 0 := by
      intro h0
      apply hη
      rw [etaFun_eq_mul hs0 hs1, h0, mul_zero]
    refine ⟨hz, ?_⟩
    rw [logDeriv_zeta_split hs0 hs1 hg0 hz]
    have hgd : ‖deriv gFun s / gFun s‖ ≤ 10000 * L := by
      rw [norm_div]
      have hgpos : 0 < ‖gFun s‖ := norm_pos_iff.mpr hg0
      rw [div_le_iff₀ hgpos]
      have hd := norm_deriv_gFun_le_one (s := s) (by rw [hsre]; exact h1)
      have : 10000 * L * (δ₀ / 5) = 1 := by
        rw [hδ₀def]
        field_simp
        ring
      nlinarith
    calc ‖deriv etaFun s / etaFun s - deriv gFun s / gFun s‖
        ≤ ‖deriv etaFun s / etaFun s‖ + ‖deriv gFun s / gFun s‖ := norm_sub_le _ _
      _ ≤ 1000000 * L ^ 2 + 10000 * L := add_le_add hηb hgd
      _ ≤ 1010000 * L ^ 2 := by nlinarith
  have hR' : ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 2 →
      riemannZeta ((σ:ℂ) - t * I) ≠ 0 ∧
      ‖deriv riemannZeta ((σ:ℂ) - t * I) / riemannZeta ((σ:ℂ) - t * I)‖
        ≤ 1010000 * L ^ 2 := by
    intro σ h1 h2
    obtain ⟨hz, hb⟩ := hR σ h1 h2
    set s : ℂ := (σ:ℂ) + t * I with hsdef
    have hs0 : 0 < s.re := by simp [hsdef]; linarith
    have hs1 : s ≠ 1 := by
      intro h
      have := congrArg Complex.im h
      simp [hsdef] at this
      linarith
    have hc : (σ:ℂ) - t * I = (starRingEnd ℂ) s := (conj_add_mul_I σ t).symm
    rw [hc, PPF.RH.riemannZeta_conj hs0, PPF.RH.deriv_riemannZeta_conj hs0 hs1]
    refine ⟨fun h0 => hz ?_, ?_⟩
    · rwa [map_eq_zero] at h0
    · rw [← map_div₀, Complex.norm_conj]
      exact hb
  have hlogt : Real.log (t + 2) ≤ L := by
    rw [hLdef]
    exact Real.log_le_log (by linarith) (by linarith)
  have hC₂L : 32 * Real.log (t + 2) ≤ 32 * L ^ 2 := by
    have h0 : 0 ≤ Real.log (t + 2) := Real.log_nonneg (by linarith)
    nlinarith
  have hLsq : 0 ≤ L ^ 2 := sq_nonneg L
  have hleft : ∀ (σ u : ℝ), -1 / 2 ≤ σ → σ < 1 / 2 → |u| = t →
      riemannZeta (((1 - σ : ℝ) : ℂ) - u * I) ≠ 0 →
      ‖deriv riemannZeta (((1 - σ : ℝ) : ℂ) - u * I)
          / riemannZeta (((1 - σ : ℝ) : ℂ) - u * I)‖ ≤ 1010000 * L ^ 2 →
      riemannZeta ((σ:ℂ) + u * I) ≠ 0 ∧
      ‖deriv riemannZeta ((σ:ℂ) + u * I) / riemannZeta ((σ:ℂ) + u * I)‖
        ≤ 1010032 * L ^ 2 := by
    intro σ u h1 h2 hu hwz hwb
    set w : ℂ := ((1 - σ : ℝ) : ℂ) - u * I with hwdef
    have hwre : w.re = 1 - σ := by simp [hwdef]
    have hwim : w.im = -u := by simp [hwdef]
    have h1w : (1:ℂ) - w = (σ:ℂ) + u * I := by
      rw [hwdef]
      push_cast
      ring
    have habs : |w.im| = t := by rw [hwim, abs_neg, hu]
    obtain ⟨hnz, hb⟩ := reflect_explicit w (by rw [hwre]; linarith) (by rw [hwre]; linarith)
      (by rw [habs]; linarith) hwz
    rw [h1w] at hnz hb
    rw [habs] at hb
    refine ⟨hnz, ?_⟩
    set A := deriv riemannZeta ((σ:ℂ) + u * I) / riemannZeta ((σ:ℂ) + u * I)
    set B := deriv riemannZeta w / riemannZeta w
    calc ‖A‖ = ‖(A + B) - B‖ := by ring_nf
      _ ≤ ‖A + B‖ + ‖B‖ := norm_sub_le _ _
      _ ≤ 32 * Real.log (t + 2) + 1010000 * L ^ 2 := add_le_add hb hwb
      _ ≤ 32 * L ^ 2 + 1010000 * L ^ 2 := by linarith
      _ = 1010032 * L ^ 2 := by ring
  refine ⟨t, ht1, ht2, ?_⟩
  intro σ hσ1 hσ2
  have ht0 : 0 ≤ t := by linarith
  rcases le_or_gt (1 / 2) σ with h | h
  · obtain ⟨hz1, hb1⟩ := hR σ h hσ2
    obtain ⟨hz2, hb2⟩ := hR' σ h hσ2
    refine ⟨hz1, hz2, ?_, ?_⟩
    · nlinarith
    · nlinarith
  · have hσ' : 1 / 2 ≤ 1 - σ := by linarith
    have hσ'' : 1 - σ ≤ 2 := by linarith
    obtain ⟨hwz1, hwb1⟩ := hR' (1 - σ) hσ' hσ''
    obtain ⟨hz1, hb1⟩ := hleft σ t hσ1 h (abs_of_nonneg ht0)
      (by exact_mod_cast hwz1) (by exact_mod_cast hwb1)
    obtain ⟨hwz2, hwb2⟩ := hR (1 - σ) hσ' hσ''
    have hneg : ∀ v : ℂ, ((1 - σ : ℝ) : ℂ) - ((-t : ℝ) : ℂ) * I = ((1 - σ : ℝ) : ℂ) + t * I := by
      intro _; push_cast; ring
    have hneg' : (σ:ℂ) + ((-t : ℝ) : ℂ) * I = (σ:ℂ) - t * I := by push_cast; ring
    obtain ⟨hz2, hb2⟩ := hleft σ (-t) hσ1 h (by rw [abs_neg, abs_of_nonneg ht0])
      (by rw [hneg 0]; exact_mod_cast hwz2) (by rw [hneg 0]; exact_mod_cast hwb2)
    rw [hneg'] at hz2 hb2
    exact ⟨hz1, hz2, hb1, hb2⟩

end PPF.Explicit
