import PPF.RH.Defs
import PPF.RH.Digamma.Euler

/-!
# D1: the digamma function grows logarithmically on vertical strips

Route: Euler's limit `Γ(w) = lim n^w n!/(w(w+1)⋯(w+n))` (Mathlib
`Complex.GammaSeq_tendsto_Gamma`, via `Complex.GammaSeq_eq_approx_Gamma_integral`)
holds uniformly on strips `a ≤ Re w ≤ b` (`a > 0`) by dominated convergence
(`PPF.RH.Digamma.Euler`), so log-derivatives converge (`Complex.logDeriv_tendsto`):
`ψ(w) = lim (log n − ∑_{j ≤ n} 1/(w+j))`. With `A = |Im w| + 1`, compare
`∑ 1/(w+j)` with `∑ 1/(j+A)` (`|1/(w+j) − 1/(j+A)| ≤ 12A/(j+A)²`, total `≤ 24`) and the
latter with `log n` by telescoping logarithms (error `≤ 1 + log A`).
-/

namespace PPF.RH

open Complex Filter Topology

namespace Dg

lemma differentiableOn_gammaSeq {n : ℕ} (hn : n ≠ 0) :
    DifferentiableOn ℂ (fun s => GammaSeq s n) {s : ℂ | 0 < s.re} := by
  intro s hs
  have hs' : 0 < s.re := hs
  apply DifferentiableAt.differentiableWithinAt
  simp only [GammaSeq]
  apply DifferentiableAt.div
  · exact (differentiableAt_id.const_cpow (Or.inl (Nat.cast_ne_zero.mpr hn))).mul_const _
  · exact DifferentiableAt.fun_finsetProd (fun j _ => differentiableAt_id.add_const _)
  · rw [Finset.prod_ne_zero_iff]
    intro j _ h
    have := congrArg re h
    simp at this
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

lemma logDeriv_gammaSeq {n : ℕ} (hn : n ≠ 0) {w : ℂ} (hw : 0 < w.re) :
    logDeriv (fun s => GammaSeq s n) w
      = (Real.log n : ℂ) - ∑ j ∈ Finset.range (n + 1), 1 / (w + j) := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hj : ∀ j ∈ Finset.range (n + 1), w + (j : ℂ) ≠ 0 := by
    intro j _ h
    have := congrArg re h
    simp at this
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hP : ∏ j ∈ Finset.range (n + 1), (w + (j : ℂ)) ≠ 0 := Finset.prod_ne_zero_iff.mpr hj
  have hfac : ((Nat.factorial n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hcpow : (n : ℂ) ^ w ≠ 0 := (cpow_ne_zero_iff_of_exponent_ne_zero
    (by intro h; rw [h, zero_re] at hw; exact lt_irrefl _ hw)).mpr hn'
  show logDeriv (fun s => (n : ℂ) ^ s * ((Nat.factorial n : ℕ) : ℂ)
      / ∏ j ∈ Finset.range (n + 1), (s + (j : ℂ))) w = _
  rw [logDeriv_div (f := fun s => (n : ℂ) ^ s * ((Nat.factorial n : ℕ) : ℂ))
    (g := fun s => ∏ j ∈ Finset.range (n + 1), (s + (j : ℂ))) w (mul_ne_zero hcpow hfac) hP
    ((differentiableAt_id.const_cpow (Or.inl hn')).mul_const _)
    (DifferentiableAt.fun_finsetProd (fun j _ => differentiableAt_id.add_const _)),
    logDeriv_mul_const (f := fun s => (n : ℂ) ^ s) w _ hfac]
  congr 1
  · rw [logDeriv_apply, (hasStrictDerivAt_const_cpow (Or.inl hn')).hasDerivAt.deriv,
      mul_div_cancel_left₀ _ hcpow, Complex.ofReal_log (Nat.cast_nonneg n),
      Complex.ofReal_natCast]
  · rw [logDeriv_prod hj (fun j _ => differentiableAt_id.add_const _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [logDeriv_apply, deriv_add_const, deriv_id'']

/-- `ψ(w) = lim (log n − ∑_{j ≤ n} 1/(w+j))` for `Re w > 0`. -/
lemma tendsto_digamma {w : ℂ} (hw : 0 < w.re) :
    Tendsto (fun n : ℕ => (Real.log n : ℂ) - ∑ j ∈ Finset.range (n + 1), 1 / (w + j))
      atTop (𝓝 (digamma w)) := by
  have h := Complex.logDeriv_tendsto (f := fun (n : ℕ) (s : ℂ) => GammaSeq s n)
    (isOpen_lt continuous_const continuous_re) (show w ∈ {s : ℂ | 0 < s.re} from hw)
    tendstoLocallyUniformlyOn_gammaSeq
    (by filter_upwards [eventually_ne_atTop 0] with n hn using differentiableOn_gammaSeq hn)
    (Gamma_ne_zero_of_re_pos hw)
  rw [← digamma_def] at h
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn using logDeriv_gammaSeq hn hw

/-- `1/(k+1) ≤ log(k+1) − log k ≤ 1/k` for `k > 0`. -/
lemma log_succ_sub_log_le {k : ℝ} (hk : 0 < k) : Real.log (k + 1) - Real.log k ≤ 1 / k := by
  rw [← Real.log_div (by linarith) hk.ne']
  have := Real.log_le_sub_one_of_pos (show 0 < (k + 1) / k by positivity)
  have e : (k + 1) / k - 1 = 1 / k := by field_simp; ring
  linarith

lemma le_log_succ_sub_log {k : ℝ} (hk : 0 < k) : 1 / (k + 1) ≤ Real.log (k + 1) - Real.log k := by
  have := Real.log_le_sub_one_of_pos (show 0 < k / (k + 1) by positivity)
  rw [Real.log_div hk.ne' (by linarith)] at this
  have e : k / (k + 1) - 1 = -(1 / (k + 1)) := by field_simp; ring
  linarith

/-- Main estimate for the partial sums. -/
lemma partial_bound {w : ℂ} (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 2) (h3 : 1 ≤ |w.im|)
    {n : ℕ} (hn : |w.im| + 1 ≤ n) :
    ‖(Real.log n : ℂ) - ∑ j ∈ Finset.range (n + 1), 1 / (w + j)‖
      ≤ 25 + Real.log (|w.im| + 1) := by
  set A : ℝ := |w.im| + 1 with hA
  have hA2 : 2 ≤ A := by linarith
  have hnpos : (0 : ℝ) < n := by linarith
  set R : ℝ := ∑ j ∈ Finset.range (n + 1), 1 / ((j : ℝ) + A) with hR
  -- comparison of the two sums
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
  -- comparison of `R` with `log n`
  have hRup : R ≤ Real.log ((n : ℝ) + A) := by
    have hle : ∀ j : ℕ, 1 / ((j : ℝ) + A)
        ≤ Real.log (((j + 1 : ℕ) : ℝ) + A - 1) - Real.log ((j : ℝ) + A - 1) := by
      intro j
      have h0 : (0 : ℝ) < (j : ℝ) + A - 1 := by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
      have := le_log_succ_sub_log h0
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
      have := log_succ_sub_log_le h0
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
      have := log_succ_sub_log_le (k := (n : ℝ) / A) (by positivity)
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

end Dg

/-- D1. -/
theorem norm_digamma_le :
    ∃ C : ℝ, ∀ w : ℂ, 1 / 2 ≤ w.re → w.re ≤ 2 → 1 ≤ |w.im| →
      ‖Complex.digamma w‖ ≤ C * Real.log (|w.im| + 2) := by
  refine ⟨26, fun w h1 h2 h3 => ?_⟩
  have hw : 0 < w.re := by linarith
  have hb : ‖Complex.digamma w‖ ≤ 25 + Real.log (|w.im| + 1) := by
    refine le_of_tendsto (Dg.tendsto_digamma hw).norm ?_
    filter_upwards [eventually_ge_atTop ⌈|w.im| + 1⌉₊] with n hn
    exact Dg.partial_bound h1 h2 h3 (Nat.ceil_le.mp hn)
  have hlog3 : 1 ≤ Real.log (|w.im| + 2) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  have hmono : Real.log (|w.im| + 1) ≤ Real.log (|w.im| + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  linarith

end PPF.RH
