import Mathlib

/-!
# Real-analysis helpers for K4

* `sq_integral_le`, `norm_sq_integral_le`: Cauchy–Schwarz on an interval.
* `integral_window_le`: `∫_X^{2X} (∫_x^{x+h} g) dx ≤ h ∫_X^{3X} g` for `g ≥ 0`
  (via the primitive `G y = ∫_X^y g`, no Fubini).
* `integral_weight_norm_sq_le`: expansion of a weighted mean square of a finite
  sum `∑ c_ρ u^{β_ρ}` with `Re β_ρ = α/2` into the kernel integrals
  `∫ w(u) u^{α + i(Im β_ρ − Im β_ρ')} du`.
-/

namespace PPF.RH.MS

open Complex MeasureTheory intervalIntegral Set

/-- Cauchy–Schwarz on an interval, real form. -/
theorem sq_integral_le {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
    (∫ x in a..b, f x) ^ 2 ≤ (b - a) * ∫ x in a..b, f x ^ 2 := by
  rcases eq_or_lt_of_le hab with h | h
  · subst h; simp
  have hba : 0 < b - a := sub_pos.mpr h
  have hfu : ContinuousOn f (uIcc a b) := by rwa [uIcc_of_le hab]
  have hfi : IntervalIntegrable f volume a b := hfu.intervalIntegrable
  have hf2 : IntervalIntegrable (fun x => f x ^ 2) volume a b :=
    (hfu.pow 2).intervalIntegrable
  set I := ∫ x in a..b, f x with hI
  set J := ∫ x in a..b, f x ^ 2 with hJ
  set m := I / (b - a) with hm
  have h0 : 0 ≤ ∫ x in a..b, (f x - m) ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun u _ => sq_nonneg _)
  have hexp : ∫ x in a..b, (f x - m) ^ 2 = J - 2 * m * I + m ^ 2 * (b - a) := by
    have hfun : (fun x => (f x - m) ^ 2) = fun x => (f x ^ 2 - 2 * m * f x) + m ^ 2 := by
      ext x; ring
    rw [hfun, intervalIntegral.integral_add (hf2.sub (hfi.const_mul _)) intervalIntegrable_const,
      intervalIntegral.integral_sub hf2 (hfi.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hkey : J - 2 * m * I + m ^ 2 * (b - a) = J - I ^ 2 / (b - a) := by
    rw [hm]; field_simp; ring
  have : I ^ 2 / (b - a) ≤ J := by linarith
  rw [div_le_iff₀ hba] at this
  linarith

/-- Cauchy–Schwarz on an interval, complex form. -/
theorem norm_sq_integral_le {F : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hF : ContinuousOn F (Icc a b)) :
    ‖∫ x in a..b, F x‖ ^ 2 ≤ (b - a) * ∫ x in a..b, ‖F x‖ ^ 2 := by
  have h1 := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := F) hab
  have h2 := sq_integral_le hab hF.norm
  calc ‖∫ x in a..b, F x‖ ^ 2 ≤ (∫ x in a..b, ‖F x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

/-- `∫_X^{2X} f ≤ h · (h ∫_X^{3X} g)` when `f x ≤ h ∫_x^{x+h} g` on `[X, 2X]`, `g ≥ 0`. -/
theorem integral_window_le {g f : ℝ → ℝ} {X h : ℝ} (hX : 0 ≤ X) (hh : 0 ≤ h) (hhX : h ≤ X)
    (hg : IntervalIntegrable g volume X (3 * X)) (hg0 : ∀ u ∈ Icc X (3 * X), 0 ≤ g u)
    (hf : IntervalIntegrable f volume X (2 * X))
    (hfg : ∀ x ∈ Icc X (2 * X), f x ≤ h * ∫ u in x..x + h, g u) :
    ∫ x in X..2 * X, f x ≤ h * (h * ∫ u in X..3 * X, g u) := by
  set G : ℝ → ℝ := fun y => ∫ u in X..y, g u with hGdef
  have hsub : ∀ y z, y ∈ Icc X (3 * X) → z ∈ Icc X (3 * X) →
      IntervalIntegrable g volume y z := by
    intro y z hy hz
    refine hg.mono_set ?_
    rw [uIcc_of_le (by linarith : X ≤ 3 * X)]
    exact uIcc_subset_Icc hy hz
  have hXm : X ∈ Icc X (3 * X) := ⟨le_rfl, by linarith⟩
  have hdiff : ∀ y z, y ∈ Icc X (3 * X) → z ∈ Icc X (3 * X) →
      G z - G y = ∫ u in y..z, g u := by
    intro y z hy hz
    exact intervalIntegral.integral_interval_sub_left (hsub X z hXm hz) (hsub X y hXm hy)
  have hGmono : MonotoneOn G (Icc X (3 * X)) := by
    intro y hy z hz hyz
    have h1 := hdiff y z hy hz
    have h2 : 0 ≤ ∫ u in y..z, g u :=
      intervalIntegral.integral_nonneg hyz (fun u hu => hg0 u ⟨hy.1.trans hu.1, hu.2.trans hz.2⟩)
    linarith
  have hG0 : ∀ y ∈ Icc X (3 * X), 0 ≤ G y := fun y hy =>
    intervalIntegral.integral_nonneg hy.1 (fun u hu => hg0 u ⟨hu.1, hu.2.trans hy.2⟩)
  have hGint : ∀ y z, y ∈ Icc X (3 * X) → z ∈ Icc X (3 * X) →
      IntervalIntegrable G volume y z := by
    intro y z hy hz
    apply MonotoneOn.intervalIntegrable
    exact hGmono.mono (uIcc_subset_Icc hy hz)
  have h2X : 2 * X ∈ Icc X (3 * X) := ⟨by linarith, by linarith⟩
  have hXh : X + h ∈ Icc X (3 * X) := ⟨by linarith, by linarith⟩
  have h2Xh : 2 * X + h ∈ Icc X (3 * X) := ⟨by linarith, by linarith⟩
  have h3X : 3 * X ∈ Icc X (3 * X) := ⟨by linarith, le_rfl⟩
  -- the shifted primitive is integrable on `[X, 2X]`
  have hGshift : IntervalIntegrable (fun x => G (x + h)) volume X (2 * X) := by
    apply MonotoneOn.intervalIntegrable
    rw [uIcc_of_le (by linarith : X ≤ 2 * X)]
    intro y hy z hz hyz
    exact hGmono ⟨by linarith [hy.1], by linarith [hy.2]⟩ ⟨by linarith [hz.1], by linarith [hz.2]⟩
      (by linarith)
  have hstep1 : ∫ x in X..2 * X, f x ≤ ∫ x in X..2 * X, h * (G (x + h) - G x) := by
    apply intervalIntegral.integral_mono_on (by linarith) hf
    · exact (hGshift.sub (hGint X (2 * X) hXm h2X)).const_mul h
    · intro x hx
      have hx3 : x ∈ Icc X (3 * X) := ⟨hx.1, by linarith [hx.2]⟩
      have hxh3 : x + h ∈ Icc X (3 * X) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
      rw [hdiff x (x + h) hx3 hxh3]
      exact hfg x hx
  have hsplit : ∫ x in X..2 * X, h * (G (x + h) - G x)
      = h * ((∫ x in 2 * X..2 * X + h, G x) - ∫ x in X..X + h, G x) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub hGshift (hGint X (2 * X) hXm h2X),
      intervalIntegral.integral_comp_add_right (fun x => G x) h]
    have e1 := intervalIntegral.integral_add_adjacent_intervals
      (hGint (X + h) (2 * X) hXh h2X) (hGint (2 * X) (2 * X + h) h2X h2Xh)
    have e2 := intervalIntegral.integral_add_adjacent_intervals
      (hGint X (X + h) hXm hXh) (hGint (X + h) (2 * X) hXh h2X)
    rw [show 2 * X + h = 2 * X + h from rfl] at e1
    rw [← e1, ← e2]
    ring
  have hup : ∫ x in 2 * X..2 * X + h, G x ≤ h * G (3 * X) := by
    have := intervalIntegral.integral_mono_on (by linarith : 2 * X ≤ 2 * X + h)
      (hGint (2 * X) (2 * X + h) h2X h2Xh) (intervalIntegrable_const (c := G (3 * X)))
      (fun x hx => hGmono ⟨by linarith [hx.1], by linarith [hx.2]⟩ h3X (by linarith [hx.2]))
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith
  have hlow : 0 ≤ ∫ x in X..X + h, G x :=
    intervalIntegral.integral_nonneg (by linarith)
      (fun x hx => hG0 x ⟨hx.1, by linarith [hx.2]⟩)
  calc ∫ x in X..2 * X, f x ≤ h * ((∫ x in 2 * X..2 * X + h, G x) - ∫ x in X..X + h, G x) := by
        rw [← hsplit]; exact hstep1
    _ ≤ h * (h * G (3 * X)) := by
        apply mul_le_mul_of_nonneg_left _ hh
        linarith
    _ = h * (h * ∫ u in X..3 * X, g u) := rfl

/-- Conjugating a real-base power. -/
theorem conj_ofReal_cpow {u : ℝ} (hu : 0 < u) (z : ℂ) :
    (starRingEnd ℂ) ((u : ℂ) ^ z) = (u : ℂ) ^ ((starRingEnd ℂ) z) := by
  have harg : (u : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hu.le]; exact Real.pi_ne_zero.symm
  rw [Complex.cpow_conj _ _ harg, Complex.conj_ofReal]

theorem continuousOn_ofReal_cpow (w : ℂ) :
    ContinuousOn (fun u : ℝ => (u : ℂ) ^ w) (Ioi 0) := by
  intro u hu
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.cpow Complex.continuous_ofReal.continuousAt continuousAt_const
  exact Complex.ofReal_mem_slitPlane.mpr hu

/-- Weighted mean square of a finite sum of powers with a common real part. -/
theorem integral_weight_norm_sq_le (Z : Finset ℂ) (c β : ℂ → ℂ) (α : ℝ)
    (hβ : ∀ ρ ∈ Z, (β ρ).re = α / 2) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {w : ℝ → ℝ}
    (hw : ContinuousOn w (Icc a b)) (K : ℝ → ℝ)
    (hK : ∀ τ : ℝ, ‖∫ u in a..b, ((w u : ℝ) : ℂ) * (u : ℂ) ^ ((α : ℂ) + (τ : ℂ) * I)‖ ≤ K τ) :
    ∫ u in a..b, w u * ‖∑ ρ ∈ Z, c ρ * (u : ℂ) ^ (β ρ)‖ ^ 2
      ≤ ∑ ρ ∈ Z, ∑ ρ' ∈ Z, ‖c ρ‖ * ‖c ρ'‖ * K ((β ρ).im - (β ρ').im) := by
  set E : ℂ → ℂ → ℂ := fun ρ ρ' => (α : ℂ) + (((β ρ).im - (β ρ').im : ℝ) : ℂ) * I with hE
  have hIcc : ∀ u ∈ uIcc a b, 0 < u := by
    intro u hu; rw [uIcc_of_le hab] at hu; exact ha.trans_le hu.1
  -- pointwise identity
  have hpt : ∀ u ∈ uIcc a b,
      (((w u * ‖∑ ρ ∈ Z, c ρ * (u : ℂ) ^ (β ρ)‖ ^ 2 : ℝ)) : ℂ)
        = ∑ ρ ∈ Z, ∑ ρ' ∈ Z,
            c ρ * (starRingEnd ℂ) (c ρ') * (((w u : ℝ) : ℂ) * (u : ℂ) ^ (E ρ ρ')) := by
    intro u hu
    have hu0 := hIcc u hu
    set S := ∑ ρ ∈ Z, c ρ * (u : ℂ) ^ (β ρ) with hS
    have hnorm : ((‖S‖ : ℝ) : ℂ) ^ 2 = S * (starRingEnd ℂ) S := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    have hconj : (starRingEnd ℂ) S
        = ∑ ρ' ∈ Z, (starRingEnd ℂ) (c ρ') * (u : ℂ) ^ ((starRingEnd ℂ) (β ρ')) := by
      rw [hS, map_sum]
      refine Finset.sum_congr rfl fun ρ' _ => ?_
      rw [map_mul, conj_ofReal_cpow hu0]
    have hpow : ∀ ρ ∈ Z, ∀ ρ' ∈ Z,
        (u : ℂ) ^ (β ρ) * (u : ℂ) ^ ((starRingEnd ℂ) (β ρ')) = (u : ℂ) ^ (E ρ ρ') := by
      intro ρ hρ ρ' hρ'
      rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hu0.ne')]
      congr 1
      apply Complex.ext
      · simp only [hE, Complex.add_re, Complex.conj_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, sub_zero]
        rw [hβ ρ hρ, hβ ρ' hρ']; ring
      · simp only [hE, Complex.add_im, Complex.conj_im, Complex.ofReal_im, Complex.mul_im,
          Complex.I_re, Complex.I_im, Complex.ofReal_re, mul_zero, mul_one, zero_add]
        ring
    push_cast
    rw [hnorm, hconj, hS, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ' hρ' => ?_
    rw [← hpow ρ hρ ρ' hρ']
    ring
  -- integrability of each term
  have hterm : ∀ ρ ρ', IntervalIntegrable
      (fun u : ℝ => ((w u : ℝ) : ℂ) * (u : ℂ) ^ (E ρ ρ')) volume a b := by
    intro ρ ρ'
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul
    · exact (Complex.continuous_ofReal.comp_continuousOn (by rwa [uIcc_of_le hab]))
    · exact (continuousOn_ofReal_cpow _).mono (fun u hu => hIcc u hu)
  have hcomplex : ((∫ u in a..b, w u * ‖∑ ρ ∈ Z, c ρ * (u : ℂ) ^ (β ρ)‖ ^ 2 : ℝ) : ℂ)
      = ∑ ρ ∈ Z, ∑ ρ' ∈ Z, c ρ * (starRingEnd ℂ) (c ρ')
          * ∫ u in a..b, ((w u : ℝ) : ℂ) * (u : ℂ) ^ (E ρ ρ') := by
    rw [← intervalIntegral.integral_ofReal, intervalIntegral.integral_congr hpt,
      intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [intervalIntegral.integral_finsetSum]
      · refine Finset.sum_congr rfl fun ρ' _ => ?_
        rw [intervalIntegral.integral_const_mul]
      · intro ρ' _; exact (hterm ρ ρ').const_mul _
    · intro ρ _
      have h := IntervalIntegrable.sum Z
        (fun ρ' _ => (hterm ρ ρ').const_mul (c ρ * (starRingEnd ℂ) (c ρ')))
      have heq : (fun x : ℝ => ∑ ρ' ∈ Z,
            c ρ * (starRingEnd ℂ) (c ρ') * (((w x : ℝ) : ℂ) * (x : ℂ) ^ (E ρ ρ')))
          = ∑ ρ' ∈ Z, (fun x : ℝ =>
            c ρ * (starRingEnd ℂ) (c ρ') * (((w x : ℝ) : ℂ) * (x : ℂ) ^ (E ρ ρ'))) := by
        funext x; rw [Finset.sum_apply]
      rw [heq]; exact h
  have hle : ∫ u in a..b, w u * ‖∑ ρ ∈ Z, c ρ * (u : ℂ) ^ (β ρ)‖ ^ 2
      ≤ ‖((∫ u in a..b, w u * ‖∑ ρ ∈ Z, c ρ * (u : ℂ) ^ (β ρ)‖ ^ 2 : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self _
  refine hle.trans ?_
  rw [hcomplex]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ' _ => ?_)
  rw [norm_mul, norm_mul, Complex.norm_conj]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have := hK ((β ρ).im - (β ρ').im)
  simpa [hE] using this

end PPF.RH.MS

namespace PPF.RH.MS

open Complex MeasureTheory intervalIntegral Set

theorem continuousOn_pow_sum (Z : Finset ℂ) (c e : ℂ → ℂ) :
    ContinuousOn (fun u : ℝ => ∑ ρ ∈ Z, c ρ * (u : ℂ) ^ (e ρ)) (Ioi 0) := by
  apply continuousOn_finsetSum
  intro ρ _
  exact continuousOn_const.mul (continuousOn_ofReal_cpow _)

theorem continuousOn_window_sum (Z : Finset ℂ) (c : ℂ → ℂ) {h : ℝ} (hh : 0 ≤ h) :
    ContinuousOn (fun x : ℝ => ∑ ρ ∈ Z, c ρ * ((((x + h : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ))
      (Ioi 0) := by
  apply continuousOn_finsetSum
  intro ρ _
  apply continuousOn_const.mul
  apply ContinuousOn.div_const
  apply ContinuousOn.sub
  · exact (continuousOn_ofReal_cpow ρ).comp (continuous_add_const h).continuousOn
      (fun x hx => by simp only [mem_Ioi] at hx ⊢; linarith)
  · exact continuousOn_ofReal_cpow ρ

theorem intervalIntegrable_of_continuousOn_Ioi {f : ℝ → ℝ} (hf : ContinuousOn f (Ioi 0))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : IntervalIntegrable f volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply hf.mono
  rw [uIcc_of_le hab]
  intro u hu; exact ha.trans_le hu.1

/-- The low-zero window as an integral of the derivative sum. -/
theorem window_sum_eq_integral (Z : Finset ℂ) (c : ℂ → ℂ) (hZ : ∀ ρ ∈ Z, ρ.re = 1 / 2)
    {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h) :
    ∑ ρ ∈ Z, c ρ * ((((x + h : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ)
      = ∫ u in x..x + h, ∑ ρ ∈ Z, c ρ * (u : ℂ) ^ (ρ - 1) := by
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun ρ hρ => ?_
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have hre : -1 < (ρ - 1).re := by
      rw [Complex.sub_re, hZ ρ hρ, Complex.one_re]; norm_num
    rw [integral_cpow (Or.inl hre), sub_add_cancel]
  · intro ρ _
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.mul
    apply (continuousOn_ofReal_cpow _).mono
    rw [uIcc_of_le (by linarith)]
    intro u hu; exact hx.trans_le hu.1

end PPF.RH.MS
