import PPF.RH.KZ.Bump

/-!
# Explicit K1: the bump kernel with its explicit constant

The proof of `PPF.RH.KZ.norm_integral_bump_cpow_le'` with its witness
`70(4^α+2) + 175·4^{α+2}` stated explicitly.
-/

namespace PPF.Explicit.MSx

open Complex PPF.RH PPF.RH.KZ

theorem kernel_explicit' (α : ℝ) (hα : -1 ≤ α) :
    ∀ X : ℝ, 1 ≤ X → ∀ τ : ℝ,
      ‖∫ u in (X / 2)..(4 * X), ((bump X u : ℝ) : ℂ) * ((u : ℂ) ^ ((α : ℂ) + τ * I))‖
        ≤ (70 * ((4 : ℝ) ^ α + 2) + 175 * (4 : ℝ) ^ (α + 2)) * X ^ (α + 1) / (1 + τ ^ 2) := by
  intro X hX τ
  have hX0 : 0 < X := by linarith
  set s : ℂ := (α : ℂ) + τ * I with hsdef
  have hsre : s.re = α := by simp [hsdef]
  have hXa : 0 ≤ X ^ (α + 1) := Real.rpow_nonneg hX0.le _
  have hK : 0 ≤ (4 : ℝ) ^ α := Real.rpow_nonneg (by norm_num) _
  have hK2 : 0 ≤ (4 : ℝ) ^ (α + 2) := Real.rpow_nonneg (by norm_num) _
  have hle : X / 2 ≤ 4 * X := by linarith
  have hlen : |4 * X - X / 2| = 7 / 2 * X := by
    rw [abs_of_pos (by linarith)]; ring
  have hmem : ∀ u ∈ Set.uIoc (X / 2) (4 * X), X / 2 ≤ u ∧ u ≤ 4 * X := by
    intro u hu
    rw [Set.uIoc_of_le hle] at hu
    exact ⟨hu.1.le, hu.2⟩
  have hτ2pos : 0 < 1 + τ ^ 2 := by positivity
  rcases le_or_gt |τ| 1 with hτ | hτ
  · have hbound : ∀ u ∈ Set.uIoc (X / 2) (4 * X),
        ‖((bump X u : ℝ) : ℂ) * (u : ℂ) ^ s‖ ≤ 10 * (((4 : ℝ) ^ α + 2) * X ^ α) := by
      intro u hu
      obtain ⟨hu1, hu2⟩ := hmem u hu
      have hupos : 0 < u := by linarith
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ bump X u by unfold bump; positivity),
        Complex.norm_cpow_eq_rpow_re_of_pos hupos, hsre]
      exact mul_le_mul (bump_le_ten hX0 hu1 hu2) (rpow_bound_low hα hX0 hu1 hu2)
        (Real.rpow_nonneg hupos.le _) (by norm_num)
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rw [hlen] at h1
    have hXα : X ^ α * X = X ^ (α + 1) := (Real.rpow_add_one hX0.ne' α).symm
    have hτ2 : τ ^ 2 ≤ 1 := by
      have := sq_abs τ
      nlinarith [abs_nonneg τ]
    calc ‖∫ u in (X / 2)..(4 * X), ((bump X u : ℝ) : ℂ) * (u : ℂ) ^ s‖
        ≤ 10 * (((4 : ℝ) ^ α + 2) * X ^ α) * (7 / 2 * X) := h1
      _ = 35 * ((4 : ℝ) ^ α + 2) * X ^ (α + 1) := by rw [← hXα]; ring
      _ ≤ (70 * ((4 : ℝ) ^ α + 2)) * X ^ (α + 1) / (1 + τ ^ 2) := by
          rw [le_div_iff₀ hτ2pos]
          have : 0 ≤ ((4 : ℝ) ^ α + 2) * X ^ (α + 1) := by positivity
          nlinarith
      _ ≤ (70 * ((4 : ℝ) ^ α + 2) + 175 * (4 : ℝ) ^ (α + 2)) * X ^ (α + 1) / (1 + τ ^ 2) := by
          gcongr
          linarith
  · have hτpos : 0 < |τ| := by linarith
    have hs1 : s ≠ -1 := by
      intro h
      have := congrArg Complex.im h
      simp [hsdef] at this
      rw [this, abs_zero] at hτ
      linarith
    have hs2 : s + 1 ≠ -1 := by
      intro h
      have := congrArg Complex.im h
      simp [hsdef] at this
      rw [this, abs_zero] at hτ
      linarith
    have hn1 : |τ| ≤ ‖s + 1‖ := by
      have := Complex.abs_im_le_norm (s + 1)
      simpa [hsdef] using this
    have hn2 : |τ| ≤ ‖s + 1 + 1‖ := by
      have := Complex.abs_im_le_norm (s + 1 + 1)
      simpa [hsdef] using this
    rw [integral_bump_cpow_eq hX0 hs1 hs2]
    set M : ℝ := 25 / X ^ 2 * ((4 : ℝ) ^ (α + 2) * X ^ (α + 2) / |τ|) / |τ| with hMdef
    have hbound : ∀ u ∈ Set.uIoc (X / 2) (4 * X),
        ‖((b2 X u : ℝ) : ℂ) * ((u : ℂ) ^ ((s + 1) + 1) / ((s + 1) + 1)) / (s + 1)‖ ≤ M := by
      intro u hu
      obtain ⟨hu1, hu2⟩ := hmem u hu
      have hupos : 0 < u := by linarith
      have hre : ((s + 1) + 1).re = α + 2 := by simp [hsdef]; ring
      rw [norm_div, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos hupos, hre]
      have hb2 := abs_b2_le hX0 hu1 hu2
      have hu3 := rpow_bound_high hα hX0 hu1 hu2
      have hpow0 : 0 ≤ u ^ (α + 2) := Real.rpow_nonneg hupos.le _
      rw [hMdef]
      gcongr
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rw [hlen] at h1
    have hXα : X ^ (α + 2) = X ^ (α + 1) * X := by
      rw [show α + 2 = (α + 1) + 1 by ring, Real.rpow_add_one hX0.ne']
    have hττ : |τ| * |τ| = τ ^ 2 := by rw [← sq, sq_abs]
    have hτ2 : 1 < τ ^ 2 := by nlinarith
    calc _ ≤ M * (7 / 2 * X) := h1
      _ = 175 / 2 * (4 : ℝ) ^ (α + 2) * X ^ (α + 1) / τ ^ 2 := by
          rw [hMdef, hXα, ← hττ]
          field_simp
          norm_num
      _ ≤ (175 * (4 : ℝ) ^ (α + 2)) * X ^ (α + 1) / (1 + τ ^ 2) := by
          rw [div_le_div_iff₀ (by positivity) hτ2pos]
          have : 0 ≤ (4 : ℝ) ^ (α + 2) * X ^ (α + 1) := by positivity
          nlinarith
      _ ≤ (70 * ((4 : ℝ) ^ α + 2) + 175 * (4 : ℝ) ^ (α + 2)) * X ^ (α + 1) / (1 + τ ^ 2) := by
          gcongr
          nlinarith

end PPF.Explicit.MSx
