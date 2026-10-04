import PPF.RH.Defs

/-!
# Helpers for K1: derivatives and bounds of the polynomial weight `bump X`

`bump X = bp X ^ 2` with `bp X u = (u − X/2)(4X − u)/X²`; `b1 = bump′`, `b2 = bump″`.
`integral_bump_cpow_eq` is the double integration by parts, done as one FTC.
-/

namespace PPF.RH.KZ

open Complex

noncomputable def bp (X u : ℝ) : ℝ := (u - X / 2) * (4 * X - u) / X ^ 2
noncomputable def bpd (X u : ℝ) : ℝ := (9 / 2 * X - 2 * u) / X ^ 2
noncomputable def b1 (X u : ℝ) : ℝ := 2 * bp X u * bpd X u
noncomputable def b2 (X u : ℝ) : ℝ := 2 * bpd X u ^ 2 - 4 * bp X u / X ^ 2

lemma bump_eq_bp_sq (X u : ℝ) : bump X u = bp X u ^ 2 := rfl

lemma hasDerivAt_bp (X u : ℝ) : HasDerivAt (bp X) (bpd X u) u := by
  have h := (((hasDerivAt_id u).sub_const (X / 2)).mul
    ((hasDerivAt_const u (4 * X)).sub (hasDerivAt_id u))).div_const (X ^ 2)
  refine HasDerivAt.congr_deriv (f := bp X) h ?_
  unfold bpd
  simp only [Pi.sub_apply, id]
  ring

lemma hasDerivAt_bpd (X u : ℝ) : HasDerivAt (bpd X) (-2 / X ^ 2) u := by
  have h := ((hasDerivAt_const u (9 / 2 * X)).sub ((hasDerivAt_id u).const_mul 2)).div_const (X ^ 2)
  refine HasDerivAt.congr_deriv (f := bpd X) h ?_
  ring

lemma hasDerivAt_bump (X u : ℝ) : HasDerivAt (bump X) (b1 X u) u := by
  have h := (hasDerivAt_bp X u).pow 2
  have : bump X = fun u => bp X u ^ 2 := rfl
  rw [this]
  refine h.congr_deriv ?_
  unfold b1
  push_cast
  ring

lemma hasDerivAt_b1 (X u : ℝ) : HasDerivAt (b1 X) (b2 X u) u := by
  have h := ((hasDerivAt_bp X u).const_mul 2).mul (hasDerivAt_bpd X u)
  have : b1 X = fun u => 2 * bp X u * bpd X u := rfl
  rw [this]
  refine h.congr_deriv ?_
  unfold b2
  ring


lemma bp_bounds {X u : ℝ} (hX : 0 < X) (h1 : X / 2 ≤ u) (h2 : u ≤ 4 * X) :
    0 ≤ bp X u ∧ bp X u ≤ 49 / 16 := by
  unfold bp
  have hX2 : 0 < X ^ 2 := by positivity
  constructor
  · apply div_nonneg _ hX2.le
    nlinarith
  · rw [div_le_iff₀ hX2]
    nlinarith [sq_nonneg (u - 9 / 4 * X)]

lemma bump_le_ten {X u : ℝ} (hX : 0 < X) (h1 : X / 2 ≤ u) (h2 : u ≤ 4 * X) :
    bump X u ≤ 10 := by
  rw [bump_eq_bp_sq]
  obtain ⟨h0, h49⟩ := bp_bounds hX h1 h2
  nlinarith

lemma abs_b2_le {X u : ℝ} (hX : 0 < X) (h1 : X / 2 ≤ u) (h2 : u ≤ 4 * X) :
    |b2 X u| ≤ 25 / X ^ 2 := by
  have hX2 : 0 < X ^ 2 := by positivity
  have hX4 : 0 < X ^ 4 := by positivity
  have key : b2 X u = (12 * (u - 9 / 4 * X) ^ 2 - 49 / 4 * X ^ 2) / X ^ 4 := by
    unfold b2 bp bpd
    field_simp
    ring
  rw [key, abs_div, abs_of_pos hX4, div_le_div_iff₀ hX4 hX2]
  have hv : (u - 9 / 4 * X) ^ 2 ≤ (7 / 4 * X) ^ 2 := by
    apply sq_le_sq' <;> nlinarith
  have hN : |12 * (u - 9 / 4 * X) ^ 2 - 49 / 4 * X ^ 2| ≤ 25 * X ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (u - 9 / 4 * X)]
  calc |12 * (u - 9 / 4 * X) ^ 2 - 49 / 4 * X ^ 2| * X ^ 2 ≤ (25 * X ^ 2) * X ^ 2 :=
        mul_le_mul_of_nonneg_right hN hX2.le
    _ = 25 * X ^ 4 := by ring

lemma bp_left (X : ℝ) : bp X (X / 2) = 0 := by unfold bp; ring
lemma bp_right (X : ℝ) : bp X (4 * X) = 0 := by unfold bp; ring

lemma rpow_bound_low {α X u : ℝ} (hα : -1 ≤ α) (hX : 0 < X) (h1 : X / 2 ≤ u) (h2 : u ≤ 4 * X) :
    u ^ α ≤ ((4 : ℝ) ^ α + 2) * X ^ α := by
  have hu : 0 < u := by linarith
  have hq : u = (u / X) * X := by field_simp
  have hq0 : 0 < u / X := div_pos hu hX
  rw [hq, Real.mul_rpow hq0.le hX.le]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hX.le _)
  have h4 : (0 : ℝ) ≤ (4 : ℝ) ^ α := Real.rpow_nonneg (by norm_num) _
  rcases le_or_gt 0 α with hα0 | hα0
  · have : (u / X) ^ α ≤ (4 : ℝ) ^ α := by
      apply Real.rpow_le_rpow hq0.le _ hα0
      rw [div_le_iff₀ hX]; linarith
    linarith
  · have hlow : (1 / 2 : ℝ) ≤ u / X := by rw [le_div_iff₀ hX]; linarith
    have : (u / X) ^ α ≤ (1 / 2 : ℝ) ^ α := Real.rpow_le_rpow_of_nonpos (by norm_num) hlow hα0.le
    have h2' : (1 / 2 : ℝ) ^ α ≤ 2 := by
      rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
      calc (2 : ℝ) ^ (-α) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := Real.rpow_one 2
    linarith

lemma rpow_bound_high {α X u : ℝ} (hα : -1 ≤ α) (hX : 0 < X) (h1 : X / 2 ≤ u) (h2 : u ≤ 4 * X) :
    u ^ (α + 2) ≤ (4 : ℝ) ^ (α + 2) * X ^ (α + 2) := by
  have hu : 0 < u := by linarith
  rw [← Real.mul_rpow (by norm_num) hX.le]
  exact Real.rpow_le_rpow hu.le h2 (by linarith)


lemma continuous_bump (X : ℝ) : Continuous (bump X) := by
  unfold bump; fun_prop

lemma continuous_b2 (X : ℝ) : Continuous (b2 X) := by
  unfold b2 bp bpd; fun_prop

/-- Two integrations by parts, packaged as one application of the FTC. -/
lemma integral_bump_cpow_eq {X : ℝ} (hX : 0 < X) {s : ℂ} (hs1 : s ≠ -1) (hs2 : s + 1 ≠ -1) :
    ∫ u in (X / 2)..(4 * X), ((bump X u : ℝ) : ℂ) * (u : ℂ) ^ s
      = ∫ u in (X / 2)..(4 * X),
          ((b2 X u : ℝ) : ℂ) * ((u : ℂ) ^ ((s + 1) + 1) / ((s + 1) + 1)) / (s + 1) := by
  set F1 : ℝ → ℂ := fun u => (u : ℂ) ^ (s + 1) / (s + 1) with hF1def
  set F2 : ℝ → ℂ := fun u => (u : ℂ) ^ ((s + 1) + 1) / ((s + 1) + 1) with hF2def
  set Φ : ℝ → ℂ := fun u => ((bump X u : ℝ) : ℂ) * F1 u - ((b1 X u : ℝ) : ℂ) * F2 u / (s + 1)
    with hΦdef
  have hle : X / 2 ≤ 4 * X := by linarith
  have hpos : ∀ u ∈ Set.uIcc (X / 2) (4 * X), 0 < u := by
    intro u hu
    rw [Set.uIcc_of_le hle] at hu
    linarith [hu.1]
  have hderiv : ∀ u ∈ Set.uIcc (X / 2) (4 * X), HasDerivAt Φ
      (((bump X u : ℝ) : ℂ) * (u : ℂ) ^ s - ((b2 X u : ℝ) : ℂ) * F2 u / (s + 1)) u := by
    intro u hu
    have hu0 : u ≠ 0 := (hpos u hu).ne'
    have hB := (hasDerivAt_bump X u).ofReal_comp
    have hB1 := (hasDerivAt_b1 X u).ofReal_comp
    have hF1 : HasDerivAt F1 ((u : ℂ) ^ s) u := hasDerivAt_ofReal_cpow_const' hu0 hs1
    have hF2 : HasDerivAt F2 ((u : ℂ) ^ (s + 1)) u := hasDerivAt_ofReal_cpow_const' hu0 hs2
    have h := (hB.mul hF1).sub ((hB1.mul hF2).div_const (s + 1))
    refine h.congr_deriv ?_
    simp only [hF1def]
    ring
  have hint : IntervalIntegrable
      (fun u => ((bump X u : ℝ) : ℂ) * (u : ℂ) ^ s - ((b2 X u : ℝ) : ℂ) * F2 u / (s + 1))
      MeasureTheory.volume (X / 2) (4 * X) := by
    apply ContinuousOn.intervalIntegrable
    intro u hu
    have hu0 : u ≠ 0 := (hpos u hu).ne'
    apply ContinuousAt.continuousWithinAt
    have c1 : ContinuousAt (fun u : ℝ => ((bump X u : ℝ) : ℂ)) u :=
      (Complex.continuous_ofReal.comp (continuous_bump X)).continuousAt
    have c2 : ContinuousAt (fun u : ℝ => ((b2 X u : ℝ) : ℂ)) u :=
      (Complex.continuous_ofReal.comp (continuous_b2 X)).continuousAt
    have c3 : ContinuousAt (fun u : ℝ => (u : ℂ) ^ s) u :=
      continuousAt_ofReal_cpow_const u s (Or.inr hu0)
    have c4 : ContinuousAt F2 u := (hasDerivAt_ofReal_cpow_const' hu0 hs2).continuousAt
    exact (c1.mul c3).sub ((c2.mul c4).div_const _)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hΦa : Φ (X / 2) = 0 := by
    simp only [hΦdef, bump_eq_bp_sq, b1, bp_left]; simp
  have hΦb : Φ (4 * X) = 0 := by
    simp only [hΦdef, bump_eq_bp_sq, b1, bp_right]; simp
  have hi1 : IntervalIntegrable (fun u => ((bump X u : ℝ) : ℂ) * (u : ℂ) ^ s)
      MeasureTheory.volume (X / 2) (4 * X) := by
    apply ContinuousOn.intervalIntegrable
    intro u hu
    apply ContinuousAt.continuousWithinAt
    exact (Complex.continuous_ofReal.comp (continuous_bump X)).continuousAt.mul
      (continuousAt_ofReal_cpow_const u s (Or.inr (hpos u hu).ne'))
  have hi2 : IntervalIntegrable (fun u => ((b2 X u : ℝ) : ℂ) * F2 u / (s + 1))
      MeasureTheory.volume (X / 2) (4 * X) := by
    apply ContinuousOn.intervalIntegrable
    intro u hu
    apply ContinuousAt.continuousWithinAt
    exact ((Complex.continuous_ofReal.comp (continuous_b2 X)).continuousAt.mul
      (hasDerivAt_ofReal_cpow_const' (hpos u hu).ne' hs2).continuousAt).div_const _
  rw [hΦa, hΦb, sub_zero, intervalIntegral.integral_sub hi1 hi2] at hFTC
  exact sub_eq_zero.mp hFTC


lemma one_le_bump' {X u : ℝ} (hX : 0 < X) (h1 : X ≤ u) (h2 : u ≤ 3 * X) :
    1 ≤ bump X u := by
  rw [bump_eq_bp_sq]
  have hX2 : 0 < X ^ 2 := by positivity
  have hb : 3 / 2 ≤ bp X u := by
    unfold bp
    rw [le_div_iff₀ hX2]
    nlinarith
  nlinarith

theorem norm_integral_bump_cpow_le' (α : ℝ) (hα : -1 ≤ α) :
    ∃ C : ℝ, ∀ X : ℝ, 1 ≤ X → ∀ τ : ℝ,
      ‖∫ u in (X / 2)..(4 * X), ((bump X u : ℝ) : ℂ) * ((u : ℂ) ^ ((α : ℂ) + τ * I))‖
        ≤ C * X ^ (α + 1) / (1 + τ ^ 2) := by
  refine ⟨70 * ((4 : ℝ) ^ α + 2) + 175 * (4 : ℝ) ^ (α + 2), ?_⟩
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

end PPF.RH.KZ
