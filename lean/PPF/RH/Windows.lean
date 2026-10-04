import PPF.RH.ExplicitFormula
import PPF.RH.MeanSquare

/-!
# B1–B3 and the final assembly

* B1 (`sum_eq_integral_theta`): for integer `h`, `θ(x+h) − θ(x)` is constant on each
  `[n, n+1)` (`Chebyshev.theta_eq_theta_coe_floor`), so the frozen discrete sum is
  an integral.
* B2 (`integral_psi_sub_theta_sq_le`): `D = ψ − θ` is monotone with
  `D(y) ≤ 2√y log y` (`Chebyshev.psi_sub_theta_le`), and
  `∫_X^{2X} (D(x+h) − D(x)) dx ≤ h D(3X)`.
* B3 (`integral_psi_window_sq_le`): E3 at `y = x` and `y = x + h` with `T = X²`
  leaves `−S(x)` plus `O(log² X)`; then K4.
* Assembly: `(θ-window − h)² ≤ 2(ψ-window − h)² + 2(D-window)²`; for each `θ > 0`,
  `X^θ ≥ log² X` for large `X`; small `X` is a finite check absorbed in `C`.
-/

namespace PPF.RH.Win

open MeasureTheory Set intervalIntegral

lemma floor_add_nat {x : ℝ} {n h : ℕ} (hx : x ∈ Ico (n : ℝ) (n + 1)) :
    ⌊x + h⌋₊ = n + h := by
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [Nat.floor_eq_iff (by linarith [hx.1, (Nat.cast_nonneg h : (0:ℝ) ≤ h)])]
  push_cast
  constructor <;> linarith [hx.1, hx.2]

lemma floor_of_mem {x : ℝ} {n : ℕ} (hx : x ∈ Ico (n : ℝ) (n + 1)) : ⌊x⌋₊ = n := by
  rw [Nat.floor_eq_iff (by linarith [hx.1, (Nat.cast_nonneg n : (0:ℝ) ≤ n)])]
  exact ⟨hx.1, hx.2⟩

lemma window_eq_on (h n : ℕ) {x : ℝ} (hx : x ∈ Ioo (n : ℝ) (n + 1)) :
    (Chebyshev.theta (x + h) - Chebyshev.theta x - h) ^ 2
      = (Chebyshev.theta ((n + h : ℕ) : ℝ) - Chebyshev.theta n - h) ^ 2 := by
  have hx' : x ∈ Ico (n : ℝ) (n + 1) := ⟨hx.1.le, hx.2⟩
  rw [Chebyshev.theta_eq_theta_coe_floor (x + h), Chebyshev.theta_eq_theta_coe_floor x,
    floor_add_nat hx', floor_of_mem hx']

lemma integral_piece (h n : ℕ) :
    ∫ x in (n : ℝ)..(n + 1), (Chebyshev.theta (x + h) - Chebyshev.theta x - h) ^ 2
      = (Chebyshev.theta ((n + h : ℕ) : ℝ) - Chebyshev.theta n - h) ^ 2 := by
  rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo,
    setIntegral_congr_fun measurableSet_Ioo (fun x hx => window_eq_on h n hx)]
  simp

lemma intervalIntegrable_piece (h n : ℕ) :
    IntervalIntegrable (fun x : ℝ => (Chebyshev.theta (x + h) - Chebyshev.theta x - h) ^ 2)
      volume n (n + 1) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith),
    integrableOn_Ioc_iff_integrableOn_Ioo]
  exact (integrableOn_const (by simp)).congr_fun
    (fun x hx => (window_eq_on h n hx).symm) measurableSet_Ioo

/-- `|g x| ≤ |g a| + |g b|` for monotone `g` and `x ∈ [a, b]`. -/
lemma abs_le_of_monotone {g : ℝ → ℝ} (hg : Monotone g) {a b x : ℝ} (hx : x ∈ Icc a b) :
    |g x| ≤ |g a| + |g b| := by
  have h1 := hg hx.1
  have h2 := hg hx.2
  exact abs_le.mpr ⟨by linarith [neg_abs_le (g a), abs_nonneg (g b)],
    by linarith [le_abs_self (g b), abs_nonneg (g a)]⟩

/-- Squares of differences of monotone functions are interval integrable. -/
lemma intervalIntegrable_sq_of_monotone {g₁ g₂ : ℝ → ℝ} (h₁ : Monotone g₁) (h₂ : Monotone g₂)
    (c : ℝ) {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable (fun x => (g₁ x - g₂ x - c) ^ 2) volume a b := by
  have hm : Measurable (fun x => (g₁ x - g₂ x - c) ^ 2) :=
    ((h₁.measurable.sub h₂.measurable).sub measurable_const).pow_const 2
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  refine IntegrableOn.of_bound (by simp) hm.aestronglyMeasurable
    ((|g₁ a| + |g₁ b| + (|g₂ a| + |g₂ b|) + |c|) ^ 2) ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  refine Filter.Eventually.of_forall (fun x hx => ?_)
  rw [Real.norm_eq_abs, abs_pow]
  apply pow_le_pow_left₀ (abs_nonneg _)
  calc |g₁ x - g₂ x - c| ≤ |g₁ x| + |g₂ x| + |c| := by
        have := abs_sub (g₁ x - g₂ x) c
        have := abs_sub (g₁ x) (g₂ x)
        linarith
    _ ≤ |g₁ a| + |g₁ b| + (|g₂ a| + |g₂ b|) + |c| := by
        gcongr
        · exact abs_le_of_monotone h₁ hx
        · exact abs_le_of_monotone h₂ hx

/-- `ψ − θ` is monotone: it is a sum of `Λ` over non-primes. -/
lemma psiSubTheta_mono : Monotone (fun x : ℝ => Chebyshev.psi x - Chebyshev.theta x) := by
  intro x y hxy
  simp only [Chebyshev.psi_sub_theta_eq_sum_not_prime]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
    exact ⟨⟨hn.1.1, hn.1.2.trans (Nat.floor_le_floor hxy)⟩, hn.2⟩
  · intro n _ _
    exact ArithmeticFunction.vonMangoldt_nonneg

/-- The zero-sum window of K4. -/
noncomputable def zsum (T h x : ℝ) : ℂ :=
  ∑ ρ ∈ zetaZeros T, (mult ρ : ℂ) * ((((x + h : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ)

lemma zsum_continuousOn {T h X : ℝ} (hX : 0 < X) (hh : 0 ≤ h) :
    ContinuousOn (fun x => zsum T h x) (Ici X) := by
  unfold zsum
  apply continuousOn_finsetSum
  intro ρ _ x hx
  have hx0 : 0 < x := lt_of_lt_of_le hX hx
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.mul continuousAt_const
  apply ContinuousAt.div_const
  apply ContinuousAt.sub
  · have hc := Complex.continuousAt_ofReal_cpow_const (x + h) ρ (Or.inr (by linarith : x + h ≠ 0))
    exact hc.comp (f := fun x : ℝ => x + h) (continuousAt_id.add continuousAt_const)
  · exact Complex.continuousAt_ofReal_cpow_const x ρ (Or.inr hx0.ne')

lemma log_three_mul_le {X : ℝ} (hX : 2 ≤ X) : Real.log (3 * X) ≤ 3 * Real.log X := by
  have hX0 : 0 < X := by linarith
  rw [Real.log_mul (by norm_num) hX0.ne']
  have : Real.log 3 ≤ Real.log (X ^ 2) := Real.log_le_log (by norm_num) (by nlinarith)
  rw [Real.log_pow] at this
  push_cast at this
  linarith

end PPF.RH.Win

namespace PPF.RH

open Complex MeasureTheory Set intervalIntegral

/-- B1. -/
theorem sum_eq_integral_theta (X h : ℕ) :
    ∑ n ∈ Finset.Ico X (2 * X),
        (Chebyshev.theta ((n + h : ℕ) : ℝ) - Chebyshev.theta n - h) ^ 2
      = ∫ x in (X : ℝ)..(2 * X), (Chebyshev.theta (x + h) - Chebyshev.theta x - h) ^ 2 := by
  have key := intervalIntegral.sum_integral_adjacent_intervals (μ := MeasureTheory.volume)
    (a := fun k : ℕ => ((X + k : ℕ) : ℝ)) (n := X)
    (f := fun x : ℝ => (Chebyshev.theta (x + h) - Chebyshev.theta x - h) ^ 2)
    (fun k _ => by simpa [Nat.cast_add, add_assoc] using Win.intervalIntegrable_piece h (X + k))
  rw [Finset.sum_Ico_eq_sum_range, show 2 * X - X = X by omega]
  have h2 : ((X + X : ℕ) : ℝ) = 2 * (X : ℝ) := by push_cast; ring
  rw [Nat.add_zero, h2] at key
  rw [← key]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have := Win.integral_piece h (X + k)
  rw [show ((X + (k + 1) : ℕ) : ℝ) = ((X + k : ℕ) : ℝ) + 1 by push_cast; ring, this]

/-- B2 (unconditional). -/
theorem integral_psi_sub_theta_sq_le :
    ∃ C : ℝ, ∀ X h : ℝ, 2 ≤ X → 0 ≤ h → h ≤ X →
      ∫ x in X..(2 * X),
          ((Chebyshev.psi (x + h) - Chebyshev.theta (x + h))
            - (Chebyshev.psi x - Chebyshev.theta x)) ^ 2
        ≤ C * h * X * Real.log X ^ 2 := by
  refine ⟨108, fun X h hX hh hhX => ?_⟩
  set D : ℝ → ℝ := fun x => Chebyshev.psi x - Chebyshev.theta x with hD
  have hDm : Monotone D := Win.psiSubTheta_mono
  have hD0 : ∀ x, 0 ≤ D x := fun x => sub_nonneg.mpr (Chebyshev.theta_le_psi x)
  have hDh : Monotone (fun x => D (x + h)) := fun a b hab => hDm (by linarith)
  have hXpos : 0 < X := by linarith
  set B := D (3 * X) with hBdef
  have hW0 : ∀ x, 0 ≤ D (x + h) - D x := fun x => sub_nonneg.mpr (hDm (by linarith))
  have hWB : ∀ x ∈ Icc X (2 * X), D (x + h) - D x ≤ B := fun x hx => by
    have := hDm (show x + h ≤ 3 * X by linarith [hx.2])
    linarith [hD0 x]
  have hint_W : IntervalIntegrable (fun x => D (x + h) - D x) volume X (2 * X) :=
    hDh.intervalIntegrable.sub hDm.intervalIntegrable
  have hint_sq : IntervalIntegrable (fun x => (D (x + h) - D x) ^ 2) volume X (2 * X) := by
    simpa using Win.intervalIntegrable_sq_of_monotone hDh hDm 0 (by linarith : X ≤ 2 * X)
  have hstep1 : ∫ x in X..(2 * X), (D (x + h) - D x) ^ 2
      ≤ ∫ x in X..(2 * X), B * (D (x + h) - D x) := by
    apply intervalIntegral.integral_mono_on (by linarith) hint_sq (hint_W.const_mul B)
    intro x hx
    have h0 := hW0 x
    have h1 := hWB x hx
    nlinarith
  have hstep2 : ∫ x in X..(2 * X), (D (x + h) - D x) ≤ h * B := by
    rw [intervalIntegral.integral_sub hDh.intervalIntegrable hDm.intervalIntegrable,
      intervalIntegral.integral_comp_add_right (fun x => D x) h]
    have e1 := intervalIntegral.integral_add_adjacent_intervals
      (hDm.intervalIntegrable (μ := volume) (a := X) (b := X + h))
      (hDm.intervalIntegrable (μ := volume) (a := X + h) (b := 2 * X + h))
    have e2 := intervalIntegral.integral_add_adjacent_intervals
      (hDm.intervalIntegrable (μ := volume) (a := X) (b := 2 * X))
      (hDm.intervalIntegrable (μ := volume) (a := 2 * X) (b := 2 * X + h))
    have hpos : 0 ≤ ∫ x in X..(X + h), D x :=
      intervalIntegral.integral_nonneg (by linarith) (fun x _ => hD0 x)
    have hle : ∫ x in (2 * X)..(2 * X + h), D x ≤ ∫ x in (2 * X)..(2 * X + h), B :=
      intervalIntegral.integral_mono_on (by linarith) hDm.intervalIntegrable
        (intervalIntegrable_const (μ := volume)) (fun x hx => hDm (by linarith [hx.2]))
    rw [intervalIntegral.integral_const, smul_eq_mul,
      show 2 * X + h - 2 * X = h by ring] at hle
    linarith
  have hB : B ≤ 2 * Real.sqrt (3 * X) * Real.log (3 * X) :=
    Chebyshev.psi_sub_theta_le (by linarith)
  have hB0 : 0 ≤ B := hD0 _
  have hlog0 : 0 ≤ Real.log (3 * X) := Real.log_nonneg (by linarith)
  have hlog := Win.log_three_mul_le hX
  calc ∫ x in X..(2 * X),
          ((Chebyshev.psi (x + h) - Chebyshev.theta (x + h))
            - (Chebyshev.psi x - Chebyshev.theta x)) ^ 2
        = ∫ x in X..(2 * X), (D (x + h) - D x) ^ 2 := rfl
    _ ≤ ∫ x in X..(2 * X), B * (D (x + h) - D x) := hstep1
    _ = B * ∫ x in X..(2 * X), (D (x + h) - D x) := intervalIntegral.integral_const_mul _ _
    _ ≤ B * (h * B) := mul_le_mul_of_nonneg_left hstep2 hB0
    _ = h * B ^ 2 := by ring
    _ ≤ h * (2 * Real.sqrt (3 * X) * Real.log (3 * X)) ^ 2 := by gcongr
    _ = h * (12 * X * Real.log (3 * X) ^ 2) := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith)]; ring
    _ ≤ h * (12 * X * (3 * Real.log X) ^ 2) := by gcongr
    _ = 108 * h * X * Real.log X ^ 2 := by ring

/-- B3. -/
theorem integral_psi_window_sq_le (hRH : RiemannHypothesis) :
    ∃ C X₀ : ℝ, ∀ X h : ℝ, X₀ ≤ X → Real.log X ^ 2 ≤ h → h ≤ X →
      ∫ x in X..(2 * X), (Chebyshev.psi (x + h) - Chebyshev.psi x - h) ^ 2
        ≤ C * h * X * Real.log X ^ 2 := by
  obtain ⟨C₃, hE⟩ := explicit_formula_RH hRH
  obtain ⟨C₄, X₄, hK⟩ := mean_square_zero_sum_le hRH
  set C₃' := max C₃ 0 with hC₃'
  set C₄' := max C₄ 0 with hC₄'
  set K := 32 * C₃' with hKdef
  have hK0 : 0 ≤ K := by positivity
  refine ⟨8 * K ^ 2 + 2 * C₄', max X₄ 100, fun X h hX hlh hhX => ?_⟩
  have hX100 : 100 ≤ X := le_trans (le_max_right _ _) hX
  have hX4 : X₄ ≤ X := le_trans (le_max_left _ _) hX
  have hXpos : 0 < X := by linarith
  have hlogX : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    have := Real.exp_one_lt_d9
    linarith
  have hh1 : 1 ≤ h := le_trans (by nlinarith) hlh
  have hh0 : 0 ≤ h := by linarith
  -- the explicit-formula error at heights `y ∈ [X, 3X]`
  have herr : ∀ y : ℝ, X ≤ y → y ≤ 3 * X →
      ‖((Chebyshev.psi y : ℝ) : ℂ) - y
          + ∑ ρ ∈ zetaZeros (X ^ 2), (mult ρ : ℂ) * ((y : ℂ) ^ ρ / ρ)‖
        ≤ K * Real.log X ^ 2 := by
    intro y hy1 hy2
    have hy0 : 0 < y := by linarith
    have hT : (2 : ℝ) ≤ X ^ 2 := by nlinarith
    have h1 := hE y (X ^ 2) (by linarith) hT
    have hL0 : 0 ≤ Real.log (X ^ 2 * y) := Real.log_nonneg (by nlinarith)
    have hL : Real.log (X ^ 2 * y) ≤ 4 * Real.log X := by
      rw [Real.log_mul (by positivity) hy0.ne', Real.log_pow]
      have := Real.log_le_log hy0 hy2
      have h3 := Win.log_three_mul_le (show (2 : ℝ) ≤ X by linarith)
      push_cast
      have : Real.log (3 * X) ≤ 2 * Real.log X := by
        rw [Real.log_mul (by norm_num) hXpos.ne']
        have : Real.log 3 ≤ Real.log X := Real.log_le_log (by norm_num) (by linarith)
        linarith
      linarith
    have hL2 : Real.log (X ^ 2 * y) ^ 2 ≤ 16 * Real.log X ^ 2 := by nlinarith
    have hyT : y / X ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    have hbr : y * Real.log (X ^ 2 * y) ^ 2 / X ^ 2 + Real.log (X ^ 2 * y) ^ 2
        ≤ 32 * Real.log X ^ 2 := by
      have : y * Real.log (X ^ 2 * y) ^ 2 / X ^ 2
          = (y / X ^ 2) * Real.log (X ^ 2 * y) ^ 2 := by ring
      rw [this]
      have := mul_le_of_le_one_left (sq_nonneg (Real.log (X ^ 2 * y))) hyT
      have : 0 ≤ y / X ^ 2 := by positivity
      nlinarith
    have hbr0 : 0 ≤ y * Real.log (X ^ 2 * y) ^ 2 / X ^ 2 + Real.log (X ^ 2 * y) ^ 2 := by
      positivity
    calc _ ≤ C₃ * (y * Real.log (X ^ 2 * y) ^ 2 / X ^ 2 + Real.log (X ^ 2 * y) ^ 2) := h1
      _ ≤ C₃' * (y * Real.log (X ^ 2 * y) ^ 2 / X ^ 2 + Real.log (X ^ 2 * y) ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hbr0
      _ ≤ C₃' * (32 * Real.log X ^ 2) :=
          mul_le_mul_of_nonneg_left hbr (le_max_right _ _)
      _ = K * Real.log X ^ 2 := by rw [hKdef]; ring
  -- pointwise bound on the window
  have hpt : ∀ x ∈ Icc X (2 * X), (Chebyshev.psi (x + h) - Chebyshev.psi x - h) ^ 2
      ≤ 8 * K ^ 2 * Real.log X ^ 4 + 2 * ‖Win.zsum (X ^ 2) h x‖ ^ 2 := by
    intro x hx
    set Z : ℝ → ℂ := fun y => ∑ ρ ∈ zetaZeros (X ^ 2), (mult ρ : ℂ) * ((y : ℂ) ^ ρ / ρ)
      with hZ
    have hZd : Z (x + h) - Z x = Win.zsum (X ^ 2) h x := by
      simp only [hZ, Win.zsum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun ρ _ => ?_)
      ring
    have hid : (((Chebyshev.psi (x + h) - Chebyshev.psi x - h : ℝ)) : ℂ)
        = ((((Chebyshev.psi (x + h) : ℝ) : ℂ) - ((x + h : ℝ) : ℂ) + Z (x + h))
          - (((Chebyshev.psi x : ℝ) : ℂ) - (x : ℂ) + Z x)) - Win.zsum (X ^ 2) h x := by
      rw [← hZd]; push_cast; ring
    have e1 := herr (x + h) (by linarith [hx.1]) (by linarith [hx.2])
    have e2 := herr x hx.1 (by linarith [hx.2])
    have habs : |Chebyshev.psi (x + h) - Chebyshev.psi x - h|
        ≤ 2 * K * Real.log X ^ 2 + ‖Win.zsum (X ^ 2) h x‖ := by
      have : ‖(((Chebyshev.psi (x + h) - Chebyshev.psi x - h : ℝ)) : ℂ)‖
          = |Chebyshev.psi (x + h) - Chebyshev.psi x - h| := by
        rw [Complex.norm_real, Real.norm_eq_abs]
      rw [← this, hid]
      calc _ ≤ ‖((((Chebyshev.psi (x + h) : ℝ) : ℂ) - ((x + h : ℝ) : ℂ) + Z (x + h))
              - (((Chebyshev.psi x : ℝ) : ℂ) - (x : ℂ) + Z x))‖
            + ‖Win.zsum (X ^ 2) h x‖ := norm_sub_le _ _
        _ ≤ (‖((Chebyshev.psi (x + h) : ℝ) : ℂ) - ((x + h : ℝ) : ℂ) + Z (x + h)‖
            + ‖((Chebyshev.psi x : ℝ) : ℂ) - (x : ℂ) + Z x‖) + ‖Win.zsum (X ^ 2) h x‖ := by
            gcongr; exact norm_sub_le _ _
        _ ≤ (K * Real.log X ^ 2 + K * Real.log X ^ 2) + ‖Win.zsum (X ^ 2) h x‖ := by
            gcongr
        _ = 2 * K * Real.log X ^ 2 + ‖Win.zsum (X ^ 2) h x‖ := by ring
    have hsq : (Chebyshev.psi (x + h) - Chebyshev.psi x - h) ^ 2
        ≤ (2 * K * Real.log X ^ 2 + ‖Win.zsum (X ^ 2) h x‖) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    have hn0 := norm_nonneg (Win.zsum (X ^ 2) h x)
    nlinarith [sq_nonneg (2 * K * Real.log X ^ 2 - ‖Win.zsum (X ^ 2) h x‖)]
  have hC0 : 0 ≤ 8 * K ^ 2 + 2 * C₄' := by positivity
  by_cases hint : IntervalIntegrable
      (fun x => (Chebyshev.psi (x + h) - Chebyshev.psi x - h) ^ 2) volume X (2 * X)
  · have hSc : ContinuousOn (fun x => ‖Win.zsum (X ^ 2) h x‖ ^ 2) (uIcc X (2 * X)) := by
      refine ((Win.zsum_continuousOn hXpos hh0).norm.pow 2).mono ?_
      rw [uIcc_of_le (by linarith)]
      exact Icc_subset_Ici_self
    have hSi := hSc.intervalIntegrable (μ := volume)
    have hKX := hK X h hX4 hh1 hhX
    have hKX' : ∫ x in X..(2 * X), ‖Win.zsum (X ^ 2) h x‖ ^ 2 ≤ C₄' * h * X * Real.log X ^ 2 :=
      le_trans hKX (by gcongr; exact le_max_left _ _)
    calc ∫ x in X..(2 * X), (Chebyshev.psi (x + h) - Chebyshev.psi x - h) ^ 2
        ≤ ∫ x in X..(2 * X), (8 * K ^ 2 * Real.log X ^ 4 + 2 * ‖Win.zsum (X ^ 2) h x‖ ^ 2) :=
          intervalIntegral.integral_mono_on (by linarith) hint
            (intervalIntegrable_const.add (hSi.const_mul 2)) hpt
      _ = (2 * X - X) * (8 * K ^ 2 * Real.log X ^ 4)
            + 2 * (∫ x in X..(2 * X), ‖Win.zsum (X ^ 2) h x‖ ^ 2) := by
          rw [intervalIntegral.integral_add intervalIntegrable_const (hSi.const_mul 2),
            intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul]
      _ ≤ X * (8 * K ^ 2 * Real.log X ^ 4) + 2 * (C₄' * h * X * Real.log X ^ 2) := by
          rw [show 2 * X - X = X by ring]
          gcongr
      _ ≤ (8 * K ^ 2 + 2 * C₄') * h * X * Real.log X ^ 2 := by
          have hl4 : Real.log X ^ 4 ≤ h * Real.log X ^ 2 := by
            rw [show Real.log X ^ 4 = Real.log X ^ 2 * Real.log X ^ 2 by ring]
            exact mul_le_mul_of_nonneg_right hlh (sq_nonneg _)
          have : X * (8 * K ^ 2 * Real.log X ^ 4) ≤ X * (8 * K ^ 2 * (h * Real.log X ^ 2)) := by
            gcongr
          nlinarith
  · rw [intervalIntegral.integral_undef hint]
    positivity

/-- Final assembly of the frozen interface from B1–B3. -/
theorem selbergMeanSquare_assembly (hRH : RiemannHypothesis) : SelbergMeanSquare := by
  intro θ' hθ'
  obtain ⟨C₂, hB2⟩ := integral_psi_sub_theta_sq_le
  obtain ⟨C₃, X₃, hB3⟩ := integral_psi_window_sq_le hRH
  obtain ⟨X₁, hX₁⟩ := Filter.eventually_atTop.mp
    ((isLittleO_log_rpow_rpow_atTop 2 hθ').bound one_pos)
  set Xb : ℝ := max (max X₁ X₃) 3 with hXb
  have hXb3 : 3 ≤ Xb := le_max_right _ _
  set C₂' := max C₂ 0
  set C₃' := max C₃ 0
  refine ⟨max (2 * C₃' + 2 * C₂') (100 * Xb ^ 3), fun X h hX hθh hh2 => ?_⟩
  have hXr : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hXpos : (0 : ℝ) < X := by linarith
  have hθ1 : (1 : ℝ) ≤ (X : ℝ) ^ θ' := Real.one_le_rpow (by linarith) hθ'.le
  have hh1r : (1 : ℝ) ≤ h := le_trans hθ1 hθh
  have hh1 : 1 ≤ h := by exact_mod_cast hh1r
  have hhX : h ≤ X := le_trans (Nat.le_self_pow (by norm_num) h) hh2
  have hhXr : (h : ℝ) ≤ X := by exact_mod_cast hhX
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hlogX : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hXr
  have hRHS0 : 0 ≤ (h : ℝ) * X * Real.log X ^ 2 := by positivity
  have hRHS1 : (0.9 : ℝ) ≤ (h : ℝ) * X * Real.log X ^ 2 := by
    have : (0.47 : ℝ) ≤ Real.log X ^ 2 := by nlinarith
    have : (2 : ℝ) ≤ (h : ℝ) * X := by nlinarith
    nlinarith
  by_cases hbig : Xb ≤ (X : ℝ)
  · have hX3 : X₃ ≤ (X : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hbig
    have hX1 : X₁ ≤ (X : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hbig
    have hlh : Real.log X ^ 2 ≤ (h : ℝ) := by
      have := hX₁ X hX1
      rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul,
        abs_of_nonneg (Real.rpow_nonneg hXpos.le _), Real.rpow_two] at this
      exact le_trans (le_trans (le_abs_self _) this) hθh
    rw [sum_eq_integral_theta X h]
    have hθi : IntervalIntegrable
        (fun x => (Chebyshev.theta (x + h) - Chebyshev.theta x - h) ^ 2) volume X (2 * X) :=
      Win.intervalIntegrable_sq_of_monotone
        (fun a b hab => Chebyshev.theta_mono (by linarith)) Chebyshev.theta_mono _
        (by linarith)
    have hψi : IntervalIntegrable
        (fun x => (Chebyshev.psi (x + h) - Chebyshev.psi x - h) ^ 2) volume X (2 * X) :=
      Win.intervalIntegrable_sq_of_monotone
        (fun a b hab => Chebyshev.psi_mono (by linarith)) Chebyshev.psi_mono _
        (by linarith)
    have hDi : IntervalIntegrable
        (fun x => ((Chebyshev.psi (x + h) - Chebyshev.theta (x + h))
            - (Chebyshev.psi x - Chebyshev.theta x)) ^ 2) volume X (2 * X) := by
      simpa using Win.intervalIntegrable_sq_of_monotone
        (g₁ := fun x => Chebyshev.psi (x + h) - Chebyshev.theta (x + h))
        (fun a b hab => Win.psiSubTheta_mono (by linarith)) Win.psiSubTheta_mono 0
        (by linarith : (X : ℝ) ≤ 2 * X)
    have hb2 := hB2 X h hXr (by positivity) hhXr
    have hb3 := hB3 X h hX3 hlh hhXr
    calc ∫ x in (X : ℝ)..(2 * X), (Chebyshev.theta (x + h) - Chebyshev.theta x - h) ^ 2
        ≤ ∫ x in (X : ℝ)..(2 * X),
            (2 * (Chebyshev.psi (x + h) - Chebyshev.psi x - h) ^ 2
              + 2 * ((Chebyshev.psi (x + h) - Chebyshev.theta (x + h))
                - (Chebyshev.psi x - Chebyshev.theta x)) ^ 2) := by
          apply intervalIntegral.integral_mono_on (by linarith) hθi
            ((hψi.const_mul 2).add (hDi.const_mul 2))
          intro x _
          nlinarith [sq_nonneg ((Chebyshev.psi (x + h) - Chebyshev.psi x - h)
            + ((Chebyshev.psi (x + h) - Chebyshev.theta (x + h))
                - (Chebyshev.psi x - Chebyshev.theta x)))]
      _ = 2 * (∫ x in (X : ℝ)..(2 * X), (Chebyshev.psi (x + h) - Chebyshev.psi x - h) ^ 2)
            + 2 * (∫ x in (X : ℝ)..(2 * X),
              ((Chebyshev.psi (x + h) - Chebyshev.theta (x + h))
                - (Chebyshev.psi x - Chebyshev.theta x)) ^ 2) := by
          rw [intervalIntegral.integral_add (hψi.const_mul 2) (hDi.const_mul 2),
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      _ ≤ 2 * (C₃' * h * X * Real.log X ^ 2) + 2 * (C₂' * h * X * Real.log X ^ 2) := by
          gcongr
          · exact le_trans hb3 (by gcongr; exact le_max_left _ _)
          · exact le_trans hb2 (by gcongr; exact le_max_left _ _)
      _ = (2 * C₃' + 2 * C₂') * h * X * Real.log X ^ 2 := by ring
      _ ≤ max (2 * C₃' + 2 * C₂') (100 * Xb ^ 3) * h * X * Real.log X ^ 2 := by
          gcongr; exact le_max_left _ _
  · push Not at hbig
    have hterm : ∀ n ∈ Finset.Ico X (2 * X),
        (Chebyshev.theta ((n + h : ℕ) : ℝ) - Chebyshev.theta n - h) ^ 2
          ≤ 81 * (X : ℝ) ^ 2 := by
      intro n hn
      have hn' := Finset.mem_Ico.mp hn
      have hnr : (n : ℝ) < 2 * X := by exact_mod_cast hn'.2
      have ht0 := Chebyshev.theta_nonneg (n : ℝ)
      have ht1 : Chebyshev.theta (n : ℝ) ≤ Chebyshev.theta ((n + h : ℕ) : ℝ) :=
        Chebyshev.theta_mono (by push_cast; linarith [(Nat.cast_nonneg h : (0 : ℝ) ≤ h)])
      have ht2 : Chebyshev.theta ((n + h : ℕ) : ℝ) ≤ Real.log 4 * ((n + h : ℕ) : ℝ) :=
        Chebyshev.theta_le_log4_mul_x (by positivity)
      have hl4 : Real.log 4 ≤ 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        have := Real.log_two_lt_d9; push_cast; linarith
      have hnh : ((n + h : ℕ) : ℝ) ≤ 3 * X := by push_cast; linarith
      have hT : Chebyshev.theta ((n + h : ℕ) : ℝ) ≤ 6 * X := by
        have : 0 ≤ ((n + h : ℕ) : ℝ) := by positivity
        nlinarith
      have habs : |Chebyshev.theta ((n + h : ℕ) : ℝ) - Chebyshev.theta n - h| ≤ 9 * X := by
        rw [abs_le]; constructor <;> nlinarith
      calc _ = |Chebyshev.theta ((n + h : ℕ) : ℝ) - Chebyshev.theta n - h| ^ 2 := (sq_abs _).symm
        _ ≤ (9 * (X : ℝ)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
        _ = 81 * (X : ℝ) ^ 2 := by ring
    calc ∑ n ∈ Finset.Ico X (2 * X),
            (Chebyshev.theta ((n + h : ℕ) : ℝ) - Chebyshev.theta n - h) ^ 2
        ≤ ∑ _n ∈ Finset.Ico X (2 * X), 81 * (X : ℝ) ^ 2 := Finset.sum_le_sum hterm
      _ = 81 * (X : ℝ) ^ 3 := by
          rw [Finset.sum_const, Nat.card_Ico, show 2 * X - X = X by omega, nsmul_eq_mul]; ring
      _ ≤ 81 * Xb ^ 3 := by gcongr
      _ ≤ 100 * Xb ^ 3 * (0.9 : ℝ) := by nlinarith [pow_pos (by linarith : (0 : ℝ) < Xb) 3]
      _ ≤ 100 * Xb ^ 3 * (h * X * Real.log X ^ 2) := by gcongr
      _ = 100 * Xb ^ 3 * h * X * Real.log X ^ 2 := by ring
      _ ≤ max (2 * C₃' + 2 * C₂') (100 * Xb ^ 3) * h * X * Real.log X ^ 2 := by
          gcongr; exact le_max_right _ _

end PPF.RH
