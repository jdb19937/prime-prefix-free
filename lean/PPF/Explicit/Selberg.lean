import PPF.RH.Windows
import PPF.Explicit.Defs
import PPF.Explicit.EF
import PPF.Explicit.MeanSquare

/-!
# Explicit bound: Selberg's mean square, explicit constants, full window range

`psi_window_explicit`: B3 (`PPF.RH.integral_psi_window_sq_le`) with
`8·(32·13·10^6)² + 2·2·10^14 ≤ 2·10^18`, `X₀ = 100`.
`theta_window_explicit`: the discrete θ-form (B1 + B2 + B3), `2·2·10^18 + 2·108 ≤ CT`.
-/

namespace PPF.Explicit.Sel

open Complex MeasureTheory Set intervalIntegral PPF.RH

/-- B3 with the explicit-formula constant `C₃` and the mean-square constant `C₄`
(valid for `X ≥ 2`) as parameters. -/
theorem psi_window_of {C₃ C₄ : ℝ} (hC₃ : 0 ≤ C₃) (hC₄ : 0 ≤ C₄)
    (hE : ∀ y T : ℝ, 100 ≤ y → 2 ≤ T →
      ‖((Chebyshev.psi y : ℝ) : ℂ) - y
          + ∑ ρ ∈ zetaZeros T, (mult ρ : ℂ) * ((y : ℂ) ^ ρ / ρ)‖
        ≤ C₃ * (y * Real.log (T * y) ^ 2 / T + Real.log (T * y) ^ 2))
    (hK : ∀ X h : ℝ, 2 ≤ X → 1 ≤ h → h ≤ X →
      ∫ x in X..(2 * X),
          ‖∑ ρ ∈ zetaZeros (X ^ 2),
              (mult ρ : ℂ) * ((((x + h : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ)‖ ^ 2
        ≤ C₄ * h * X * Real.log X ^ 2) :
    ∀ X h : ℝ, 100 ≤ X → Real.log X ^ 2 ≤ h → h ≤ X →
      ∫ x in X..(2 * X), (Chebyshev.psi (x + h) - Chebyshev.psi x - h) ^ 2
        ≤ (8 * (32 * C₃) ^ 2 + 2 * C₄) * h * X * Real.log X ^ 2 := by
  intro X h hX100 hlh hhX
  set K := 32 * C₃ with hKdef
  have hK0 : 0 ≤ K := by positivity
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
    calc _ ≤ C₃ * (y * Real.log (X ^ 2 * y) ^ 2 / X ^ 2 + Real.log (X ^ 2 * y) ^ 2) := h1
      _ ≤ C₃ * (32 * Real.log X ^ 2) := mul_le_mul_of_nonneg_left hbr hC₃
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
  by_cases hint : IntervalIntegrable
      (fun x => (Chebyshev.psi (x + h) - Chebyshev.psi x - h) ^ 2) volume X (2 * X)
  · have hSc : ContinuousOn (fun x => ‖Win.zsum (X ^ 2) h x‖ ^ 2) (uIcc X (2 * X)) := by
      refine ((Win.zsum_continuousOn hXpos hh0).norm.pow 2).mono ?_
      rw [uIcc_of_le (by linarith)]
      exact Icc_subset_Ici_self
    have hSi := hSc.intervalIntegrable (μ := volume)
    have hKX : ∫ x in X..(2 * X), ‖Win.zsum (X ^ 2) h x‖ ^ 2 ≤ C₄ * h * X * Real.log X ^ 2 :=
      hK X h (by linarith) hh1 hhX
    calc ∫ x in X..(2 * X), (Chebyshev.psi (x + h) - Chebyshev.psi x - h) ^ 2
        ≤ ∫ x in X..(2 * X), (8 * K ^ 2 * Real.log X ^ 4 + 2 * ‖Win.zsum (X ^ 2) h x‖ ^ 2) :=
          intervalIntegral.integral_mono_on (by linarith) hint
            (intervalIntegrable_const.add (hSi.const_mul 2)) hpt
      _ = (2 * X - X) * (8 * K ^ 2 * Real.log X ^ 4)
            + 2 * (∫ x in X..(2 * X), ‖Win.zsum (X ^ 2) h x‖ ^ 2) := by
          rw [intervalIntegral.integral_add intervalIntegrable_const (hSi.const_mul 2),
            intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul]
      _ ≤ X * (8 * K ^ 2 * Real.log X ^ 4) + 2 * (C₄ * h * X * Real.log X ^ 2) := by
          rw [show 2 * X - X = X by ring]
          gcongr
      _ ≤ (8 * K ^ 2 + 2 * C₄) * h * X * Real.log X ^ 2 := by
          have hl4 : Real.log X ^ 4 ≤ h * Real.log X ^ 2 := by
            rw [show Real.log X ^ 4 = Real.log X ^ 2 * Real.log X ^ 2 by ring]
            exact mul_le_mul_of_nonneg_right hlh (sq_nonneg _)
          have : X * (8 * K ^ 2 * Real.log X ^ 4) ≤ X * (8 * K ^ 2 * (h * Real.log X ^ 2)) := by
            gcongr
          nlinarith
  · rw [intervalIntegral.integral_undef hint]
    have : 0 ≤ 8 * K ^ 2 + 2 * C₄ := by positivity
    positivity

/-- B2 with its explicit constant `108`. -/
theorem psi_sub_theta_window_le :
    ∀ X h : ℝ, 2 ≤ X → 0 ≤ h → h ≤ X →
      ∫ x in X..(2 * X),
          ((Chebyshev.psi (x + h) - Chebyshev.theta (x + h))
            - (Chebyshev.psi x - Chebyshev.theta x)) ^ 2
        ≤ 108 * h * X * Real.log X ^ 2 := by
  intro X h hX hh hhX
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

end PPF.Explicit.Sel

namespace PPF.Explicit

open MeasureTheory Set intervalIntegral PPF.RH

theorem psi_window_explicit (hRH : RiemannHypothesis) :
    ∀ X h : ℝ, 100 ≤ X → Real.log X ^ 2 ≤ h → h ≤ X →
      ∫ x in X..(2 * X), (Chebyshev.psi (x + h) - Chebyshev.psi x - h) ^ 2
        ≤ 2 * 10 ^ 18 * h * X * Real.log X ^ 2 := by
  intro X h hX hlh hhX
  have key := Sel.psi_window_of (C₃ := 13000000) (C₄ := 2 * 10 ^ 14) (by norm_num) (by norm_num)
    (explicit_formula_explicit hRH) (mean_square_explicit hRH) X h hX hlh hhX
  have hXpos : 0 < X := by linarith
  have hh0 : 0 ≤ h := le_trans (sq_nonneg _) hlh
  have hR0 : 0 ≤ h * X * Real.log X ^ 2 := by positivity
  calc _ ≤ (8 * (32 * 13000000) ^ 2 + 2 * (2 * 10 ^ 14)) * h * X * Real.log X ^ 2 := key
    _ = (8 * (32 * 13000000) ^ 2 + 2 * (2 * 10 ^ 14)) * (h * X * Real.log X ^ 2) := by ring
    _ ≤ (2 * 10 ^ 18) * (h * X * Real.log X ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ hR0
        norm_num
    _ = 2 * 10 ^ 18 * h * X * Real.log X ^ 2 := by ring

theorem theta_window_explicit (hRH : RiemannHypothesis) :
    ∀ X h : ℕ, 100 ≤ X → Real.log X ^ 2 ≤ h → h ≤ X →
      ∑ n ∈ Finset.Ico X (2 * X),
          (Chebyshev.theta ((n + h : ℕ) : ℝ) - Chebyshev.theta n - h) ^ 2
        ≤ CT * h * X * Real.log X ^ 2 := by
  intro X h hX hlh hhX
  have hXr : (100 : ℝ) ≤ X := by exact_mod_cast hX
  have hXpos : (0 : ℝ) < X := by linarith
  have hhXr : (h : ℝ) ≤ X := by exact_mod_cast hhX
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
  have hb2 := Sel.psi_sub_theta_window_le X h (by linarith) (by positivity) hhXr
  have hb3 := psi_window_explicit hRH X h hXr hlh hhXr
  have hR0 : 0 ≤ (h : ℝ) * X * Real.log X ^ 2 := by positivity
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
    _ ≤ 2 * (2 * 10 ^ 18 * h * X * Real.log X ^ 2) + 2 * (108 * h * X * Real.log X ^ 2) := by
        gcongr
    _ = (4 * 10 ^ 18 + 216) * ((h : ℝ) * X * Real.log X ^ 2) := by ring
    _ ≤ CT * ((h : ℝ) * X * Real.log X ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ hR0
        unfold CT; norm_num
    _ = CT * h * X * Real.log X ^ 2 := by ring

end PPF.Explicit
