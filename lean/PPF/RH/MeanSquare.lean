import PPF.RH.Kernel
import PPF.RH.ZeroSums
import PPF.RH.MeanSquare.Helpers

/-!
# K4: Selberg's mean square of the zero sum

`S(x) = ∑_{ρ ∈ zetaZeros (X²)} mult ρ · ((x+h)^ρ − x^ρ)/ρ`, `ρ = 1/2 + iγ` (RH).
Split at `U = max(X/h, 2)`.
* Low zeros: `((x+h)^ρ − x^ρ)/ρ = ∫_x^{x+h} u^{ρ−1} du`; Cauchy–Schwarz and the
  primitive trick give `∫_X^{2X} |S_low|² ≤ h² ∫ bump(u) |∑ m u^{−1/2+iγ}|² du`,
  which K1 (α = −1) and K3 (low) bound by `h² · U log² U ≪ h X log² X`.
* High zeros: `S_high(x) = G(x+h) − G(x)`, `G(x) = ∑ m x^ρ/ρ`;
  `∫ |S_high|² ≤ 4 ∫ bump |G|²`, bounded by K1 (α = 1) and K3 (high):
  `X² log² U / U ≪ h X log² X`.
-/

namespace PPF.RH

open Complex

namespace MS

open MeasureTheory intervalIntegral Set

theorem bump_continuous (X : ℝ) : Continuous (fun u => bump X u) := by
  unfold bump; fun_prop

/-- `∫_X^{3X} q ≤ ∫_{X/2}^{4X} bump · q` for `q ≥ 0`. -/
theorem integral_le_bump {q : ℝ → ℝ} {X : ℝ} (hX : 0 < X) (hq : ContinuousOn q (Ioi 0))
    (hq0 : ∀ u, 0 ≤ q u) :
    ∫ u in X..3 * X, q u ≤ ∫ u in (X / 2)..(4 * X), bump X u * q u := by
  have hbq : ContinuousOn (fun u => bump X u * q u) (Ioi 0) :=
    (bump_continuous X).continuousOn.mul hq
  calc ∫ u in X..3 * X, q u ≤ ∫ u in X..3 * X, bump X u * q u := by
        apply intervalIntegral.integral_mono_on (by linarith)
        · exact intervalIntegrable_of_continuousOn_Ioi hq hX (by linarith)
        · exact intervalIntegrable_of_continuousOn_Ioi hbq hX (by linarith)
        · intro u hu
          have := one_le_bump hX hu.1 hu.2
          nlinarith [hq0 u]
    _ ≤ ∫ u in (X / 2)..(4 * X), bump X u * q u := by
        apply intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
        · exact Filter.Eventually.of_forall (fun u => mul_nonneg (bump_nonneg X u) (hq0 u))
        · exact intervalIntegrable_of_continuousOn_Ioi hbq (by linarith) (by linarith)

/-- Low zeros: Cauchy–Schwarz on `∫_x^{x+h} ∑ c u^{ρ−1} du`. -/
theorem low_bound (Z : Finset ℂ) (c : ℂ → ℂ) (hZ : ∀ ρ ∈ Z, ρ.re = 1 / 2) {X h : ℝ}
    (hX : 0 < X) (hh : 0 ≤ h) (hhX : h ≤ X) :
    ∫ x in X..2 * X, ‖∑ ρ ∈ Z, c ρ * ((((x + h : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ)‖ ^ 2
      ≤ h * (h * ∫ u in (X / 2)..(4 * X),
          bump X u * ‖∑ ρ ∈ Z, c ρ * (u : ℂ) ^ (ρ - 1)‖ ^ 2) := by
  set F : ℝ → ℂ := fun u => ∑ ρ ∈ Z, c ρ * (u : ℂ) ^ (ρ - 1) with hF
  have hFc : ContinuousOn F (Ioi 0) := continuousOn_pow_sum Z c (fun ρ => ρ - 1)
  have hg : ContinuousOn (fun u => ‖F u‖ ^ 2) (Ioi 0) := hFc.norm.pow 2
  have hfc : ContinuousOn (fun x : ℝ =>
      ‖∑ ρ ∈ Z, c ρ * ((((x + h : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ)‖ ^ 2) (Ioi 0) :=
    (continuousOn_window_sum Z c hh).norm.pow 2
  have hwin := integral_window_le (g := fun u => ‖F u‖ ^ 2) hX.le hh hhX
    (intervalIntegrable_of_continuousOn_Ioi hg hX (by linarith))
    (fun u _ => sq_nonneg _)
    (intervalIntegrable_of_continuousOn_Ioi hfc hX (by linarith))
    (by
      intro x hx
      have hx0 : 0 < x := hX.trans_le hx.1
      rw [window_sum_eq_integral Z c hZ hx0 hh]
      have := norm_sq_integral_le (F := F) (a := x) (b := x + h) (by linarith)
        (hFc.mono (fun u hu => hx0.trans_le hu.1))
      rw [show x + h - x = h by ring] at this
      exact this)
  refine hwin.trans ?_
  apply mul_le_mul_of_nonneg_left _ hh
  apply mul_le_mul_of_nonneg_left _ hh
  exact integral_le_bump hX hg (fun u => sq_nonneg _)

/-- High zeros: `S = G(x+h) − G(x)`. -/
theorem high_bound (Z : Finset ℂ) (c : ℂ → ℂ) {X h : ℝ} (hX : 0 < X) (hh : 0 ≤ h)
    (hhX : h ≤ X) :
    ∫ x in X..2 * X, ‖∑ ρ ∈ Z, c ρ * ((((x + h : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ)‖ ^ 2
      ≤ 4 * ∫ u in (X / 2)..(4 * X), bump X u * ‖∑ ρ ∈ Z, c ρ / ρ * (u : ℂ) ^ ρ‖ ^ 2 := by
  set H : ℝ → ℂ := fun u => ∑ ρ ∈ Z, c ρ / ρ * (u : ℂ) ^ ρ with hH
  have hHc : ContinuousOn H (Ioi 0) := continuousOn_pow_sum Z (fun ρ => c ρ / ρ) (fun ρ => ρ)
  have hq : ContinuousOn (fun u => ‖H u‖ ^ 2) (Ioi 0) := hHc.norm.pow 2
  have hdiff : ∀ x : ℝ, ∑ ρ ∈ Z, c ρ * ((((x + h : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ)
      = H (x + h) - H x := by
    intro x
    simp only [hH]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    ring
  have hpt : ∀ x, ‖H (x + h) - H x‖ ^ 2 ≤ 2 * ‖H (x + h)‖ ^ 2 + 2 * ‖H x‖ ^ 2 := by
    intro x
    have := norm_sub_le (H (x + h)) (H x)
    nlinarith [norm_nonneg (H (x + h) - H x), norm_nonneg (H (x + h)), norm_nonneg (H x),
      sq_nonneg (‖H (x + h)‖ - ‖H x‖)]
  have hshift : ContinuousOn (fun x : ℝ => x + h) (Ioi 0) := (continuous_add_const h).continuousOn
  have hmaps : MapsTo (fun x : ℝ => x + h) (Ioi 0) (Ioi 0) := fun x hx => by
    simp only [mem_Ioi] at hx ⊢; linarith
  have hIH : IntervalIntegrable (fun x => ‖H x‖ ^ 2) volume X (2 * X) :=
    intervalIntegrable_of_continuousOn_Ioi hq hX (by linarith)
  have hIHs : IntervalIntegrable (fun x => ‖H (x + h)‖ ^ 2) volume X (2 * X) :=
    intervalIntegrable_of_continuousOn_Ioi (hq.comp hshift hmaps) hX (by linarith)
  have hIL : IntervalIntegrable (fun x => ‖H (x + h) - H x‖ ^ 2) volume X (2 * X) :=
    intervalIntegrable_of_continuousOn_Ioi (((hHc.comp hshift hmaps).sub hHc).norm.pow 2)
      hX (by linarith)
  have hI3 : IntervalIntegrable (fun x => ‖H x‖ ^ 2) volume X (3 * X) :=
    intervalIntegrable_of_continuousOn_Ioi hq hX (by linarith)
  calc ∫ x in X..2 * X, ‖∑ ρ ∈ Z, c ρ * ((((x + h : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ)‖ ^ 2
        = ∫ x in X..2 * X, ‖H (x + h) - H x‖ ^ 2 := by
        congr 1; funext x; rw [hdiff x]
    _ ≤ ∫ x in X..2 * X, (2 * ‖H (x + h)‖ ^ 2 + 2 * ‖H x‖ ^ 2) :=
        intervalIntegral.integral_mono_on (by linarith) hIL
          ((hIHs.const_mul 2).add (hIH.const_mul 2)) (fun x _ => hpt x)
    _ = 2 * (∫ x in X..2 * X, ‖H (x + h)‖ ^ 2) + 2 * ∫ x in X..2 * X, ‖H x‖ ^ 2 := by
        rw [intervalIntegral.integral_add (hIHs.const_mul 2) (hIH.const_mul 2),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    _ = 2 * (∫ x in X + h..2 * X + h, ‖H x‖ ^ 2) + 2 * ∫ x in X..2 * X, ‖H x‖ ^ 2 := by
        rw [intervalIntegral.integral_comp_add_right (fun x => ‖H x‖ ^ 2) h]
    _ ≤ 2 * (∫ x in X..3 * X, ‖H x‖ ^ 2) + 2 * ∫ x in X..3 * X, ‖H x‖ ^ 2 := by
        have h1 : ∫ x in X + h..2 * X + h, ‖H x‖ ^ 2 ≤ ∫ x in X..3 * X, ‖H x‖ ^ 2 :=
          intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
            (Filter.Eventually.of_forall fun x => sq_nonneg _) hI3
        have h2 : ∫ x in X..2 * X, ‖H x‖ ^ 2 ≤ ∫ x in X..3 * X, ‖H x‖ ^ 2 :=
          intervalIntegral.integral_mono_interval le_rfl (by linarith) (by linarith)
            (Filter.Eventually.of_forall fun x => sq_nonneg _) hI3
        linarith
    _ = 4 * ∫ x in X..3 * X, ‖H x‖ ^ 2 := by ring
    _ ≤ 4 * ∫ u in (X / 2)..(4 * X), bump X u * ‖H u‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact integral_le_bump hX hq (fun u => sq_nonneg _)

/-- The closing arithmetic. -/
theorem final_arith {A B X h : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hX : 2 ≤ X) (hh : 1 ≤ h)
    (hhX : h ≤ X) :
    2 * (h * (h * (A * (max (X / h) 2 * Real.log (max (X / h) 2) ^ 2))))
        + 2 * (4 * (B * X ^ 2 * (Real.log (max (X / h) 2) ^ 2 / max (X / h) 2)))
      ≤ (4 * A + 8 * B) * h * X * Real.log X ^ 2 := by
  have hX0 : 0 < X := by linarith
  have hh0 : 0 < h := by linarith
  have hlog2 : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hX
  have hlog20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hL : Real.log 2 ^ 2 ≤ Real.log X ^ 2 := pow_le_pow_left₀ hlog20 hlog2 2
  have hLX0 : 0 ≤ Real.log X ^ 2 := sq_nonneg _
  by_cases hc : 2 ≤ X / h
  · rw [max_eq_left hc]
    have hlu0 : 0 ≤ Real.log (X / h) := Real.log_nonneg (by linarith)
    have hlu : Real.log (X / h) ≤ Real.log X :=
      Real.log_le_log (by positivity) (div_le_self hX0.le hh)
    have hsq : Real.log (X / h) ^ 2 ≤ Real.log X ^ 2 := pow_le_pow_left₀ hlu0 hlu 2
    have key : 2 * (h * (h * (A * (X / h * Real.log (X / h) ^ 2))))
        + 2 * (4 * (B * X ^ 2 * (Real.log (X / h) ^ 2 / (X / h))))
        = (2 * A + 8 * B) * (h * X) * Real.log (X / h) ^ 2 := by
      field_simp
      ring
    rw [key]
    have hhX0 : 0 ≤ h * X := by positivity
    calc (2 * A + 8 * B) * (h * X) * Real.log (X / h) ^ 2
        ≤ (2 * A + 8 * B) * (h * X) * Real.log X ^ 2 := by
          apply mul_le_mul_of_nonneg_left hsq; positivity
      _ ≤ (4 * A + 8 * B) * h * X * Real.log X ^ 2 := by
          have : 0 ≤ 2 * A * (h * X) * Real.log X ^ 2 := by positivity
          nlinarith
  · replace hc := not_le.mp hc
    rw [max_eq_right hc.le]
    have hX2h : X < 2 * h := by rwa [div_lt_iff₀ hh0] at hc
    have e : 2 * (h * (h * (A * (2 * Real.log 2 ^ 2))))
        + 2 * (4 * (B * X ^ 2 * (Real.log 2 ^ 2 / 2)))
        = 4 * A * (h * h) * Real.log 2 ^ 2 + 4 * B * (X * X) * Real.log 2 ^ 2 := by ring
    rw [e]
    have h1 : h * h ≤ h * X := mul_le_mul_of_nonneg_left hhX hh0.le
    have h2 : X * X ≤ 2 * h * X := mul_le_mul_of_nonneg_right hX2h.le hX0.le
    have t1 : 4 * A * (h * h) * Real.log 2 ^ 2 ≤ 4 * A * (h * X) * Real.log X ^ 2 := by
      apply mul_le_mul _ hL (sq_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    have t2 : 4 * B * (X * X) * Real.log 2 ^ 2 ≤ 4 * B * (2 * h * X) * Real.log X ^ 2 := by
      apply mul_le_mul _ hL (sq_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    nlinarith

end MS

open MS

/-- K4. -/
theorem mean_square_zero_sum_le (hRH : RiemannHypothesis) :
    ∃ C X₀ : ℝ, ∀ X h : ℝ, X₀ ≤ X → 1 ≤ h → h ≤ X →
      ∫ x in X..(2 * X),
          ‖∑ ρ ∈ zetaZeros (X ^ 2),
              (mult ρ : ℂ) * ((((x + h : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ)‖ ^ 2
        ≤ C * h * X * Real.log X ^ 2 := by
  obtain ⟨K₁, hK₁⟩ := norm_integral_bump_cpow_le (-1) le_rfl
  obtain ⟨K₂, hK₂⟩ := norm_integral_bump_cpow_le 1 (by norm_num)
  obtain ⟨C₃, hC₃⟩ := sum_low_pairs_le hRH
  obtain ⟨C₄, hC₄⟩ := sum_high_pairs_le hRH
  set A := max K₁ 0 * max C₃ 0 with hA
  set B := max K₂ 0 * max C₄ 0 with hB
  have hA0 : 0 ≤ A := mul_nonneg (le_max_right _ _) (le_max_right _ _)
  have hB0 : 0 ≤ B := mul_nonneg (le_max_right _ _) (le_max_right _ _)
  refine ⟨4 * A + 8 * B, 2, fun X h hX hh hhX => ?_⟩
  have hX0 : 0 < X := by linarith
  set U := max (X / h) 2 with hUdef
  have hU : 2 ≤ U := le_max_right _ _
  have hU0 : 0 < U := by linarith
  set Z := zetaZeros (X ^ 2) with hZ
  set low := Z.filter (fun ρ => ¬ U < |ρ.im|) with hlow
  set high := Z.filter (fun ρ => U < |ρ.im|) with hhigh
  have hre : ∀ ρ ∈ Z, ρ.re = 1 / 2 := fun ρ hρ => re_eq_half_of_mem hRH hρ
  set T : ℂ → ℝ → ℂ := fun ρ x => (mult ρ : ℂ) * ((((x + h : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ)
    with hT
  -- pointwise splitting
  have hsplit : ∀ x : ℝ, ∑ ρ ∈ Z, T ρ x = ∑ ρ ∈ low, T ρ x + ∑ ρ ∈ high, T ρ x := by
    intro x
    rw [add_comm]
    exact (Finset.sum_filter_add_sum_filter_not Z (fun ρ => U < |ρ.im|) (fun ρ => T ρ x)).symm
  have hpt : ∀ x : ℝ, ‖∑ ρ ∈ Z, T ρ x‖ ^ 2
      ≤ 2 * ‖∑ ρ ∈ low, T ρ x‖ ^ 2 + 2 * ‖∑ ρ ∈ high, T ρ x‖ ^ 2 := by
    intro x
    rw [hsplit x]
    have := norm_add_le (∑ ρ ∈ low, T ρ x) (∑ ρ ∈ high, T ρ x)
    nlinarith [norm_nonneg (∑ ρ ∈ low, T ρ x + ∑ ρ ∈ high, T ρ x),
      norm_nonneg (∑ ρ ∈ low, T ρ x), norm_nonneg (∑ ρ ∈ high, T ρ x),
      sq_nonneg (‖∑ ρ ∈ low, T ρ x‖ - ‖∑ ρ ∈ high, T ρ x‖)]
  have hhh : (0 : ℝ) ≤ h := by linarith
  have hcont : ∀ W : Finset ℂ, IntervalIntegrable (fun x : ℝ => ‖∑ ρ ∈ W, T ρ x‖ ^ 2)
      MeasureTheory.volume X (2 * X) := fun W =>
    intervalIntegrable_of_continuousOn_Ioi
      ((continuousOn_window_sum W (fun ρ => (mult ρ : ℂ)) hhh).norm.pow 2) hX0 (by linarith)
  have hint : ∫ x in X..2 * X, ‖∑ ρ ∈ Z, T ρ x‖ ^ 2
      ≤ 2 * (∫ x in X..2 * X, ‖∑ ρ ∈ low, T ρ x‖ ^ 2)
        + 2 * ∫ x in X..2 * X, ‖∑ ρ ∈ high, T ρ x‖ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add ((hcont low).const_mul 2) ((hcont high).const_mul 2)]
    exact intervalIntegral.integral_mono_on (by linarith) (hcont Z)
      (((hcont low).const_mul 2).add ((hcont high).const_mul 2)) (fun x _ => hpt x)
  have hlowB := low_bound low (fun ρ => (mult ρ : ℂ))
    (fun ρ hρ => hre ρ (Finset.mem_filter.mp hρ).1) hX0 hhh hhX
  have hhighB := high_bound high (fun ρ => (mult ρ : ℂ)) hX0 hhh hhX
  -- the low quadratic form
  have hlowsub : low ⊆ zetaZeros U := by
    intro ρ hρ
    obtain ⟨hρZ, hρU⟩ := Finset.mem_filter.mp hρ
    obtain ⟨h1, h2, _, h4⟩ := (mem_zetaZeros hRH).mp hρZ
    exact (mem_zetaZeros hRH).mpr ⟨h1, h2, not_lt.mp hρU, h4⟩
  have hQlow : ∫ u in (X / 2)..(4 * X),
      bump X u * ‖∑ ρ ∈ low, (mult ρ : ℂ) * (u : ℂ) ^ (ρ - 1)‖ ^ 2
      ≤ A * (U * Real.log U ^ 2) := by
    have h1 := integral_weight_norm_sq_le low (fun ρ => (mult ρ : ℂ)) (fun ρ => ρ - 1) (-1)
      (by
        intro ρ hρ
        rw [Complex.sub_re, hre ρ (Finset.mem_filter.mp hρ).1, Complex.one_re]; norm_num)
      (by linarith : (0 : ℝ) < X / 2) (by linarith : X / 2 ≤ 4 * X)
      (bump_continuous X).continuousOn
      (fun τ => max K₁ 0 / (1 + τ ^ 2))
      (by
        intro τ
        have := hK₁ X (by linarith) τ
        simp only [show ((-1 : ℝ) + 1) = 0 by norm_num, Real.rpow_zero, mul_one] at this
        refine this.trans ?_
        exact div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
    refine h1.trans ?_
    have hsum : ∑ ρ ∈ low, ∑ ρ' ∈ low, ‖(mult ρ : ℂ)‖ * ‖(mult ρ' : ℂ)‖
          * (max K₁ 0 / (1 + ((ρ - 1).im - (ρ' - 1).im) ^ 2))
        = max K₁ 0 * ∑ ρ ∈ low, ∑ ρ' ∈ low,
            ((mult ρ : ℝ) * mult ρ') / (1 + (ρ.im - ρ'.im) ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ρ' _ => ?_
      simp only [Complex.norm_natCast, Complex.sub_im, Complex.one_im, sub_zero]
      ring
    rw [hsum, hA, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
    have hnn : ∀ ρ ρ' : ℂ, 0 ≤ ((mult ρ : ℝ) * mult ρ') / (1 + (ρ.im - ρ'.im) ^ 2) :=
      fun ρ ρ' => by positivity
    calc ∑ ρ ∈ low, ∑ ρ' ∈ low, ((mult ρ : ℝ) * mult ρ') / (1 + (ρ.im - ρ'.im) ^ 2)
        ≤ ∑ ρ ∈ zetaZeros U, ∑ ρ' ∈ zetaZeros U,
            ((mult ρ : ℝ) * mult ρ') / (1 + (ρ.im - ρ'.im) ^ 2) := by
          refine (Finset.sum_le_sum fun ρ _ =>
            Finset.sum_le_sum_of_subset_of_nonneg hlowsub (fun ρ' _ _ => hnn ρ ρ')).trans ?_
          exact Finset.sum_le_sum_of_subset_of_nonneg hlowsub
            (fun ρ _ _ => Finset.sum_nonneg fun ρ' _ => hnn ρ ρ')
      _ ≤ C₃ * U * Real.log U ^ 2 := hC₃ U hU
      _ ≤ max C₃ 0 * (U * Real.log U ^ 2) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  -- the high quadratic form
  have hQhigh : ∫ u in (X / 2)..(4 * X),
      bump X u * ‖∑ ρ ∈ high, (mult ρ : ℂ) / ρ * (u : ℂ) ^ ρ‖ ^ 2
      ≤ B * X ^ 2 * (Real.log U ^ 2 / U) := by
    have h1 := integral_weight_norm_sq_le high (fun ρ => (mult ρ : ℂ) / ρ) (fun ρ => ρ) 1
      (by
        intro ρ hρ
        show ρ.re = 1 / 2
        exact hre ρ (Finset.mem_filter.mp hρ).1)
      (by linarith : (0 : ℝ) < X / 2) (by linarith : X / 2 ≤ 4 * X)
      (bump_continuous X).continuousOn
      (fun τ => max K₂ 0 * X ^ 2 / (1 + τ ^ 2))
      (by
        intro τ
        have := hK₂ X (by linarith) τ
        simp only [show ((1 : ℝ) + 1) = 2 by norm_num, Real.rpow_two] at this
        refine this.trans ?_
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg X)) (by positivity))
    refine h1.trans ?_
    have hsum : ∑ ρ ∈ high, ∑ ρ' ∈ high, ‖(mult ρ : ℂ) / ρ‖ * ‖(mult ρ' : ℂ) / ρ'‖
          * (max K₂ 0 * X ^ 2 / (1 + (ρ.im - ρ'.im) ^ 2))
        = max K₂ 0 * X ^ 2 * ∑ ρ ∈ high, ∑ ρ' ∈ high,
            ((mult ρ : ℝ) * mult ρ') / (‖ρ‖ * ‖ρ'‖ * (1 + (ρ.im - ρ'.im) ^ 2)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ρ' _ => ?_
      simp only [norm_div, Complex.norm_natCast]
      simp only [div_eq_mul_inv, mul_inv]
      ring
    rw [hsum, hB]
    have hle := hC₄ U (X ^ 2) hU
    have hX2 : 0 ≤ max K₂ 0 * X ^ 2 := mul_nonneg (le_max_right _ _) (sq_nonneg _)
    calc max K₂ 0 * X ^ 2 * ∑ ρ ∈ high, ∑ ρ' ∈ high,
            ((mult ρ : ℝ) * mult ρ') / (‖ρ‖ * ‖ρ'‖ * (1 + (ρ.im - ρ'.im) ^ 2))
        ≤ max K₂ 0 * X ^ 2 * (C₄ * Real.log U ^ 2 / U) :=
          mul_le_mul_of_nonneg_left hle hX2
      _ ≤ max K₂ 0 * X ^ 2 * (max C₄ 0 * (Real.log U ^ 2 / U)) := by
          apply mul_le_mul_of_nonneg_left _ hX2
          rw [mul_div_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ = max K₂ 0 * max C₄ 0 * X ^ 2 * (Real.log U ^ 2 / U) := by ring
  -- assembly
  have hfin := final_arith hA0 hB0 hX (hh) hhX
  calc ∫ x in X..2 * X, ‖∑ ρ ∈ Z, T ρ x‖ ^ 2
      ≤ 2 * (∫ x in X..2 * X, ‖∑ ρ ∈ low, T ρ x‖ ^ 2)
        + 2 * ∫ x in X..2 * X, ‖∑ ρ ∈ high, T ρ x‖ ^ 2 := hint
    _ ≤ 2 * (h * (h * (A * (U * Real.log U ^ 2))))
        + 2 * (4 * (B * X ^ 2 * (Real.log U ^ 2 / U))) := by
      have e1 : ∫ x in X..2 * X, ‖∑ ρ ∈ low, T ρ x‖ ^ 2
          ≤ h * (h * (A * (U * Real.log U ^ 2))) := by
        refine hlowB.trans ?_
        apply mul_le_mul_of_nonneg_left _ hhh
        exact mul_le_mul_of_nonneg_left hQlow hhh
      have e2 : ∫ x in X..2 * X, ‖∑ ρ ∈ high, T ρ x‖ ^ 2
          ≤ 4 * (B * X ^ 2 * (Real.log U ^ 2 / U)) := by
        refine hhighB.trans ?_
        exact mul_le_mul_of_nonneg_left hQhigh (by norm_num)
      linarith
    _ ≤ (4 * A + 8 * B) * h * X * Real.log X ^ 2 := hfin

end PPF.RH
