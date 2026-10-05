import PPF.RH.ZeroCount
import PPF.RH.ExplicitFormula.Core

/-!
# Explicit E3, core

A copy of `PPF.RH.EFA.explicit_formula_core` whose inputs D3, D4 and K2 carry explicit
constants, so that the output constant is explicit.
-/

namespace PPF.Explicit

namespace EFx

open Complex PPF.RH PPF.RH.EFA
open scoped Real Interval

set_option maxHeartbeats 4000000 in
/-- E3 with explicit constants: the constant is `920 + ‖ζ′(0)/ζ(0)‖ + 12 C₄ + 8 C₃ + 2 C₂`,
where `C₃`, `C₄`, `C₂` are the explicit constants of D3, D4 and K2. -/
theorem explicit_formula_core_explicit (hRH : RiemannHypothesis) (C3 C4 C2 : ℝ)
    (hC3 : ∀ t : ℝ,
      riemannZeta ((-1 / 2 : ℝ) + t * I) ≠ 0 ∧
      ‖deriv riemannZeta ((-1 / 2 : ℝ) + t * I) / riemannZeta ((-1 / 2 : ℝ) + t * I)‖
        ≤ C3 * Real.log (|t| + 2))
    (hC4 : ∀ T : ℝ, 2 ≤ T → ∃ t : ℝ, T ≤ t ∧ t ≤ T + 1 ∧
      ∀ σ : ℝ, -1 / 2 ≤ σ → σ ≤ 2 →
        riemannZeta ((σ : ℂ) + t * I) ≠ 0 ∧ riemannZeta ((σ : ℂ) - t * I) ≠ 0 ∧
        ‖deriv riemannZeta ((σ : ℂ) + t * I) / riemannZeta ((σ : ℂ) + t * I)‖
          ≤ C4 * Real.log (T + 4) ^ 2 ∧
        ‖deriv riemannZeta ((σ : ℂ) - t * I) / riemannZeta ((σ : ℂ) - t * I)‖
          ≤ C4 * Real.log (T + 4) ^ 2)
    (hC2nn : 0 ≤ C2)
    (hC2 : ∀ T t : ℝ,
      ∑ ρ ∈ (zetaZeros T).filter (fun ρ => t ≤ ρ.im ∧ ρ.im ≤ t + 1), (mult ρ : ℝ)
        ≤ C2 * Real.log (|t| + 2))
    (hRT : ∀ {y c t : ℝ}, 1 < y → 1 < c → 2 ≤ t →
      (∀ σ : ℝ, -1 / 2 ≤ σ → σ ≤ c →
        riemannZeta ((σ : ℂ) + t * I) ≠ 0 ∧ riemannZeta ((σ : ℂ) - t * I) ≠ 0) →
      Carmichael.rectInt (fun s => -(deriv riemannZeta s / riemannZeta s) * ((y : ℂ) ^ s / s))
          (((-1 / 2 : ℝ) : ℂ) - (t : ℂ) * I) ((c : ℂ) + (t : ℂ) * I)
        = 2 * π * I * ((y : ℂ) - deriv riemannZeta 0 / riemannZeta 0
            - ∑ ρ ∈ zetaZeros t, (mult ρ : ℂ) * ((y : ℂ) ^ ρ / ρ))) :
    ∀ y T : ℝ, 100 ≤ y → 2 ≤ T →
      ‖((Chebyshev.psi y : ℝ) : ℂ) - y
          + ∑ ρ ∈ zetaZeros T, (mult ρ : ℂ) * ((y : ℂ) ^ ρ / ρ)‖
        ≤ (920 + ‖deriv riemannZeta 0 / riemannZeta 0‖ + 12 * C4 + 8 * C3 + 2 * C2)
          * (y * Real.log (T * y) ^ 2 / T + Real.log (T * y) ^ 2) := by
  have hC3nn : 0 ≤ C3 := by
    have h := (hC3 0).2
    have hl : 0 < Real.log (|(0 : ℝ)| + 2) := Real.log_pos (by norm_num)
    exact (mul_nonneg_iff_of_pos_right hl).mp ((norm_nonneg _).trans h)
  have hC4nn : 0 ≤ C4 := by
    obtain ⟨t, -, -, ht⟩ := hC4 2 le_rfl
    have h := (ht 0 (by norm_num) (by norm_num)).2.2.1
    have hl : 0 < Real.log (2 + 4) ^ 2 := pow_pos (Real.log_pos (by norm_num)) 2
    exact (mul_nonneg_iff_of_pos_right hl).mp ((norm_nonneg _).trans h)
  set K0 := ‖deriv riemannZeta 0 / riemannZeta 0‖ with hK0
  have hK0nn : 0 ≤ K0 := norm_nonneg _
  intro y T hy hT
  -- basic quantities
  have hy0 : (0 : ℝ) < y := by linarith
  have hy1 : (1 : ℝ) ≤ y := by linarith
  have hT0 : (0 : ℝ) < T := by linarith
  have hlogy : 4 ≤ Real.log y := Carmichael.EF.four_le_log hy
  set c : ℝ := 1 + 1 / Real.log y with hcdef
  have hinv : 1 / Real.log y ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hlogy
  have hinv0 : 0 < 1 / Real.log y := one_div_pos.mpr (by linarith)
  have hc1 : 1 < c := by rw [hcdef]; linarith
  have hc2 : c ≤ 5 / 4 := by rw [hcdef]; linarith
  have hyc3 : y ^ c ≤ 3 * y := by
    rw [hcdef, Carmichael.EF.rpow_one_add_inv_log hy]
    nlinarith [Real.exp_one_lt_d9]
  obtain ⟨t, hTt, htT, hgood⟩ := hC4 T hT
  have ht2 : 2 ≤ t := le_trans hT hTt
  have ht0 : (0 : ℝ) < t := by linarith
  -- logarithms
  set LT := Real.log (T * y) with hLT
  have hTy : 100 ≤ T * y := by nlinarith
  have hLT4 : 4 ≤ LT := Carmichael.EF.four_le_log hTy
  have hTy0 : 0 < T * y := by linarith
  have hlog_le : ∀ z : ℝ, 0 < z → z ≤ T * y → Real.log z ≤ LT := fun z hz hzle =>
    Real.log_le_log hz hzle
  have hlogT4 : Real.log (T + 4) ≤ LT := hlog_le _ (by linarith) (by nlinarith)
  have hlogt2 : Real.log (t + 2) ≤ LT := hlog_le _ (by linarith) (by nlinarith)
  have hlogT3 : Real.log (T + 3) ≤ LT := hlog_le _ (by linarith) (by nlinarith)
  have hlog1t : Real.log (1 + t) ≤ LT := hlog_le _ (by linarith) (by nlinarith)
  have hlogty : Real.log (t * y) ≤ 2 * LT := by
    have h1 : Real.log (t * y) ≤ Real.log (2 * (T * y)) :=
      Real.log_le_log (by positivity) (by nlinarith)
    rw [Real.log_mul (by norm_num) hTy0.ne'] at h1
    have h2 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    linarith
  have hlogty0 : 0 ≤ Real.log (t * y) := Real.log_nonneg (by nlinarith)
  set A := y * LT ^ 2 / T with hAdef
  have hA0 : 0 ≤ A := by positivity
  have hL2 : 1 ≤ LT ^ 2 := by nlinarith
  -- the integrand
  set f : ℂ → ℂ := fun s => -(deriv riemannZeta s / riemannZeta s) * ((y : ℂ) ^ s / s)
    with hfdef
  -- the residue theorem on `[−1/2, c] × [−t, t]`
  have hRT := hRT (y := y) (c := c) (t := t) (by linarith) hc1 ht2
    (fun σ h1 h2 => ⟨(hgood σ h1 (by linarith)).1, (hgood σ h1 (by linarith)).2.1⟩)
  have hzre : (((-1 / 2 : ℝ) : ℂ) - (t : ℂ) * I).re = -1 / 2 := by simp
  have hzim : (((-1 / 2 : ℝ) : ℂ) - (t : ℂ) * I).im = -t := by simp
  have hwre : ((c : ℂ) + (t : ℂ) * I).re = c := by simp
  have hwim : ((c : ℂ) + (t : ℂ) * I).im = t := by simp
  unfold Carmichael.rectInt at hRT
  rw [hzre, hzim, hwre, hwim] at hRT
  set Bm := ∫ x : ℝ in (-1 / 2 : ℝ)..c, f ((x : ℂ) + ((-t : ℝ) : ℂ) * I) with hBm
  set Tp := ∫ x : ℝ in (-1 / 2 : ℝ)..c, f ((x : ℂ) + (t : ℂ) * I) with hTp
  set R := ∫ u : ℝ in (-t)..t, f ((c : ℂ) + (u : ℂ) * I) with hR
  set L := ∫ u : ℝ in (-t)..t, f (((-1 / 2 : ℝ) : ℂ) + (u : ℂ) * I) with hL
  -- the right edge is the Perron sum
  set P := Carmichael.EF.perronSum (1 : DirichletCharacter ℂ 1) y c t with hP
  have hRP : R = ((2 * π : ℝ) : ℂ) * P := by
    have h := Carmichael.EF.integral_right_edge (1 : DirichletCharacter ℂ 1) hy hc1 ht0
    rw [DirichletCharacter.LFunction_modOne_eq] at h
    rw [hR, ← h]
    congr 1
    funext u
    simp only [hfdef, neg_div]
  -- zero sums
  have hfinT := zetaZeros_finite hRH T
  have hsub : zetaZeros T ⊆ zetaZeros t := by
    intro ρ hρ
    rw [mem_zetaZeros hRH] at hρ ⊢
    exact ⟨hρ.1, hρ.2.1, le_trans hρ.2.2.1 hTt, hρ.2.2.2⟩
  set g : ℂ → ℂ := fun ρ => (mult ρ : ℂ) * ((y : ℂ) ^ ρ / ρ) with hgdef
  set St := ∑ ρ ∈ zetaZeros t, g ρ with hSt
  set ST := ∑ ρ ∈ zetaZeros T, g ρ with hST
  set D := ∑ ρ ∈ zetaZeros t \ zetaZeros T, g ρ with hD
  have hStD : St = D + ST := (Finset.sum_sdiff hsub).symm
  set Z0 : ℂ := deriv riemannZeta 0 / riemannZeta 0 with hZ0
  -- the key identity
  have hkey : (2 * π * I) * (P - ((y : ℂ) - Z0 - St)) = Tp - Bm + I * L := by
    rw [hRP] at hRT
    simp only [smul_eq_mul] at hRT
    push_cast at hRT ⊢
    linear_combination hRT
  have hE : ((Chebyshev.psi y : ℝ) : ℂ) - y + ST
      = -(P - Carmichael.EF.psiChi (1 : DirichletCharacter ℂ 1) y)
        + (P - ((y : ℂ) - Z0 - St)) - Z0 - D := by
    rw [psiChi_one_eq, hStD]; ring
  -- (a) Perron sum vs ψ
  have ha : ‖P - Carmichael.EF.psiChi (1 : DirichletCharacter ℂ 1) y‖
      ≤ 800 * A + 120 * LT ^ 2 := by
    have h := Carmichael.EF.perronSum_sub_psiChi_le (1 : DirichletCharacter ℂ 1) hy ht2
    have hsq : Real.log (t * y) ^ 2 ≤ 4 * LT ^ 2 := by nlinarith
    have h1 : y * Real.log (t * y) ^ 2 / t ≤ 4 * A := by
      rw [hAdef]
      calc y * Real.log (t * y) ^ 2 / t ≤ y * (4 * LT ^ 2) / t := by gcongr
        _ ≤ y * (4 * LT ^ 2) / T := by gcongr
        _ = 4 * (y * LT ^ 2 / T) := by ring
    calc ‖P - Carmichael.EF.psiChi (1 : DirichletCharacter ℂ 1) y‖
        ≤ 200 * (y * Real.log (t * y) ^ 2 / t) + 30 * Real.log (t * y) ^ 2 := h
      _ ≤ 200 * (4 * A) + 30 * (4 * LT ^ 2) := by gcongr
      _ = 800 * A + 120 * LT ^ 2 := by ring
  -- (b) horizontal edges
  have hhoriz : ∀ s : ℂ, s.im = t ∨ s.im = -t → -1 / 2 ≤ s.re → s.re ≤ c →
      ‖deriv riemannZeta s / riemannZeta s‖ ≤ C4 * Real.log (T + 4) ^ 2 →
      ‖f s‖ ≤ C4 * Real.log (T + 4) ^ 2 * (3 * y / T) := by
    intro s hs hs1 hs2 hK
    have h := norm_integrand_le hy0 s hK
    have hnorm : T ≤ ‖s‖ := by
      have := Complex.abs_im_le_norm s
      rcases hs with hs | hs <;> rw [hs] at this
      · rw [abs_of_pos ht0] at this; linarith
      · rw [abs_neg, abs_of_pos ht0] at this; linarith
    have hys : y ^ s.re ≤ 3 * y :=
      le_trans (Real.rpow_le_rpow_of_exponent_le hy1 hs2) hyc3
    have hK0' : 0 ≤ C4 * Real.log (T + 4) ^ 2 := by positivity
    calc ‖f s‖ ≤ C4 * Real.log (T + 4) ^ 2 * (y ^ s.re / ‖s‖) := h
      _ ≤ C4 * Real.log (T + 4) ^ 2 * (3 * y / T) := by
          gcongr
  have hedge_bound : C4 * Real.log (T + 4) ^ 2 * (3 * y / T) * |c - (-1 / 2)| ≤ 6 * C4 * A := by
    rw [abs_of_pos (by linarith)]
    have h1 : Real.log (T + 4) ^ 2 ≤ LT ^ 2 := by
      have : 0 ≤ Real.log (T + 4) := Real.log_nonneg (by linarith)
      nlinarith
    rw [hAdef]
    have h3 : 0 ≤ 3 * y / T := by positivity
    have h4 : c - (-1 / 2) ≤ 2 := by linarith
    have h5 : 0 ≤ c - (-1 / 2) := by linarith
    have h6 : C4 * Real.log (T + 4) ^ 2 * (3 * y / T) ≤ C4 * LT ^ 2 * (3 * y / T) := by gcongr
    have h7 : 0 ≤ C4 * LT ^ 2 * (3 * y / T) := by positivity
    calc C4 * Real.log (T + 4) ^ 2 * (3 * y / T) * (c - (-1 / 2))
        ≤ C4 * LT ^ 2 * (3 * y / T) * 2 := mul_le_mul h6 h4 h5 h7
      _ = 6 * C4 * (y * LT ^ 2 / T) := by ring
  have hTpb : ‖Tp‖ ≤ 6 * C4 * A := by
    refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const ?_) hedge_bound
    intro x hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    have hgx := hgood x hx.1.le (by linarith [hx.2])
    exact hhoriz _ (Or.inl (by simp)) (by simp; linarith [hx.1]) (by simp; exact hx.2)
      (by simpa using hgx.2.2.1)
  have hBmb : ‖Bm‖ ≤ 6 * C4 * A := by
    refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const ?_) hedge_bound
    intro x hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    have hgx := hgood x hx.1.le (by linarith [hx.2])
    have heq : (x : ℂ) + ((-t : ℝ) : ℂ) * I = (x : ℂ) - (t : ℂ) * I := by push_cast; ring
    rw [heq]
    exact hhoriz _ (Or.inr (by simp)) (by simp; linarith [hx.1]) (by simp; exact hx.2)
      hgx.2.2.2
  -- (c) left edge
  have hLb : ‖L‖ ≤ 8 * C3 * LT ^ 2 := by
    have hint : IntervalIntegrable (fun u : ℝ => 4 * C3 * Real.log (t + 2) * (1 / (1 + |u|)))
        MeasureTheory.volume (-t) t :=
      (continuous_const.mul Carmichael.EF.continuous_one_div_one_add_abs).intervalIntegrable _ _
    have h := intervalIntegral.norm_integral_le_of_norm_le (by linarith : -t ≤ t)
      (f := fun u : ℝ => f (((-1 / 2 : ℝ) : ℂ) + (u : ℂ) * I))
      (g := fun u : ℝ => 4 * C3 * Real.log (t + 2) * (1 / (1 + |u|))) ?_ hint
    · rw [intervalIntegral.integral_const_mul,
        Carmichael.EF.integral_one_div_one_add_abs (by linarith) ht0.le] at h
      have hl2 : 0 ≤ Real.log (t + 2) := Real.log_nonneg (by linarith)
      have hl1 : 0 ≤ Real.log (1 + t) := Real.log_nonneg (by linarith)
      have hlt : Real.log (1 - -t) = Real.log (1 + t) := by ring_nf
      rw [hlt] at h
      calc ‖L‖ ≤ 4 * C3 * Real.log (t + 2) * (Real.log (1 + t) + Real.log (1 + t)) := h
        _ ≤ 4 * C3 * LT * (LT + LT) := by gcongr
        _ = 8 * C3 * LT ^ 2 := by ring
    · refine Filter.Eventually.of_forall (fun u hu => ?_)
      have hu' : |u| ≤ t := abs_le.mpr ⟨hu.1.le, hu.2⟩
      have hD3 := (hC3 u).2
      have h1 := norm_integrand_le hy0 (((-1 / 2 : ℝ) : ℂ) + (u : ℂ) * I) hD3
      have hre : (((-1 / 2 : ℝ) : ℂ) + (u : ℂ) * I).re = -1 / 2 := by simp
      rw [hre] at h1
      have hy12 : y ^ (-1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy1 (by norm_num)
      have hnorm := norm_left_ge u
      have hpos : 0 < (1 + |u|) / 4 := by positivity
      have hlog : Real.log (|u| + 2) ≤ Real.log (t + 2) :=
        Real.log_le_log (by positivity) (by linarith)
      have hlog0 : 0 ≤ Real.log (|u| + 2) := Real.log_nonneg (by linarith [abs_nonneg u])
      have hq : y ^ (-1 / 2 : ℝ) / ‖((-1 / 2 : ℝ) : ℂ) + (u : ℂ) * I‖ ≤ 4 * (1 / (1 + |u|)) := by
        rw [div_le_iff₀ (lt_of_lt_of_le hpos hnorm)]
        have : 4 * (1 / (1 + |u|)) * ((1 + |u|) / 4) = 1 := by
          field_simp
        nlinarith [mul_le_mul_of_nonneg_left hnorm (by positivity : (0:ℝ) ≤ 4 * (1 / (1 + |u|)))]
      calc ‖f (((-1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖
          ≤ C3 * Real.log (|u| + 2)
              * (y ^ (-1 / 2 : ℝ) / ‖((-1 / 2 : ℝ) : ℂ) + (u : ℂ) * I‖) := h1
        _ ≤ C3 * Real.log (t + 2) * (4 * (1 / (1 + |u|))) := by
            have hCl : 0 ≤ C3 * Real.log (t + 2) :=
              mul_nonneg hC3nn (Real.log_nonneg (by linarith))
            gcongr
        _ = 4 * C3 * Real.log (t + 2) * (1 / (1 + |u|)) := by ring
  -- (d) zeros with `T < |Im ρ| ≤ t`
  have hDb : ‖D‖ ≤ 2 * C2 * A := by
    have hterm : ∀ ρ ∈ zetaZeros t \ zetaZeros T, ‖g ρ‖ ≤ (mult ρ : ℝ) * (y / T) := by
      intro ρ hρ
      rw [Finset.mem_sdiff] at hρ
      have hρt := hρ.1
      have hre := re_eq_half_of_mem hRH hρt
      have hmem := (mem_zetaZeros hRH).mp hρt
      have hnot : ¬ (0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T ∧ riemannZeta ρ = 0) := fun h =>
        hρ.2 ((mem_zetaZeros hRH).mpr h)
      have him : T < |ρ.im| := by
        by_contra hle
        push Not at hle
        exact hnot ⟨hmem.1, hmem.2.1, hle, hmem.2.2.2⟩
      have hnorm : T ≤ ‖ρ‖ := le_trans him.le (Complex.abs_im_le_norm ρ)
      rw [hgdef]
      simp only
      rw [norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy0, hre, Complex.norm_natCast]
      have hyh : y ^ (1 / 2 : ℝ) ≤ y := by
        calc y ^ (1 / 2 : ℝ) ≤ y ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hy1 (by norm_num)
          _ = y := Real.rpow_one y
      have hm0 : (0 : ℝ) ≤ mult ρ := Nat.cast_nonneg _
      have hq : y ^ (1 / 2 : ℝ) / ‖ρ‖ ≤ y / T := by
        calc y ^ (1 / 2 : ℝ) / ‖ρ‖ ≤ y / ‖ρ‖ := by gcongr
          _ ≤ y / T := by gcongr
      exact mul_le_mul_of_nonneg_left hq hm0
    have hcount : ∑ ρ ∈ zetaZeros t \ zetaZeros T, (mult ρ : ℝ) ≤ 2 * C2 * Real.log (T + 3) := by
      set F1 := (zetaZeros t).filter (fun ρ => T ≤ ρ.im ∧ ρ.im ≤ T + 1) with hF1
      set F2 := (zetaZeros t).filter (fun ρ => -T - 1 ≤ ρ.im ∧ ρ.im ≤ -T - 1 + 1) with hF2
      have hs : zetaZeros t \ zetaZeros T ⊆ F1 ∪ F2 := by
        intro ρ hρ
        rw [Finset.mem_sdiff] at hρ
        have hmem := (mem_zetaZeros hRH).mp hρ.1
        have hnot : ¬ (0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T ∧ riemannZeta ρ = 0) := fun h =>
          hρ.2 ((mem_zetaZeros hRH).mpr h)
        have him : T < |ρ.im| := by
          by_contra hle
          push Not at hle
          exact hnot ⟨hmem.1, hmem.2.1, hle, hmem.2.2.2⟩
        have hle := hmem.2.2.1
        rw [Finset.mem_union, hF1, hF2, Finset.mem_filter, Finset.mem_filter]
        rcases le_or_gt 0 ρ.im with h0 | h0
        · rw [abs_of_nonneg h0] at him hle
          left; exact ⟨hρ.1, him.le, by linarith⟩
        · rw [abs_of_neg h0] at him hle
          right; exact ⟨hρ.1, by linarith, by linarith⟩
      have h1 := hC2 t T
      have h2 := hC2 t (-T - 1)
      have habs : |(-T - 1 : ℝ)| = T + 1 := by
        rw [abs_of_neg (by linarith)]; ring
      rw [habs] at h2
      rw [abs_of_pos hT0] at h1
      have hl1 : Real.log (T + 2) ≤ Real.log (T + 3) := Real.log_le_log (by linarith) (by linarith)
      have hl2 : Real.log (T + 1 + 2) = Real.log (T + 3) := by ring_nf
      rw [hl2] at h2
      have hinter : 0 ≤ ∑ ρ ∈ F1 ∩ F2, (mult ρ : ℝ) :=
        Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
      have hunion := Finset.sum_union_inter (s₁ := F1) (s₂ := F2) (f := fun ρ => (mult ρ : ℝ))
      calc ∑ ρ ∈ zetaZeros t \ zetaZeros T, (mult ρ : ℝ)
          ≤ ∑ ρ ∈ F1 ∪ F2, (mult ρ : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => Nat.cast_nonneg _)
        _ ≤ ∑ ρ ∈ F1, (mult ρ : ℝ) + ∑ ρ ∈ F2, (mult ρ : ℝ) := by linarith
        _ ≤ C2 * Real.log (T + 2) + C2 * Real.log (T + 3) := add_le_add h1 h2
        _ ≤ 2 * C2 * Real.log (T + 3) := by nlinarith
    calc ‖D‖ ≤ ∑ ρ ∈ zetaZeros t \ zetaZeros T, ‖g ρ‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ zetaZeros t \ zetaZeros T, (mult ρ : ℝ) * (y / T) :=
          Finset.sum_le_sum hterm
      _ = (∑ ρ ∈ zetaZeros t \ zetaZeros T, (mult ρ : ℝ)) * (y / T) := by
          rw [Finset.sum_mul]
      _ ≤ (2 * C2 * Real.log (T + 3)) * (y / T) := by gcongr
      _ ≤ (2 * C2 * LT ^ 2) * (y / T) := by
          have : Real.log (T + 3) ≤ LT ^ 2 := by nlinarith
          gcongr
      _ = 2 * C2 * A := by rw [hAdef]; ring
  -- (e) the middle term
  have hmid : ‖P - ((y : ℂ) - Z0 - St)‖ ≤ 12 * C4 * A + 8 * C3 * LT ^ 2 := by
    have hn : ‖(2 * π * I : ℂ)‖ = 2 * π := by
      rw [norm_mul, Complex.norm_I, mul_one, norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le]
    have h2pi : (1 : ℝ) ≤ 2 * π := by linarith [Real.pi_gt_three]
    have h := congrArg norm hkey
    rw [norm_mul, hn] at h
    have htri : ‖Tp - Bm + I * L‖ ≤ ‖Tp‖ + ‖Bm‖ + ‖L‖ := by
      calc ‖Tp - Bm + I * L‖ ≤ ‖Tp - Bm‖ + ‖I * L‖ := norm_add_le _ _
        _ ≤ ‖Tp‖ + ‖Bm‖ + ‖L‖ := by
            rw [norm_mul, Complex.norm_I, one_mul]
            linarith [norm_sub_le Tp Bm]
    have hnn := norm_nonneg (P - ((y : ℂ) - Z0 - St))
    calc ‖P - ((y : ℂ) - Z0 - St)‖ ≤ 2 * π * ‖P - ((y : ℂ) - Z0 - St)‖ := by nlinarith
      _ = ‖Tp - Bm + I * L‖ := h
      _ ≤ ‖Tp‖ + ‖Bm‖ + ‖L‖ := htri
      _ ≤ 6 * C4 * A + 6 * C4 * A + 8 * C3 * LT ^ 2 := by linarith
      _ = 12 * C4 * A + 8 * C3 * LT ^ 2 := by ring
  -- assembly
  have hZ0b : ‖Z0‖ ≤ K0 * LT ^ 2 := by
    rw [← hK0]
    nlinarith
  rw [hE]
  calc ‖-(P - Carmichael.EF.psiChi (1 : DirichletCharacter ℂ 1) y)
        + (P - ((y : ℂ) - Z0 - St)) - Z0 - D‖
      ≤ ‖P - Carmichael.EF.psiChi (1 : DirichletCharacter ℂ 1) y‖
        + ‖P - ((y : ℂ) - Z0 - St)‖ + ‖Z0‖ + ‖D‖ := by
        have e1 := norm_sub_le (-(P - Carmichael.EF.psiChi (1 : DirichletCharacter ℂ 1) y)
          + (P - ((y : ℂ) - Z0 - St)) - Z0) D
        have e2 := norm_sub_le (-(P - Carmichael.EF.psiChi (1 : DirichletCharacter ℂ 1) y)
          + (P - ((y : ℂ) - Z0 - St))) Z0
        have e3 := norm_add_le (-(P - Carmichael.EF.psiChi (1 : DirichletCharacter ℂ 1) y))
          (P - ((y : ℂ) - Z0 - St))
        rw [norm_neg] at e3
        linarith
    _ ≤ (800 * A + 120 * LT ^ 2) + (12 * C4 * A + 8 * C3 * LT ^ 2) + K0 * LT ^ 2
        + 2 * C2 * A := by linarith
    _ ≤ (920 + K0 + 12 * C4 + 8 * C3 + 2 * C2) * (A + LT ^ 2) := by
        nlinarith [mul_nonneg hK0nn hA0, mul_nonneg hC4nn hA0, mul_nonneg hC3nn hA0,
          mul_nonneg hC2nn hA0, mul_nonneg hC4nn (sq_nonneg LT), mul_nonneg hC2nn (sq_nonneg LT),
          mul_nonneg hC3nn (sq_nonneg LT)]
    _ = (920 + K0 + 12 * C4 + 8 * C3 + 2 * C2) * (y * Real.log (T * y) ^ 2 / T
          + Real.log (T * y) ^ 2) := by rw [hAdef, hLT]

end EFx

end PPF.Explicit
