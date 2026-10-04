import PPF.RH.Reflection
import PPF.RH.ZeroCount
import PPF.Vendor.ExplicitFormula

/-!
# D4: good horizontal lines for `ζ′/ζ` across `−1/2 ≤ Re s ≤ 2`

For `1/2 ≤ σ ≤ 2`: `Carmichael.EF.exists_good_height` for `etaFun`
(`ζ′/ζ = η′/η − g′/g`, `g = 1 − 2^{1−s}`), avoiding the ordinates of the zeros of
`g` (`Re = 1`, `Im ∈ (2π/log 2) ℤ`), as in the opening of
`Carmichael.EF.contour_zeta`. Conjugation symmetry handles `−t`.
For `−1/2 ≤ σ < 1/2`: reflect with D2 to `1 − σ ∈ (1/2, 3/2]` at height `∓t`.
-/

namespace PPF.RH

open Complex
open scoped Real

-- `hs` is part of the frozen interface; the symmetry holds on all of `ℂ`.
set_option linter.unusedVariables false in
/-- Conjugation symmetry of `ζ` on the right half-plane. -/
theorem riemannZeta_conj {s : ℂ} (hs : 0 < s.re) :
    riemannZeta ((starRingEnd ℂ) s) = (starRingEnd ℂ) (riemannZeta s) :=
  _root_.riemannZeta_conj s

-- `hs`, `hs1` are part of the frozen interface.
set_option linter.unusedVariables false in
theorem deriv_riemannZeta_conj {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    deriv riemannZeta ((starRingEnd ℂ) s) = (starRingEnd ℂ) (deriv riemannZeta s) := by
  have hfun : (starRingEnd ℂ) ∘ riemannZeta ∘ (starRingEnd ℂ) = riemannZeta := by
    funext z
    simp [Function.comp, _root_.riemannZeta_conj]
  have h := congrFun (deriv_conj_conj (f := riemannZeta)) ((starRingEnd ℂ) s)
  rw [hfun] at h
  simpa using h

namespace GH

open Carmichael Carmichael.EF

/-- `ζ′/ζ = η′/η − g′/g` on `Re s > 0`, `s ≠ 1`, where `g` and `ζ` do not vanish. -/
lemma logDeriv_zeta_split {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) (hg : gFun s ≠ 0)
    (hz : riemannZeta s ≠ 0) :
    deriv riemannZeta s / riemannZeta s
      = deriv etaFun s / etaFun s - deriv gFun s / gFun s := by
  have hopen : IsOpen {z : ℂ | 0 < z.re ∧ z ≠ 1} := by
    have h1 : IsOpen {z : ℂ | 0 < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have h2 : IsOpen {z : ℂ | z ≠ 1} := isOpen_compl_singleton
    exact h1.inter h2
  have hev : etaFun =ᶠ[nhds s] fun z => gFun z * riemannZeta z := by
    filter_upwards [hopen.mem_nhds (⟨hs0, hs1⟩ : s ∈ {z : ℂ | 0 < z.re ∧ z ≠ 1})]
      with z hz'
    exact etaFun_eq_mul hz'.1 hz'.2
  have hzd : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hgd : DifferentiableAt ℂ gFun s := differentiable_gFun s
  have hderiv : deriv etaFun s
      = deriv gFun s * riemannZeta s + gFun s * deriv riemannZeta s :=
    ((hgd.hasDerivAt.mul hzd.hasDerivAt).congr_of_eventuallyEq hev).deriv
  have heta : etaFun s = gFun s * riemannZeta s := etaFun_eq_mul hs0 hs1
  rw [hderiv, heta]
  field_simp
  ring

/-- `‖g′‖ ≤ 1` on `Re s ≥ 1/2`. -/
lemma norm_deriv_gFun_le_one {s : ℂ} (hre : 1 / 2 ≤ s.re) : ‖deriv gFun s‖ ≤ 1 := by
  rw [deriv_gFun, norm_mul, norm_two_cpow, Complex.norm_real,
    Real.norm_of_nonneg (Real.log_nonneg (by norm_num))]
  have h1 : Real.log 2 ≤ 0.6931471808 := Real.log_two_lt_d9.le
  have h2 : (2:ℝ) ^ (1 - s.re) ≤ (2:ℝ) ^ ((1:ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h3 : (2:ℝ) ^ ((1:ℝ) / 2) ≤ 1.4143 := by
    have h4 : ((2:ℝ) ^ ((1:ℝ) / 2)) ^ (2:ℕ) = 2 := by
      rw [← Real.rpow_natCast ((2:ℝ) ^ ((1:ℝ) / 2)) 2, ← Real.rpow_mul (by norm_num)]
      norm_num
    by_contra hlt
    push Not at hlt
    have h5 : ((1.4143:ℝ)) ^ (2:ℕ) ≤ ((2:ℝ) ^ ((1:ℝ) / 2)) ^ (2:ℕ) :=
      pow_le_pow_left₀ (by norm_num) hlt.le _
    rw [h4] at h5
    norm_num at h5
  have h6 : (0:ℝ) ≤ (2:ℝ) ^ (1 - s.re) := Real.rpow_nonneg (by norm_num) _
  have h7 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith

/-- `‖g‖ ≥ 1/10` on `Re s ≥ 5/4`. -/
lemma norm_gFun_ge_right {s : ℂ} (hre : 5 / 4 ≤ s.re) : 1 / 10 ≤ ‖gFun s‖ := by
  have h1 : (2:ℝ) ^ (1 - s.re) ≤ 9 / 10 := by
    have h2 : (2:ℝ) ^ (1 - s.re) ≤ (2:ℝ) ^ (-(1:ℝ) / 4) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h3 : (2:ℝ) ^ (-(1:ℝ) / 4) ≤ 9 / 10 := by
      have h4 : ((2:ℝ) ^ (-(1:ℝ) / 4)) ^ (4:ℕ) = 1 / 2 := by
        rw [← Real.rpow_natCast ((2:ℝ) ^ (-(1:ℝ) / 4)) 4, ← Real.rpow_mul (by norm_num)]
        norm_num
      by_contra hlt
      push Not at hlt
      have h5 : ((9 / 10 : ℝ)) ^ (4:ℕ) ≤ ((2:ℝ) ^ (-(1:ℝ) / 4)) ^ (4:ℕ) :=
        pow_le_pow_left₀ (by norm_num) hlt.le _
      rw [h4] at h5
      norm_num at h5
    linarith
  calc (1 / 10 : ℝ) ≤ ‖(1:ℂ)‖ - ‖(2:ℂ) ^ ((1:ℂ) - s)‖ := by
        rw [norm_two_cpow, norm_one]
        linarith
    _ ≤ ‖(1:ℂ) - (2:ℂ) ^ ((1:ℂ) - s)‖ := norm_sub_norm_le _ _
    _ = ‖gFun s‖ := rfl

/-- Lower bound for `‖g‖` on a horizontal line with a sine lower bound. -/
lemma norm_gFun_ge {σ t δ : ℝ} (hδ1 : δ ≤ 1 / 10)
    (hsin : δ ≤ (4 / 5) * |Real.sin (t * Real.log 2)|) :
    δ ≤ ‖gFun ((σ:ℂ) + t * I)‖ := by
  have hre : ((σ:ℂ) + t * I).re = σ := by simp
  rcases le_or_gt σ (5 / 8) with h | h
  · have := norm_gFun_ge_left (s := (σ:ℂ) + t * I) (by rw [hre]; exact h)
    linarith
  · rcases le_or_gt σ (5 / 4) with h' | h'
    · exact le_trans hsin (norm_gFun_ge_sin (by linarith) h')
    · have := norm_gFun_ge_right (s := (σ:ℂ) + t * I) (by rw [hre]; exact h'.le)
      linarith

lemma conj_add_mul_I (σ t : ℝ) :
    (starRingEnd ℂ) ((σ:ℂ) + t * I) = (σ:ℂ) - t * I := by
  apply Complex.ext <;> simp

end GH

-- `hRH` is part of the frozen interface; reflection through D2 makes D4 unconditional.
set_option linter.unusedVariables false in
open Carmichael Carmichael.EF GH in
/-- D4: one height `t ∈ [T, T+1]` good at `+t` and `−t` for all `σ ∈ [−1/2, 2]`. -/
theorem exists_good_height_zeta (hRH : RiemannHypothesis) :
    ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → ∃ t : ℝ, T ≤ t ∧ t ≤ T + 1 ∧
      ∀ σ : ℝ, -1 / 2 ≤ σ → σ ≤ 2 →
        riemannZeta ((σ : ℂ) + t * I) ≠ 0 ∧ riemannZeta ((σ : ℂ) - t * I) ≠ 0 ∧
        ‖deriv riemannZeta ((σ : ℂ) + t * I) / riemannZeta ((σ : ℂ) + t * I)‖
          ≤ C * Real.log (T + 4) ^ 2 ∧
        ‖deriv riemannZeta ((σ : ℂ) - t * I) / riemannZeta ((σ : ℂ) - t * I)‖
          ≤ C * Real.log (T + 4) ^ 2 := by
  obtain ⟨C₂, hC₂⟩ := norm_logDeriv_zeta_reflect_le
  set C₂' : ℝ := max C₂ 0 with hC₂'
  refine ⟨1010000 + C₂', fun T hT => ?_⟩
  have hDD : DiskData etaFun 1 := diskData_etaFun
  set L : ℝ := Real.log (T + 4) with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hL0 : 0 < L := by linarith
  have hL1' : Real.log ((1:ℝ) * (T + 4)) = L := by rw [one_mul]
  -- the pigeonholed `g`-ordinates
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
  -- right part at `+t`
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
  -- right part at `−t`, by conjugation
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
    rw [hc, riemannZeta_conj hs0, deriv_riemannZeta_conj hs0 hs1]
    refine ⟨fun h0 => hz ?_, ?_⟩
    · rwa [map_eq_zero] at h0
    · rw [← map_div₀, Complex.norm_conj]
      exact hb
  -- the reflection constant
  have hlogt : Real.log (t + 2) ≤ L := by
    rw [hLdef]
    exact Real.log_le_log (by linarith) (by linarith)
  have hC₂L : C₂ * Real.log (t + 2) ≤ C₂' * L ^ 2 := by
    have h0 : 0 ≤ Real.log (t + 2) := Real.log_nonneg (by linarith)
    calc C₂ * Real.log (t + 2) ≤ C₂' * Real.log (t + 2) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) h0
      _ ≤ C₂' * L ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
          nlinarith
  have hLsq : 0 ≤ L ^ 2 := sq_nonneg L
  have hC₂'0 : 0 ≤ C₂' := le_max_right _ _
  -- left part, generic in the sign of the height
  have hleft : ∀ (σ u : ℝ), -1 / 2 ≤ σ → σ < 1 / 2 → |u| = t →
      riemannZeta (((1 - σ : ℝ) : ℂ) - u * I) ≠ 0 →
      ‖deriv riemannZeta (((1 - σ : ℝ) : ℂ) - u * I)
          / riemannZeta (((1 - σ : ℝ) : ℂ) - u * I)‖ ≤ 1010000 * L ^ 2 →
      riemannZeta ((σ:ℂ) + u * I) ≠ 0 ∧
      ‖deriv riemannZeta ((σ:ℂ) + u * I) / riemannZeta ((σ:ℂ) + u * I)‖
        ≤ (1010000 + C₂') * L ^ 2 := by
    intro σ u h1 h2 hu hwz hwb
    set w : ℂ := ((1 - σ : ℝ) : ℂ) - u * I with hwdef
    have hwre : w.re = 1 - σ := by simp [hwdef]
    have hwim : w.im = -u := by simp [hwdef]
    have h1w : (1:ℂ) - w = (σ:ℂ) + u * I := by
      rw [hwdef]
      push_cast
      ring
    have habs : |w.im| = t := by rw [hwim, abs_neg, hu]
    obtain ⟨hnz, hb⟩ := hC₂ w (by rw [hwre]; linarith) (by rw [hwre]; linarith)
      (by rw [habs]; linarith) hwz
    rw [h1w] at hnz hb
    rw [habs] at hb
    refine ⟨hnz, ?_⟩
    set A := deriv riemannZeta ((σ:ℂ) + u * I) / riemannZeta ((σ:ℂ) + u * I)
    set B := deriv riemannZeta w / riemannZeta w
    calc ‖A‖ = ‖(A + B) - B‖ := by ring_nf
      _ ≤ ‖A + B‖ + ‖B‖ := norm_sub_le _ _
      _ ≤ C₂ * Real.log (t + 2) + 1010000 * L ^ 2 := add_le_add hb hwb
      _ ≤ C₂' * L ^ 2 + 1010000 * L ^ 2 := by linarith
      _ = (1010000 + C₂') * L ^ 2 := by ring
  refine ⟨t, ht1, ht2, ?_⟩
  intro σ hσ1 hσ2
  have ht0 : 0 ≤ t := by linarith
  rcases le_or_gt (1 / 2) σ with h | h
  · obtain ⟨hz1, hb1⟩ := hR σ h hσ2
    obtain ⟨hz2, hb2⟩ := hR' σ h hσ2
    refine ⟨hz1, hz2, ?_, ?_⟩
    · nlinarith
    · nlinarith
  · -- `+t`: reflect to `1 − σ − t i`
    have hσ' : 1 / 2 ≤ 1 - σ := by linarith
    have hσ'' : 1 - σ ≤ 2 := by linarith
    obtain ⟨hwz1, hwb1⟩ := hR' (1 - σ) hσ' hσ''
    obtain ⟨hz1, hb1⟩ := hleft σ t hσ1 h (abs_of_nonneg ht0)
      (by exact_mod_cast hwz1) (by exact_mod_cast hwb1)
    -- `−t`: reflect to `1 − σ + t i`
    obtain ⟨hwz2, hwb2⟩ := hR (1 - σ) hσ' hσ''
    have hneg : ∀ v : ℂ, ((1 - σ : ℝ) : ℂ) - ((-t : ℝ) : ℂ) * I = ((1 - σ : ℝ) : ℂ) + t * I := by
      intro _; push_cast; ring
    have hneg' : (σ:ℂ) + ((-t : ℝ) : ℂ) * I = (σ:ℂ) - t * I := by push_cast; ring
    obtain ⟨hz2, hb2⟩ := hleft σ (-t) hσ1 h (by rw [abs_neg, abs_of_nonneg ht0])
      (by rw [hneg 0]; exact_mod_cast hwz2) (by rw [hneg 0]; exact_mod_cast hwb2)
    rw [hneg'] at hz2 hb2
    exact ⟨hz1, hz2, hb1, hb2⟩

end PPF.RH
