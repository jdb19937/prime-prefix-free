import PPF.RH.Digamma
import PPF.Vendor.ExplicitFormula

/-!
# D2, D3: the functional equation for `ζ′/ζ`, and the line `Re s = −1/2`

Mathlib's `riemannZeta_one_sub`: `ζ(1 − w) = 2 (2π)^{−w} Γ(w) cos(πw/2) ζ(w)`.
Taking log-derivatives, `ζ′/ζ(1 − w) + ζ′/ζ(w) = log(2π) − ψ(w) + (π/2) tan(πw/2)`,
and `|tan(πw/2)| ≤ 2` once `|Im w| ≥ 2`; D1 bounds `ψ`.
On `Re w = 3/2`, `ζ′/ζ` is bounded by `∑ Λ(n) n^{−3/2}`, so D2 gives D3.
-/

namespace PPF.RH

open Complex
open scoped Real

namespace Refl

/-- `‖sin z‖ ≤ 2 ‖cos z‖` and `cos z ≠ 0` once `|Im z| ≥ 1`. -/
lemma norm_sin_le_two_mul_norm_cos {z : ℂ} (hz : 1 ≤ |z.im|) :
    cos z ≠ 0 ∧ ‖sin z‖ ≤ 2 * ‖cos z‖ := by
  set a := Real.exp z.im with ha
  set b := Real.exp (-z.im) with hb
  have ha0 : 0 < a := Real.exp_pos _
  have hb0 : 0 < b := Real.exp_pos _
  have hab : a * b = 1 := by rw [ha, hb, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have e1 : ‖exp (z * I)‖ = b := by rw [norm_exp]; simp [hb]
  have e2 : ‖exp (-z * I)‖ = a := by rw [norm_exp]; simp [ha]
  have hcos : 2 * cos z = exp (z * I) + exp (-z * I) := by
    rw [Complex.cos]; ring
  have hsin : 2 * sin z = (exp (-z * I) - exp (z * I)) * I := by
    rw [Complex.sin]; ring
  have hcos_ge : |a - b| ≤ 2 * ‖cos z‖ := by
    have : ‖2 * cos z‖ = 2 * ‖cos z‖ := by rw [norm_mul]; norm_num
    rw [← this, hcos, ← e1, ← e2, add_comm]
    have := abs_norm_sub_norm_le (exp (-z * I)) (-exp (z * I))
    rwa [norm_neg, sub_neg_eq_add] at this
  have hsin_le : 2 * ‖sin z‖ ≤ a + b := by
    have : ‖2 * sin z‖ = 2 * ‖sin z‖ := by rw [norm_mul]; norm_num
    rw [← this, hsin, norm_mul, norm_I, mul_one]
    calc ‖exp (-z * I) - exp (z * I)‖ ≤ ‖exp (-z * I)‖ + ‖exp (z * I)‖ := norm_sub_le _ _
      _ = a + b := by rw [e1, e2]
  -- `|Im z| ≥ 1` forces the larger of `a, b` to be at least `2`
  have hkey : a + b ≤ 2 * |a - b| ∧ 0 < |a - b| := by
    rcases le_or_gt 0 z.im with hy | hy
    · have hy1 : 1 ≤ z.im := by rwa [abs_of_nonneg hy] at hz
      have ha2 : 2 ≤ a := by
        have := Real.add_one_le_exp z.im
        rw [ha]; linarith
      have hb' : b = 1 / a := by field_simp; linarith [hab]
      have hb1 : b ≤ 1 / 2 := by
        rw [hb']; rw [div_le_div_iff₀ ha0 (by norm_num)]; linarith
      rw [abs_of_pos (by linarith)]
      constructor <;> linarith
    · have hy1 : 1 ≤ -z.im := by rwa [abs_of_neg hy] at hz
      have hb2 : 2 ≤ b := by
        have := Real.add_one_le_exp (-z.im)
        rw [hb]; linarith
      have ha' : a = 1 / b := by field_simp; linarith [hab]
      have ha1 : a ≤ 1 / 2 := by
        rw [ha']; rw [div_le_div_iff₀ hb0 (by norm_num)]; linarith
      rw [abs_of_neg (by linarith)]
      constructor <;> linarith
  refine ⟨?_, ?_⟩
  · intro h0
    rw [h0, norm_zero, mul_zero] at hcos_ge
    linarith [hkey.2]
  · linarith [hkey.1]

/-- The exponential factor of the functional equation. -/
noncomputable def expFac (s : ℂ) : ℂ := 2 * (2 * (π : ℂ)) ^ (-s)

lemma hasDerivAt_expFac (w : ℂ) :
    HasDerivAt expFac (2 * ((2 * (π : ℂ)) ^ (-w) * Complex.log (2 * π) * (-1))) w := by
  have h1 : HasDerivAt (fun s : ℂ => -s) (-1) w := (hasDerivAt_id w).neg
  have h2 := h1.const_cpow (c := 2 * (π : ℂ)) (Or.inl (by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero this))
  exact h2.const_mul 2

lemma expFac_ne_zero (w : ℂ) : expFac w ≠ 0 := by
  unfold expFac
  refine mul_ne_zero two_ne_zero ?_
  rw [Ne, cpow_eq_zero_iff]
  have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  exact fun h => (mul_ne_zero two_ne_zero this) h.1

lemma logDeriv_expFac (w : ℂ) : logDeriv expFac w = -Complex.log (2 * π) := by
  rw [logDeriv_apply, (hasDerivAt_expFac w).deriv]
  have h := expFac_ne_zero w
  unfold expFac at h ⊢
  field_simp

lemma hasDerivAt_cosFac (w : ℂ) :
    HasDerivAt (fun s : ℂ => cos ((π : ℂ) * s / 2)) (-sin ((π : ℂ) * w / 2) * ((π : ℂ) / 2)) w := by
  have h1 : HasDerivAt (fun s : ℂ => (π : ℂ) * s / 2) ((π : ℂ) / 2) w := by
    have := ((hasDerivAt_id w).const_mul (π : ℂ)).div_const 2
    simpa using this
  exact (Complex.hasDerivAt_cos _).comp w h1

lemma im_pi_mul_div_two (w : ℂ) : ((π : ℂ) * w / 2).im = π * w.im / 2 := by
  simp [Complex.mul_im, Complex.div_ofNat_im]

/-- Reflection identity for `ζ′/ζ`, valid off the real axis. -/
lemma reflect_identity {w : ℂ} (hw : 2 ≤ |w.im|) (hz : riemannZeta w ≠ 0) :
    riemannZeta (1 - w) ≠ 0 ∧
    deriv riemannZeta (1 - w) / riemannZeta (1 - w) + deriv riemannZeta w / riemannZeta w
      = -(logDeriv expFac w + Complex.digamma w
          + (-sin ((π : ℂ) * w / 2) * ((π : ℂ) / 2)) / cos ((π : ℂ) * w / 2)) := by
  have hwim : w.im ≠ 0 := by intro h; rw [h, abs_zero] at hw; linarith
  have hnotnat : ∀ s : ℂ, s.im ≠ 0 → ∀ n : ℕ, s ≠ -n := by
    intro s hs n h; apply hs; rw [h]; simp
  have hnot1 : ∀ s : ℂ, s.im ≠ 0 → s ≠ 1 := by
    intro s hs h; apply hs; rw [h]; simp
  -- cosine factor nonvanishing
  have hcosw : cos ((π : ℂ) * w / 2) ≠ 0 := by
    refine (norm_sin_le_two_mul_norm_cos ?_).1
    rw [im_pi_mul_div_two, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_two]
    have : 2 * 2 ≤ π * |w.im| := by nlinarith [Real.pi_gt_three]
    linarith
  have hG : Gamma w ≠ 0 := Complex.Gamma_ne_zero (hnotnat w hwim)
  set F : ℂ → ℂ := fun s => riemannZeta (1 - s) with hF
  set G : ℂ → ℂ := fun s => expFac s * Gamma s * cos ((π : ℂ) * s / 2) * riemannZeta s with hGdef
  have hFG : F =ᶠ[nhds w] G := by
    have hopen : IsOpen {s : ℂ | s.im ≠ 0} :=
      isOpen_ne_fun Complex.continuous_im continuous_const
    filter_upwards [hopen.mem_nhds hwim] with s hs
    simp only [hF, hGdef, expFac]
    exact riemannZeta_one_sub (hnotnat s hs) (hnot1 s hs)
  have hFw : F w = G w := hFG.eq_of_nhds
  have hGw : G w ≠ 0 := by
    simp only [hGdef]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (expFac_ne_zero w) hG) hcosw) hz
  have hzeta1 : riemannZeta (1 - w) ≠ 0 := by
    have : F w = riemannZeta (1 - w) := rfl
    rw [← this, hFw]; exact hGw
  refine ⟨hzeta1, ?_⟩
  -- log-derivative of `F`
  have hw1 : 1 - w ≠ 1 := by
    intro h; apply hwim; have : w = 0 := by linear_combination -h
    rw [this]; simp
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
  -- log-derivative of `G`, factor by factor
  have dE : DifferentiableAt ℂ expFac w := (hasDerivAt_expFac w).differentiableAt
  have dΓ : DifferentiableAt ℂ Gamma w := Complex.differentiableAt_Gamma w (hnotnat w hwim)
  have dC : DifferentiableAt ℂ (fun s : ℂ => cos ((π : ℂ) * s / 2)) w :=
    (hasDerivAt_cosFac w).differentiableAt
  have dZ : DifferentiableAt ℂ riemannZeta w := differentiableAt_riemannZeta (hnot1 w hwim)
  have l1 : logDeriv (fun s => expFac s * Gamma s) w = logDeriv expFac w + logDeriv Gamma w :=
    logDeriv_mul w (expFac_ne_zero w) hG dE dΓ
  have l2 : logDeriv (fun s => expFac s * Gamma s * cos ((π : ℂ) * s / 2)) w
      = logDeriv (fun s => expFac s * Gamma s) w + logDeriv (fun s : ℂ => cos ((π : ℂ) * s / 2)) w :=
    logDeriv_mul (f := fun s => expFac s * Gamma s) (g := fun s : ℂ => cos ((π : ℂ) * s / 2)) w
      (mul_ne_zero (expFac_ne_zero w) hG) hcosw (dE.mul dΓ) dC
  have l3 : logDeriv G w
      = logDeriv (fun s => expFac s * Gamma s * cos ((π : ℂ) * s / 2)) w + logDeriv riemannZeta w :=
    logDeriv_mul (f := fun s => expFac s * Gamma s * cos ((π : ℂ) * s / 2)) (g := riemannZeta) w
      (mul_ne_zero (mul_ne_zero (expFac_ne_zero w) hG) hcosw) hz ((dE.mul dΓ).mul dC) dZ
  have lC : logDeriv (fun s : ℂ => cos ((π : ℂ) * s / 2)) w
      = (-sin ((π : ℂ) * w / 2) * ((π : ℂ) / 2)) / cos ((π : ℂ) * w / 2) := by
    rw [logDeriv_apply, (hasDerivAt_cosFac w).deriv]
  have hdig : logDeriv Gamma w = Complex.digamma w := rfl
  have hZ : logDeriv riemannZeta w = deriv riemannZeta w / riemannZeta w := logDeriv_apply _ _
  have key : -(deriv riemannZeta (1 - w) / riemannZeta (1 - w))
      = logDeriv expFac w + Complex.digamma w
        + (-sin ((π : ℂ) * w / 2) * ((π : ℂ) / 2)) / cos ((π : ℂ) * w / 2)
        + deriv riemannZeta w / riemannZeta w := by
    rw [← hlogF, hlogFG, l3, l2, l1, lC, hdig, hZ]
  linear_combination -key

end Refl

/-- D2 (unconditional). -/
theorem norm_logDeriv_zeta_reflect_le :
    ∃ C : ℝ, ∀ w : ℂ, 1 / 2 ≤ w.re → w.re ≤ 3 / 2 → 2 ≤ |w.im| → riemannZeta w ≠ 0 →
      riemannZeta (1 - w) ≠ 0 ∧
      ‖deriv riemannZeta (1 - w) / riemannZeta (1 - w) + deriv riemannZeta w / riemannZeta w‖
        ≤ C * Real.log (|w.im| + 2) := by
  obtain ⟨C₁, hC₁⟩ := norm_digamma_le
  set K : ℝ := ‖Complex.log (2 * π)‖ with hK
  refine ⟨max C₁ 0 + K + π, fun w hre1 hre2 him hz => ?_⟩
  obtain ⟨hz1, hid⟩ := Refl.reflect_identity him hz
  refine ⟨hz1, ?_⟩
  rw [hid, norm_neg]
  have hlog1 : 1 ≤ Real.log (|w.im| + 2) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  have hlog0 : 0 ≤ Real.log (|w.im| + 2) := by linarith
  have hψ : ‖Complex.digamma w‖ ≤ max C₁ 0 * Real.log (|w.im| + 2) :=
    (hC₁ w hre1 (by linarith) (by linarith)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hlog0)
  have htan : ‖(-sin ((π : ℂ) * w / 2) * ((π : ℂ) / 2)) / cos ((π : ℂ) * w / 2)‖ ≤ π := by
    have hz' : 1 ≤ |((π : ℂ) * w / 2).im| := by
      rw [Refl.im_pi_mul_div_two, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_two]
      have : 2 * 1 ≤ π * |w.im| := by nlinarith [Real.pi_gt_three]
      linarith
    obtain ⟨hc0, hsc⟩ := Refl.norm_sin_le_two_mul_norm_cos hz'
    have hcpos : 0 < ‖cos ((π : ℂ) * w / 2)‖ := norm_pos_iff.mpr hc0
    rw [norm_div, norm_mul, norm_neg, div_le_iff₀ hcpos]
    have hpi : ‖(π : ℂ) / 2‖ = π / 2 := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]; norm_num
    rw [hpi]
    nlinarith [Real.pi_pos]
  rw [Refl.logDeriv_expFac w]
  calc ‖-Complex.log (2 * π) + Complex.digamma w
          + (-sin ((π : ℂ) * w / 2) * ((π : ℂ) / 2)) / cos ((π : ℂ) * w / 2)‖
      ≤ ‖-Complex.log (2 * π)‖ + ‖Complex.digamma w‖
          + ‖(-sin ((π : ℂ) * w / 2) * ((π : ℂ) / 2)) / cos ((π : ℂ) * w / 2)‖ :=
        norm_add₃_le
    _ ≤ K + max C₁ 0 * Real.log (|w.im| + 2) + π := by
        rw [norm_neg]; gcongr
    _ ≤ (max C₁ 0 + K + π) * Real.log (|w.im| + 2) := by
        have hK0 : 0 ≤ K := norm_nonneg _
        nlinarith [Real.pi_pos]

/-- D3: `ζ′/ζ` on the line `Re s = −1/2`. -/
theorem left_line_bound (hRH : RiemannHypothesis) :
    ∃ C : ℝ, ∀ t : ℝ,
      riemannZeta ((-1 / 2 : ℝ) + t * I) ≠ 0 ∧
      ‖deriv riemannZeta ((-1 / 2 : ℝ) + t * I) / riemannZeta ((-1 / 2 : ℝ) + t * I)‖
        ≤ C * Real.log (|t| + 2) := by
  set s : ℝ → ℂ := fun t => ((-1 / 2 : ℝ) : ℂ) + t * I with hs
  have hsre : ∀ t, (s t).re = -1 / 2 := by intro t; simp [hs]
  have hs1 : ∀ t, s t ≠ 1 := by
    intro t h; have := hsre t; rw [h] at this; norm_num at this
  -- nonvanishing on the line, from RH
  have hnz : ∀ t, riemannZeta (s t) ≠ 0 := by
    intro t h0
    have htriv : ¬∃ n : ℕ, s t = -2 * (n + 1) := by
      rintro ⟨n, hn⟩
      have h1 := congrArg Complex.re hn
      rw [hsre t] at h1
      simp at h1
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have := hRH (s t) h0 htriv (hs1 t)
    rw [hsre t] at this; norm_num at this
  -- far range `|t| ≥ 2`: reflect to `Re = 3/2`
  obtain ⟨C₂, hC₂⟩ := norm_logDeriv_zeta_reflect_le
  have hfar : ∀ t : ℝ, 2 ≤ |t| →
      ‖deriv riemannZeta (s t) / riemannZeta (s t)‖ ≤ (max C₂ 0 + 24) * Real.log (|t| + 2) := by
    intro t ht
    set w : ℂ := ((3 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I with hw
    have hwre : w.re = 3 / 2 := by simp [hw]
    have hwim : w.im = -t := by simp [hw]
    have hzw : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by rw [hwre]; norm_num)
    have him : 2 ≤ |w.im| := by rw [hwim, abs_neg]; exact ht
    obtain ⟨-, hb⟩ := hC₂ w (by rw [hwre]; norm_num) (by rw [hwre]) him hzw
    have h1w : 1 - w = s t := by
      simp only [hw, hs]; push_cast; ring
    rw [h1w, hwim, abs_neg] at hb
    -- `ζ′/ζ` on `Re = 3/2`
    have hright : ‖deriv riemannZeta w / riemannZeta w‖ ≤ 24 := by
      have := Carmichael.EF.norm_logDeriv_LFunction_le (N := 1) (1 : DirichletCharacter ℂ 1)
        (c := 3 / 2) (by norm_num) (by norm_num) (-t)
      rw [DirichletCharacter.LFunction_modOne_eq] at this
      have hw' : ((3 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I = w := rfl
      rw [hw'] at this
      norm_num at this ⊢
      exact this
    have hlog1 : 1 ≤ Real.log (|t| + 2) := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      have := Real.exp_one_lt_d9
      linarith
    have hlog0 : 0 ≤ Real.log (|t| + 2) := by linarith
    calc ‖deriv riemannZeta (s t) / riemannZeta (s t)‖
        = ‖(deriv riemannZeta (s t) / riemannZeta (s t) + deriv riemannZeta w / riemannZeta w)
            - deriv riemannZeta w / riemannZeta w‖ := by ring_nf
      _ ≤ ‖deriv riemannZeta (s t) / riemannZeta (s t) + deriv riemannZeta w / riemannZeta w‖
            + ‖deriv riemannZeta w / riemannZeta w‖ := norm_sub_le _ _
      _ ≤ C₂ * Real.log (|t| + 2) + 24 := add_le_add hb hright
      _ ≤ (max C₂ 0 + 24) * Real.log (|t| + 2) := by
          have : C₂ * Real.log (|t| + 2) ≤ max C₂ 0 * Real.log (|t| + 2) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hlog0
          nlinarith
  -- near range `|t| ≤ 2`: continuity on a compact interval
  have hcont : Continuous (fun t : ℝ => deriv riemannZeta (s t) / riemannZeta (s t)) := by
    have hsc : Continuous s := by
      simp only [hs]; fun_prop
    have hdz : ContinuousOn (deriv riemannZeta) {1}ᶜ :=
      (analyticOn_riemannZeta.deriv).continuousOn
    have hz : ContinuousOn riemannZeta {1}ᶜ := analyticOn_riemannZeta.continuousOn
    refine Continuous.div ?_ ?_ hnz
    · exact hdz.comp_continuous hsc (fun t => hs1 t)
    · exact hz.comp_continuous hsc (fun t => hs1 t)
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    hcont.continuousOn
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨max (max C₂ 0 + 24) (max B 0 / Real.log 2), fun t => ⟨hnz t, ?_⟩⟩
  have hlogt : Real.log 2 ≤ Real.log (|t| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hlog0 : 0 ≤ Real.log (|t| + 2) := by linarith
  show ‖deriv riemannZeta (s t) / riemannZeta (s t)‖ ≤ _
  rcases le_or_gt 2 |t| with ht | ht
  · exact (hfar t ht).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hlog0)
  · have hmem : t ∈ Set.Icc (-2 : ℝ) 2 := by
      rw [abs_lt] at ht; exact ⟨ht.1.le, ht.2.le⟩
    have h1 := hB t hmem
    calc ‖deriv riemannZeta (s t) / riemannZeta (s t)‖ ≤ max B 0 := h1.trans (le_max_left _ _)
      _ = max B 0 / Real.log 2 * Real.log 2 := by field_simp
      _ ≤ max B 0 / Real.log 2 * Real.log (|t| + 2) := by
          apply mul_le_mul_of_nonneg_left hlogt
          exact div_nonneg (le_max_right _ _) hlog2.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hlog0

end PPF.RH
