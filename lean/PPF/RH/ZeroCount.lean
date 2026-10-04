import PPF.RH.Defs
import PPF.Vendor.ZeroCount

/-!
# Zeros of ζ under RH: finiteness and unit-window counts

Reuses `Carmichael.sum_ord_etaFun_disk_le` (vendored `ZeroCount`) together with
`Carmichael.analyticOrderNatAt_zeta_le_etaFun`: `ord_ζ ≤ ord_η`, and a unit
window on `Re = 1/2` lies in a `13/8`-disk around `2 + i t₀`.
-/

namespace PPF.RH

open Complex

-- `hRH` is part of the frozen interface; finiteness holds unconditionally.
set_option linter.unusedVariables false in
/-- Under RH the critical-strip zeros with `|Im| ≤ T` form a finite set. -/
theorem zetaZeros_finite (hRH : RiemannHypothesis) (T : ℝ) : (zeroSet T).Finite := by
  have hbox := Carmichael.isCompact_box 0 T
  apply (hbox.inter_riemannZetaZeros_finite).subset
  rintro s ⟨h1, h2, h3, h4⟩
  exact ⟨⟨h1.le, h2.le, h3⟩, h4⟩

theorem mem_zetaZeros (hRH : RiemannHypothesis) {T : ℝ} {ρ : ℂ} :
    ρ ∈ zetaZeros T ↔ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T ∧ riemannZeta ρ = 0 := by
  unfold zetaZeros
  rw [dif_pos (zetaZeros_finite hRH T), Set.Finite.mem_toFinset]
  rfl

theorem re_eq_half_of_mem (hRH : RiemannHypothesis) {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ zetaZeros T) : ρ.re = 1 / 2 := by
  obtain ⟨h1, h2, _, h4⟩ := (mem_zetaZeros hRH).mp hρ
  apply hRH ρ h4
  · rintro ⟨n, hn⟩
    have : ρ.re = -2 * ((n : ℝ) + 1) := by rw [hn]; simp
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · intro h
    rw [h] at h2
    simp at h2

namespace ZC

/-- A zero in the unit window `[t, t+1]` lies in the `13/8`-disk around `2 + i(t + 1/2)`. -/
lemma mem_disk_of_window (hRH : RiemannHypothesis) {T t : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ zetaZeros T) (h1 : t ≤ ρ.im) (h2 : ρ.im ≤ t + 1) :
    ρ ∈ Metric.closedBall ((2 : ℂ) + ((t + 1 / 2 : ℝ) : ℂ) * I) (13 / 8 : ℝ) := by
  have hre := re_eq_half_of_mem hRH hρ
  rw [Metric.mem_closedBall, Complex.dist_eq]
  apply Carmichael.norm_le_of_sq_le (by norm_num)
  have hr : (ρ - ((2 : ℂ) + ((t + 1 / 2 : ℝ) : ℂ) * I)).re = ρ.re - 2 := by simp
  have hi : (ρ - ((2 : ℂ) + ((t + 1 / 2 : ℝ) : ℂ) * I)).im = ρ.im - (t + 1 / 2) := by simp
  rw [hr, hi, hre]
  have : (ρ.im - (t + 1 / 2)) ^ 2 ≤ 1 / 4 := by nlinarith
  nlinarith

lemma log_shift_le (t : ℝ) : Real.log (|t + 1 / 2| + 2) ≤ 2 * Real.log (|t| + 2) := by
  have hpos : (0 : ℝ) < |t| + 2 := by positivity
  have hle : |t + 1 / 2| + 2 ≤ (|t| + 2) ^ 2 := by
    have := abs_add_le t (1 / 2)
    have h0 : (0 : ℝ) ≤ |t| := abs_nonneg t
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
    nlinarith
  calc Real.log (|t + 1 / 2| + 2) ≤ Real.log ((|t| + 2) ^ 2) :=
        Real.log_le_log (by positivity) hle
    _ = 2 * Real.log (|t| + 2) := by rw [Real.log_pow]; norm_num

end ZC

/-- K2: zeros (with multiplicity) in a unit window of heights. -/
theorem sum_mult_window_le (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T t : ℝ,
      ∑ ρ ∈ (zetaZeros T).filter (fun ρ => t ≤ ρ.im ∧ ρ.im ≤ t + 1), (mult ρ : ℝ)
        ≤ C * Real.log (|t| + 2) := by
  refine ⟨224, by norm_num, fun T t => ?_⟩
  set F := (zetaZeros T).filter (fun ρ => t ≤ ρ.im ∧ ρ.im ≤ t + 1) with hF
  have hdisk : ∀ ρ ∈ F,
      ρ ∈ Metric.closedBall ((2 : ℂ) + ((t + 1 / 2 : ℝ) : ℂ) * I) (13 / 8 : ℝ) := by
    intro ρ hρ
    rw [hF, Finset.mem_filter] at hρ
    exact ZC.mem_disk_of_window hRH hρ.1 hρ.2.1 hρ.2.2
  have hη := Carmichael.sum_ord_etaFun_disk_le (t + 1 / 2) hdisk
  have hle : ∑ ρ ∈ F, (mult ρ : ℝ) ≤ ∑ ρ ∈ F, (analyticOrderNatAt Carmichael.etaFun ρ : ℝ) := by
    apply Finset.sum_le_sum
    intro ρ hρ
    rw [hF, Finset.mem_filter] at hρ
    obtain ⟨h1, h2, _, _⟩ := (mem_zetaZeros hRH).mp hρ.1
    have hne : ρ ≠ 1 := by
      intro h; rw [h] at h2; simp at h2
    exact_mod_cast Carmichael.analyticOrderNatAt_zeta_le_etaFun h1 hne
  have hlog := ZC.log_shift_le t
  have hlog0 : 0 ≤ Real.log (|t + 1 / 2| + 2) := Real.log_nonneg (by linarith [abs_nonneg (t + 1/2)])
  calc ∑ ρ ∈ F, (mult ρ : ℝ) ≤ 112 * Real.log (|t + 1 / 2| + 2) := le_trans hle hη
    _ ≤ 224 * Real.log (|t| + 2) := by linarith

/-- Total count `N(T) ≪ T log T`. -/
theorem sum_mult_le (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T →
      ∑ ρ ∈ zetaZeros T, (mult ρ : ℝ) ≤ C * T * Real.log T := by
  obtain ⟨C, hC0, hC⟩ := sum_mult_window_le hRH
  refine ⟨6 * C, by positivity, fun T hT => ?_⟩
  set K := ⌊2 * T⌋₊ + 1 with hK
  set g : ℂ → ℕ := fun ρ => ⌊ρ.im + T⌋₊ with hg
  have hmaps : ∀ ρ ∈ zetaZeros T, g ρ ∈ Finset.range K := by
    intro ρ hρ
    obtain ⟨_, _, h3, _⟩ := (mem_zetaZeros hRH).mp hρ
    rw [Finset.mem_range, hK, hg]
    have : ρ.im + T ≤ 2 * T := by linarith [(abs_le.mp h3).2]
    exact Nat.lt_succ_of_le (Nat.floor_le_floor this)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hwin : ∀ k ∈ Finset.range K,
      ∑ ρ ∈ (zetaZeros T).filter (fun ρ => g ρ = k), (mult ρ : ℝ)
        ≤ C * Real.log (T + 2) := by
    intro k hk
    have hkK : (k : ℝ) ≤ 2 * T := by
      rw [Finset.mem_range, hK, Nat.lt_succ_iff] at hk
      calc (k : ℝ) ≤ (⌊2 * T⌋₊ : ℝ) := by exact_mod_cast hk
        _ ≤ 2 * T := Nat.floor_le (by linarith)
    have hsub : (zetaZeros T).filter (fun ρ => g ρ = k) ⊆
        (zetaZeros T).filter (fun ρ => ((k : ℝ) - T) ≤ ρ.im ∧ ρ.im ≤ ((k : ℝ) - T) + 1) := by
      intro ρ hρ
      rw [Finset.mem_filter] at hρ ⊢
      refine ⟨hρ.1, ?_⟩
      obtain ⟨_, _, h3, _⟩ := (mem_zetaZeros hRH).mp hρ.1
      have hnn : 0 ≤ ρ.im + T := by linarith [(abs_le.mp h3).1]
      have hk' := hρ.2
      simp only [hg] at hk'
      have hfl := Nat.floor_le hnn
      have hlt := Nat.lt_floor_add_one (ρ.im + T)
      rw [hk'] at hfl hlt
      constructor <;> linarith
    have hmono : ∑ ρ ∈ (zetaZeros T).filter (fun ρ => g ρ = k), (mult ρ : ℝ)
        ≤ ∑ ρ ∈ (zetaZeros T).filter
            (fun ρ => ((k : ℝ) - T) ≤ ρ.im ∧ ρ.im ≤ ((k : ℝ) - T) + 1), (mult ρ : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
    have habs : |(k : ℝ) - T| ≤ T := by
      rw [abs_le]; constructor <;> linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    have hlog : Real.log (|(k : ℝ) - T| + 2) ≤ Real.log (T + 2) :=
      Real.log_le_log (by positivity) (by linarith)
    calc _ ≤ _ := hmono
      _ ≤ C * Real.log (|(k : ℝ) - T| + 2) := hC T _
      _ ≤ C * Real.log (T + 2) := mul_le_mul_of_nonneg_left hlog hC0
  have hsum := Finset.sum_le_sum hwin
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hKr : (K : ℝ) ≤ 3 * T := by
    rw [hK]; push_cast
    have := Nat.floor_le (show (0:ℝ) ≤ 2 * T by linarith)
    linarith
  have hlogT : Real.log (T + 2) ≤ 2 * Real.log T := by
    have : T + 2 ≤ T ^ 2 := by nlinarith
    calc Real.log (T + 2) ≤ Real.log (T ^ 2) := Real.log_le_log (by linarith) this
      _ = 2 * Real.log T := by rw [Real.log_pow]; norm_num
  have hlog0 : 0 ≤ Real.log (T + 2) := Real.log_nonneg (by linarith)
  calc _ ≤ (K : ℝ) * (C * Real.log (T + 2)) := hsum
    _ ≤ (3 * T) * (C * (2 * Real.log T)) := by
        apply mul_le_mul hKr (mul_le_mul_of_nonneg_left hlogT hC0) (by positivity)
          (by linarith)
    _ = 6 * C * T * Real.log T := by ring

end PPF.RH
