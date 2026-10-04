import PPF.RH.ZeroCount
import PPF.RH.KZ.Pairs

/-!
# K3: double sums over zeros with the kernel `1/(1 + (γ − γ′)²)`

Group zeros into unit windows `⌊γ⌋ = n` (`KZ.double_sum_le`): the double sum is at most
`24 ∑ₙ Wₙ²`, with `Wₙ` the window weight. For low zeros `Wₙ ≪ log U` (K2) and
`∑ₙ Wₙ = N(U) ≪ U log U`. For high zeros `Wₙ ≪ log(|n|+2)/max(U, |n|−1)`, and the sum
over windows is the tail bound `KZ.sum_tail_log_sq_le`.
-/

namespace PPF.RH

open Complex Finset

namespace KZ

lemma abs_win_le (ρ : ℂ) : |((win ρ : ℤ) : ℝ)| ≤ |ρ.im| + 1 := by
  have h1 := Int.floor_le ρ.im
  have h2 := Int.lt_floor_add_one ρ.im
  have h3 := le_abs_self ρ.im
  have h4 := neg_abs_le ρ.im
  simp only [win]
  rw [abs_le]
  constructor <;> linarith

lemma abs_im_le_win (ρ : ℂ) : |ρ.im| ≤ |((win ρ : ℤ) : ℝ)| + 1 := by
  have h1 := Int.floor_le ρ.im
  have h2 := Int.lt_floor_add_one ρ.im
  have h3 := le_abs_self ((⌊ρ.im⌋ : ℤ) : ℝ)
  have h4 := neg_abs_le ((⌊ρ.im⌋ : ℤ) : ℝ)
  simp only [win]
  rw [abs_le]
  constructor <;> linarith

lemma win_window {ρ : ℂ} {n : ℤ} (h : win ρ = n) : (n : ℝ) ≤ ρ.im ∧ ρ.im ≤ n + 1 := by
  have h1 := Int.floor_le ρ.im
  have h2 := Int.lt_floor_add_one ρ.im
  simp only [win] at h
  rw [h] at h1 h2
  exact ⟨h1, h2.le⟩

lemma log_add_le_three_log {U c : ℝ} (hU : 2 ≤ U) (hc0 : 0 ≤ c) (hc : c ≤ 4) :
    Real.log (U + c) ≤ 3 * Real.log U := by
  have hU0 : 0 < U := by linarith
  have h4 : 4 ≤ U ^ 2 := by nlinarith
  have h3 : U ^ 3 = U * U ^ 2 := by ring
  calc Real.log (U + c) ≤ Real.log (U ^ 3) :=
        Real.log_le_log (by linarith) (by nlinarith)
    _ = 3 * Real.log U := by rw [Real.log_pow]; push_cast; ring

lemma four_le_nine_log_sq {U : ℝ} (hU : 2 ≤ U) : 4 ≤ 9 * Real.log U ^ 2 := by
  have h2 : Real.log 2 ≤ Real.log U := Real.log_le_log (by norm_num) hU
  have h3 := Real.log_two_gt_d9
  nlinarith

/-- Window weight is bounded by the window zero count. -/
lemma winW_le_window {T : ℝ} {Z : Finset ℂ}
    (hZ : Z ⊆ zetaZeros T) (n : ℤ) :
    winW Z (fun ρ => (mult ρ : ℝ)) n
      ≤ ∑ ρ ∈ (zetaZeros T).filter (fun ρ => (n : ℝ) ≤ ρ.im ∧ ρ.im ≤ (n : ℝ) + 1), (mult ρ : ℝ) := by
  apply sum_le_sum_of_subset_of_nonneg
  · intro ρ hρ
    rw [mem_filter] at hρ ⊢
    exact ⟨hZ hρ.1, win_window hρ.2⟩
  · intro ρ _ _; positivity

end KZ

/-- K3, low zeros: `≪ U log² U`. -/
theorem sum_low_pairs_le (hRH : RiemannHypothesis) :
    ∃ C : ℝ, ∀ U : ℝ, 2 ≤ U →
      ∑ ρ ∈ zetaZeros U, ∑ ρ' ∈ zetaZeros U,
          ((mult ρ : ℝ) * mult ρ') / (1 + (ρ.im - ρ'.im) ^ 2)
        ≤ C * U * Real.log U ^ 2 := by
  obtain ⟨C₂, hC₂, hwin⟩ := sum_mult_window_le hRH
  obtain ⟨C₁, hC₁, htot⟩ := sum_mult_le hRH
  refine ⟨72 * C₁ * C₂, ?_⟩
  intro U hU
  set Z := zetaZeros U with hZ
  set w : ℂ → ℝ := fun ρ => (mult ρ : ℝ) with hw
  have hw0 : ∀ ρ ∈ Z, 0 ≤ w ρ := fun _ _ => Nat.cast_nonneg _
  have h1 := KZ.double_sum_le Z w hw0
  have hlogU : 0 < Real.log U := Real.log_pos (by linarith)
  set B := C₂ * (3 * Real.log U) with hB
  have hWn : ∀ n ∈ Z.image KZ.win, KZ.winW Z w n ≤ B := by
    intro n hn
    obtain ⟨ρ0, hρ0, rfl⟩ := mem_image.1 hn
    have hmem := (mem_zetaZeros hRH).1 hρ0
    have habs : |((KZ.win ρ0 : ℤ) : ℝ)| ≤ U + 1 :=
      (KZ.abs_win_le ρ0).trans (by linarith [hmem.2.2.1])
    calc KZ.winW Z w (KZ.win ρ0)
        ≤ ∑ ρ ∈ (zetaZeros U).filter
            (fun ρ => ((KZ.win ρ0 : ℤ) : ℝ) ≤ ρ.im ∧ ρ.im ≤ ((KZ.win ρ0 : ℤ) : ℝ) + 1),
            (mult ρ : ℝ) := KZ.winW_le_window (subset_refl _) _
      _ ≤ C₂ * Real.log (|((KZ.win ρ0 : ℤ) : ℝ)| + 2) := hwin U _
      _ ≤ B := by
          rw [hB]
          apply mul_le_mul_of_nonneg_left _ hC₂
          calc Real.log (|((KZ.win ρ0 : ℤ) : ℝ)| + 2) ≤ Real.log (U + 3) :=
                Real.log_le_log (by positivity) (by linarith)
            _ ≤ 3 * Real.log U := KZ.log_add_le_three_log hU (by norm_num) (by norm_num)
  have hW0 : ∀ n, 0 ≤ KZ.winW Z w n := fun n =>
    sum_nonneg (fun ρ hρ => hw0 ρ (mem_filter.1 hρ).1)
  have hmaps : ∀ ρ ∈ Z, KZ.win ρ ∈ Z.image KZ.win := fun ρ hρ => mem_image_of_mem _ hρ
  have hsumW : ∑ n ∈ Z.image KZ.win, KZ.winW Z w n = ∑ ρ ∈ Z, w ρ :=
    sum_fiberwise_of_maps_to hmaps w
  have htotU := htot U hU
  calc ∑ ρ ∈ Z, ∑ ρ' ∈ Z, ((mult ρ : ℝ) * mult ρ') / (1 + (ρ.im - ρ'.im) ^ 2)
      ≤ 24 * ∑ n ∈ Z.image KZ.win, KZ.winW Z w n ^ 2 := h1
    _ ≤ 24 * ∑ n ∈ Z.image KZ.win, KZ.winW Z w n * B := by
        gcongr with n hn
        rw [sq]
        exact mul_le_mul_of_nonneg_left (hWn n hn) (hW0 n)
    _ = 24 * B * ∑ ρ ∈ Z, w ρ := by rw [← sum_mul, hsumW]; ring
    _ ≤ 24 * B * (C₁ * U * Real.log U) := by
        gcongr
    _ = 72 * C₁ * C₂ * U * Real.log U ^ 2 := by rw [hB]; ring

/-- K3, high zeros: `≪ log² U / U`, uniformly in the truncation `T`. -/
theorem sum_high_pairs_le (hRH : RiemannHypothesis) :
    ∃ C : ℝ, ∀ U T : ℝ, 2 ≤ U →
      ∑ ρ ∈ (zetaZeros T).filter (fun ρ => U < |ρ.im|),
        ∑ ρ' ∈ (zetaZeros T).filter (fun ρ => U < |ρ.im|),
          ((mult ρ : ℝ) * mult ρ') / (‖ρ‖ * ‖ρ'‖ * (1 + (ρ.im - ρ'.im) ^ 2))
        ≤ C * Real.log U ^ 2 / U := by
  obtain ⟨C₂, hC₂, hwin⟩ := sum_mult_window_le hRH
  refine ⟨24 * (2 * (459 * C₂ ^ 2)), ?_⟩
  intro U T hU
  have hU0 : 0 < U := by linarith
  have hlogU : 0 < Real.log U := Real.log_pos (by linarith)
  set Z := (zetaZeros T).filter (fun ρ => U < |ρ.im|) with hZ
  have hZsub : Z ⊆ zetaZeros T := filter_subset _ _
  set w : ℂ → ℝ := fun ρ => (mult ρ : ℝ) / ‖ρ‖ with hw
  have hw0 : ∀ ρ ∈ Z, 0 ≤ w ρ := fun _ _ => by simp only [hw]; positivity
  have hrw : ∀ ρ ∈ Z, ∀ ρ' ∈ Z,
      ((mult ρ : ℝ) * mult ρ') / (‖ρ‖ * ‖ρ'‖ * (1 + (ρ.im - ρ'.im) ^ 2))
        = w ρ * w ρ' / (1 + (ρ.im - ρ'.im) ^ 2) := by
    intro ρ _ ρ' _
    simp only [hw]
    rw [div_mul_div_comm, div_div]
  rw [sum_congr rfl (fun ρ hρ => sum_congr rfl (fun ρ' hρ' => hrw ρ hρ ρ' hρ'))]
  have h1 := KZ.double_sum_le Z w hw0
  set N := Z.image KZ.win with hN
  -- lower bound for the norm on a window
  set L : ℤ → ℝ := fun n => max U (|(n : ℝ)| - 1) with hL
  have hLpos : ∀ n, 0 < L n := fun n => lt_of_lt_of_le hU0 (le_max_left _ _)
  have hnorm : ∀ ρ ∈ Z, L (KZ.win ρ) ≤ ‖ρ‖ := by
    intro ρ hρ
    have hU' := (mem_filter.1 hρ).2
    have h2 := KZ.abs_win_le ρ
    have h3 := Complex.abs_im_le_norm ρ
    simp only [hL]
    apply max_le <;> linarith
  -- window bound
  have hWn : ∀ n, KZ.winW Z w n ≤ C₂ * Real.log (|(n : ℝ)| + 2) / L n := by
    intro n
    calc KZ.winW Z w n
        = ∑ ρ ∈ Z.filter (fun ρ => KZ.win ρ = n), (mult ρ : ℝ) / ‖ρ‖ := rfl
      _ ≤ ∑ ρ ∈ Z.filter (fun ρ => KZ.win ρ = n), (mult ρ : ℝ) / L n := by
          apply sum_le_sum
          intro ρ hρ
          obtain ⟨hρZ, hρn⟩ := mem_filter.1 hρ
          have := hnorm ρ hρZ
          rw [hρn] at this
          exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (hLpos n) this
      _ = KZ.winW Z (fun ρ => (mult ρ : ℝ)) n / L n := by
          rw [KZ.winW, sum_div]
      _ ≤ (∑ ρ ∈ (zetaZeros T).filter (fun ρ => (n : ℝ) ≤ ρ.im ∧ ρ.im ≤ (n : ℝ) + 1),
              (mult ρ : ℝ)) / L n := by
          exact (div_le_div_iff_of_pos_right (hLpos n)).mpr (KZ.winW_le_window hZsub n)
      _ ≤ C₂ * Real.log (|(n : ℝ)| + 2) / L n :=
          (div_le_div_iff_of_pos_right (hLpos n)).mpr (hwin T n)
  have hW0 : ∀ n, 0 ≤ KZ.winW Z w n := fun n =>
    sum_nonneg (fun ρ hρ => hw0 ρ (mem_filter.1 hρ).1)
  -- the function on ℕ
  set F : ℕ → ℝ := fun k => Real.log ((k : ℝ) + 2) ^ 2 / max U ((k : ℝ) - 1) ^ 2 with hF
  have hF0 : ∀ k, 0 ≤ F k := fun k => by simp only [hF]; positivity
  have hWsq : ∀ n, KZ.winW Z w n ^ 2 ≤ C₂ ^ 2 * F (0 - n).natAbs := by
    intro n
    have habs : ((0 - n).natAbs : ℝ) = |(n : ℝ)| := by
      rw [Nat.cast_natAbs, Int.cast_abs]; push_cast; rw [zero_sub, abs_neg]
    have hb := hWn n
    have hlog0 : 0 ≤ Real.log (|(n : ℝ)| + 2) := Real.log_nonneg (by linarith [abs_nonneg (n : ℝ)])
    calc KZ.winW Z w n ^ 2 ≤ (C₂ * Real.log (|(n : ℝ)| + 2) / L n) ^ 2 :=
          pow_le_pow_left₀ (hW0 n) hb 2
      _ = C₂ ^ 2 * F (0 - n).natAbs := by
          simp only [hF, hL, habs]
          rw [div_pow, mul_pow, mul_div_assoc]
  have hsumF : ∑ n ∈ N, KZ.winW Z w n ^ 2 ≤ C₂ ^ 2 * (2 * ∑ k ∈ N.image (fun d => (0 - d).natAbs), F k) := by
    calc ∑ n ∈ N, KZ.winW Z w n ^ 2 ≤ ∑ n ∈ N, C₂ ^ 2 * F (0 - n).natAbs := sum_le_sum (fun n _ => hWsq n)
      _ = C₂ ^ 2 * ∑ n ∈ N, F (0 - n).natAbs := by rw [mul_sum]
      _ ≤ C₂ ^ 2 * (2 * ∑ k ∈ N.image (fun d => (0 - d).natAbs), F k) := by
          gcongr
          exact KZ.sum_natAbs_le N 0 F hF0
  -- bound the sum of F over S
  set S := N.image (fun d => (0 - d).natAbs) with hS
  have hSlow : ∀ k ∈ S, U - 1 < (k : ℝ) := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := mem_image.1 hk
    obtain ⟨ρ, hρ, rfl⟩ := mem_image.1 hn
    have hU' := (mem_filter.1 hρ).2
    have h2 := KZ.abs_im_le_win ρ
    have habs : (((0 - KZ.win ρ).natAbs : ℕ) : ℝ) = |((KZ.win ρ : ℤ) : ℝ)| := by
      rw [Nat.cast_natAbs, Int.cast_abs]; push_cast; rw [zero_sub, abs_neg]
    rw [habs]
    linarith
  set K₀ : ℕ := ⌈U⌉₊ + 1 with hK₀
  have hceil1 : U ≤ (⌈U⌉₊ : ℝ) := Nat.le_ceil U
  have hceil2 : (⌈U⌉₊ : ℝ) < U + 1 := Nat.ceil_lt_add_one hU0.le
  have hK₀3 : 3 ≤ K₀ := by
    have : (2 : ℝ) ≤ (⌈U⌉₊ : ℝ) := hU.trans hceil1
    have : 2 ≤ ⌈U⌉₊ := by exact_mod_cast this
    omega
  have hpartA : ∑ k ∈ S.filter (fun k => k ≤ K₀), F k ≤ 27 * Real.log U ^ 2 / U := by
    have hsub : S.filter (fun k => k ≤ K₀) ⊆ Icc (K₀ - 2) K₀ := by
      intro k hk
      obtain ⟨hkS, hkK⟩ := mem_filter.1 hk
      have hlow := hSlow k hkS
      rw [mem_Icc]
      refine ⟨?_, hkK⟩
      have : (⌈U⌉₊ : ℝ) < (k : ℝ) + 2 := by linarith
      have : ⌈U⌉₊ < k + 2 := by exact_mod_cast this
      omega
    have hcard : #(Icc (K₀ - 2) K₀) ≤ 3 := by
      rw [Nat.card_Icc]; omega
    calc ∑ k ∈ S.filter (fun k => k ≤ K₀), F k
        ≤ ∑ k ∈ Icc (K₀ - 2) K₀, F k :=
          sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => hF0 k)
      _ ≤ ∑ k ∈ Icc (K₀ - 2) K₀, 9 * Real.log U ^ 2 / U ^ 2 := by
          apply sum_le_sum
          intro k hk
          -- every k in the interval obeys the same bound
          have hkK : k ≤ K₀ := (mem_Icc.1 hk).2
          have hkr : (k : ℝ) ≤ K₀ := by exact_mod_cast hkK
          have hK₀r : (K₀ : ℝ) ≤ U + 2 := by simp only [hK₀]; push_cast; linarith
          have hlog : Real.log ((k : ℝ) + 2) ≤ 3 * Real.log U := by
            calc Real.log ((k : ℝ) + 2) ≤ Real.log (U + 4) :=
                  Real.log_le_log (by positivity) (by linarith)
              _ ≤ 3 * Real.log U := KZ.log_add_le_three_log hU (by norm_num) (by norm_num)
          have hlog0 : 0 ≤ Real.log ((k : ℝ) + 2) :=
            Real.log_nonneg (by linarith [k.cast_nonneg (α := ℝ)])
          simp only [hF]
          have hmax : U ^ 2 ≤ max U ((k : ℝ) - 1) ^ 2 :=
            pow_le_pow_left₀ hU0.le (le_max_left _ _) 2
          calc Real.log ((k : ℝ) + 2) ^ 2 / max U ((k : ℝ) - 1) ^ 2
              ≤ Real.log ((k : ℝ) + 2) ^ 2 / U ^ 2 :=
                div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hmax
            _ ≤ (3 * Real.log U) ^ 2 / U ^ 2 := by gcongr
            _ = 9 * Real.log U ^ 2 / U ^ 2 := by ring
      _ = #(Icc (K₀ - 2) K₀) * (9 * Real.log U ^ 2 / U ^ 2) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ 3 * (9 * Real.log U ^ 2 / U ^ 2) := by
          gcongr
          exact_mod_cast hcard
      _ = 27 * Real.log U ^ 2 / U ^ 2 := by ring
      _ ≤ 27 * Real.log U ^ 2 / U :=
          div_le_div_of_nonneg_left (by positivity) hU0 (by nlinarith)
  have hpartB : ∑ k ∈ S.filter (fun k => ¬ k ≤ K₀), F k ≤ 432 * Real.log U ^ 2 / U := by
    have hsub : S.filter (fun k => ¬ k ≤ K₀) ⊆ Ico (K₀ + 1) (S.sup id + 1) := by
      intro k hk
      obtain ⟨hkS, hkK⟩ := mem_filter.1 hk
      rw [mem_Ico]
      refine ⟨by omega, ?_⟩
      have := le_sup (f := id) hkS
      simp only [id] at this
      omega
    have hterm : ∀ k ∈ Ico (K₀ + 1) (S.sup id + 1),
        F k ≤ Real.log ((k : ℝ) + 2) ^ 2 / ((k : ℝ) - 1) ^ 2 := by
      intro k hk
      have hk1 : K₀ + 1 ≤ k := (mem_Ico.1 hk).1
      have hkr : (K₀ : ℝ) + 1 ≤ k := by exact_mod_cast hk1
      have hK₀r : U + 1 ≤ (K₀ : ℝ) := by simp only [hK₀]; push_cast; linarith
      have hkpos : 0 < (k : ℝ) - 1 := by linarith
      simp only [hF]
      apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      exact pow_le_pow_left₀ hkpos.le (le_max_right _ _) 2
    have htail := KZ.sum_tail_log_sq_le (K₀ + 1) (by omega) (S.sup id + 1)
    have hK₁lo : U ≤ ((K₀ + 1 : ℕ) : ℝ) := by
      simp only [hK₀]; push_cast; linarith
    have hK₁hi : ((K₀ + 1 : ℕ) : ℝ) ≤ U + 3 := by
      simp only [hK₀]; push_cast; linarith
    have hlogK : Real.log ((K₀ + 1 : ℕ) : ℝ) ≤ 3 * Real.log U := by
      calc Real.log ((K₀ + 1 : ℕ) : ℝ) ≤ Real.log (U + 3) :=
            Real.log_le_log (by linarith) hK₁hi
        _ ≤ 3 * Real.log U := KZ.log_add_le_three_log hU (by norm_num) (by norm_num)
    have hlogK0 : 0 ≤ Real.log ((K₀ + 1 : ℕ) : ℝ) := Real.log_nonneg (by linarith)
    have h4 := KZ.four_le_nine_log_sq hU
    have hfrac : (Real.log ((K₀ + 1 : ℕ) : ℝ) ^ 2 + 4) / ((K₀ + 1 : ℕ) : ℝ)
        ≤ 18 * Real.log U ^ 2 / U := by
      rw [div_le_div_iff₀ (by linarith) hU0]
      have hsq : Real.log ((K₀ + 1 : ℕ) : ℝ) ^ 2 ≤ 9 * Real.log U ^ 2 := by nlinarith
      have : 0 ≤ Real.log U ^ 2 := sq_nonneg _
      nlinarith
    calc ∑ k ∈ S.filter (fun k => ¬ k ≤ K₀), F k
        ≤ ∑ k ∈ Ico (K₀ + 1) (S.sup id + 1), F k :=
          sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => hF0 k)
      _ ≤ ∑ k ∈ Ico (K₀ + 1) (S.sup id + 1), Real.log ((k : ℝ) + 2) ^ 2 / ((k : ℝ) - 1) ^ 2 :=
          sum_le_sum hterm
      _ ≤ 24 * ((Real.log ((K₀ + 1 : ℕ) : ℝ) ^ 2 + 4) / ((K₀ + 1 : ℕ) : ℝ)) := htail
      _ ≤ 24 * (18 * Real.log U ^ 2 / U) := by gcongr
      _ = 432 * Real.log U ^ 2 / U := by ring
  have hSsum : ∑ k ∈ S, F k ≤ 459 * Real.log U ^ 2 / U := by
    rw [← sum_filter_add_sum_filter_not S (fun k => k ≤ K₀)]
    have : 27 * Real.log U ^ 2 / U + 432 * Real.log U ^ 2 / U = 459 * Real.log U ^ 2 / U := by
      ring
    linarith
  calc ∑ ρ ∈ Z, ∑ ρ' ∈ Z, w ρ * w ρ' / (1 + (ρ.im - ρ'.im) ^ 2)
      ≤ 24 * ∑ n ∈ N, KZ.winW Z w n ^ 2 := h1
    _ ≤ 24 * (C₂ ^ 2 * (2 * ∑ k ∈ S, F k)) := by gcongr
    _ ≤ 24 * (C₂ ^ 2 * (2 * (459 * Real.log U ^ 2 / U))) := by gcongr
    _ = 24 * (2 * (459 * C₂ ^ 2)) * Real.log U ^ 2 / U := by ring

end PPF.RH
