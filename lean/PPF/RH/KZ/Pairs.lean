import Mathlib

/-!
# Helpers for K3: double sums with the kernel `1/(1 + (γ − γ′)²)`

Points are grouped into unit windows `win ρ = ⌊Im ρ⌋`. Across windows the kernel is
at most `4/(1 + (n − n′)²)`, whose row sums are at most `24`; by AM–GM the double sum is
at most `24 ∑ₙ Wₙ²`, where `Wₙ` is the window weight (`double_sum_le`).
`sum_tail_log_sq_le` is the tail bound `∑_{k ≥ K} log²(k+2)/(k−1)² ≤ 24(log² K + 4)/K`.
-/

namespace PPF.RH.KZ

open Finset

lemma sum_range_inv_one_add_sq_le (M : ℕ) : ∑ k ∈ range M, 1 / (1 + (k : ℝ) ^ 2) ≤ 3 := by
  have h : ∀ M : ℕ, ∑ k ∈ range (M + 1), 1 / (1 + (k : ℝ) ^ 2) ≤ 3 - 2 / ((M : ℝ) + 1) := by
    intro M
    induction M with
    | zero => norm_num
    | succ M ih =>
      rw [sum_range_succ]
      have hM : (0 : ℝ) ≤ M := M.cast_nonneg
      have key : 1 / (1 + ((M : ℝ) + 1) ^ 2) ≤ 2 / ((M : ℝ) + 1) - 2 / ((M : ℝ) + 1 + 1) := by
        rw [div_sub_div _ _ (by positivity) (by positivity),
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      push_cast
      linarith
  cases M with
  | zero => simp
  | succ M =>
    have h1 := h M
    have h2 : (0 : ℝ) ≤ 2 / ((M : ℝ) + 1) := by positivity
    linarith

lemma card_filter_natAbs_le (D : Finset ℤ) (n : ℤ) (k : ℕ) :
    #(D.filter (fun d => (n - d).natAbs = k)) ≤ 2 := by
  have hsub : D.filter (fun d => (n - d).natAbs = k) ⊆ {n - k, n + k} := by
    intro d hd
    rw [mem_filter] at hd
    rw [mem_insert, mem_singleton]
    have := Int.natAbs_eq (n - d)
    rw [hd.2] at this
    omega
  calc #(D.filter (fun d => (n - d).natAbs = k)) ≤ #({n - k, n + k} : Finset ℤ) :=
        card_le_card hsub
    _ ≤ 2 := by
        refine (card_insert_le _ _).trans ?_
        simp

lemma sum_natAbs_le (D : Finset ℤ) (n : ℤ) (F : ℕ → ℝ) (hF : ∀ k, 0 ≤ F k) :
    ∑ d ∈ D, F (n - d).natAbs ≤ 2 * ∑ k ∈ D.image (fun d => (n - d).natAbs), F k := by
  rw [Finset.sum_comp, Finset.mul_sum]
  apply sum_le_sum
  intro k _
  rw [nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_filter_natAbs_le D n k) (hF k)

lemma sum_kernel_le (D : Finset ℤ) (n : ℤ) :
    ∑ d ∈ D, 1 / (1 + (((n - d : ℤ)) : ℝ) ^ 2) ≤ 6 := by
  set F : ℕ → ℝ := fun k => 1 / (1 + (k : ℝ) ^ 2) with hFdef
  have hF0 : ∀ k, 0 ≤ F k := fun k => by simp only [hFdef]; positivity
  have hF : ∀ d ∈ D, 1 / (1 + (((n - d : ℤ)) : ℝ) ^ 2) = F (n - d).natAbs := by
    intro d _
    simp only [hFdef, Nat.cast_natAbs, Int.cast_abs, sq_abs]
  rw [sum_congr rfl hF]
  set I := D.image (fun d => (n - d).natAbs) with hI
  have h1 := sum_natAbs_le D n F hF0
  have h2 : ∑ k ∈ I, F k ≤ ∑ k ∈ range (I.sup id + 1), F k := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro k hk
      rw [mem_range, Nat.lt_succ_iff]
      exact le_sup (f := id) hk
    · intro k _ _; exact hF0 k
  have h3 : ∑ k ∈ range (I.sup id + 1), F k ≤ 3 := sum_range_inv_one_add_sq_le _
  linarith

/-- Unit window index of a point. -/
noncomputable def win (ρ : ℂ) : ℤ := ⌊ρ.im⌋

lemma kernel_window_le (ρ ρ' : ℂ) :
    1 / (1 + (ρ.im - ρ'.im) ^ 2) ≤ 4 * (1 / (1 + (((win ρ - win ρ' : ℤ)) : ℝ) ^ 2)) := by
  have h1 := Int.floor_le ρ.im
  have h2 := Int.lt_floor_add_one ρ.im
  have h3 := Int.floor_le ρ'.im
  have h4 := Int.lt_floor_add_one ρ'.im
  have hd : (((win ρ - win ρ' : ℤ)) : ℝ) = (⌊ρ.im⌋ : ℝ) - ⌊ρ'.im⌋ := by
    simp [win]
  rw [hd]
  set x := ρ.im - ρ'.im with hx
  set d := (⌊ρ.im⌋ : ℝ) - ⌊ρ'.im⌋ with hdd
  have hlo : -1 < x - d := by rw [hx, hdd]; linarith
  have hhi : x - d < 1 := by rw [hx, hdd]; linarith
  have hsq : (x - d) ^ 2 < 1 := by nlinarith
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg (2 * x - d)]

/-- Window weight. -/
noncomputable def winW (Z : Finset ℂ) (w : ℂ → ℝ) (n : ℤ) : ℝ :=
  ∑ ρ ∈ Z.filter (fun ρ => win ρ = n), w ρ

theorem double_sum_le (Z : Finset ℂ) (w : ℂ → ℝ) (hw : ∀ ρ ∈ Z, 0 ≤ w ρ) :
    ∑ ρ ∈ Z, ∑ ρ' ∈ Z, w ρ * w ρ' / (1 + (ρ.im - ρ'.im) ^ 2)
      ≤ 24 * ∑ n ∈ Z.image win, winW Z w n ^ 2 := by
  set N := Z.image win with hN
  set W := winW Z w with hW
  set κ : ℤ → ℤ → ℝ := fun n n' => 4 * (1 / (1 + (((n - n' : ℤ)) : ℝ) ^ 2)) with hκ
  have hκ0 : ∀ n n', 0 ≤ κ n n' := by intro n n'; simp only [hκ]; positivity
  have hκsymm : ∀ n n', κ n n' = κ n' n := by
    intro n n'; simp only [hκ]; push_cast; ring
  have hκsum : ∀ n, ∑ n' ∈ N, κ n n' ≤ 24 := by
    intro n
    simp only [hκ]
    rw [← mul_sum]
    linarith [sum_kernel_le N n]
  have hmaps : ∀ ρ ∈ Z, win ρ ∈ N := fun ρ hρ => mem_image_of_mem win hρ
  have step1 : ∑ ρ ∈ Z, ∑ ρ' ∈ Z, w ρ * w ρ' / (1 + (ρ.im - ρ'.im) ^ 2)
      ≤ ∑ ρ ∈ Z, ∑ ρ' ∈ Z, w ρ * w ρ' * κ (win ρ) (win ρ') := by
    apply sum_le_sum; intro ρ hρ; apply sum_le_sum; intro ρ' hρ'
    have := kernel_window_le ρ ρ'
    calc w ρ * w ρ' / (1 + (ρ.im - ρ'.im) ^ 2)
        = (w ρ * w ρ') * (1 / (1 + (ρ.im - ρ'.im) ^ 2)) := by ring
      _ ≤ (w ρ * w ρ') * κ (win ρ) (win ρ') :=
          mul_le_mul_of_nonneg_left this (mul_nonneg (hw ρ hρ) (hw ρ' hρ'))
  have step2 : ∑ ρ ∈ Z, ∑ ρ' ∈ Z, w ρ * w ρ' * κ (win ρ) (win ρ')
      = ∑ n ∈ N, ∑ n' ∈ N, W n * W n' * κ n n' := by
    rw [← sum_fiberwise_of_maps_to hmaps]
    apply sum_congr rfl
    intro n _
    have inner : ∀ ρ ∈ Z.filter (fun ρ => win ρ = n),
        ∑ ρ' ∈ Z, w ρ * w ρ' * κ (win ρ) (win ρ')
          = ∑ n' ∈ N, ∑ ρ' ∈ Z.filter (fun ρ' => win ρ' = n'), w ρ * w ρ' * κ n n' := by
      intro ρ hρ
      rw [(mem_filter.1 hρ).2, ← sum_fiberwise_of_maps_to hmaps]
      apply sum_congr rfl
      intro n' _
      apply sum_congr rfl
      intro ρ' hρ'
      rw [(mem_filter.1 hρ').2]
    rw [sum_congr rfl inner, sum_comm]
    apply sum_congr rfl
    intro n' _
    simp only [hW, winW, sum_mul, mul_sum]
    rw [sum_comm]
  have hW0 : ∀ n, 0 ≤ W n := fun n =>
    sum_nonneg (fun ρ hρ => hw ρ (mem_filter.1 hρ).1)
  have step3 : ∑ n ∈ N, ∑ n' ∈ N, W n * W n' * κ n n'
      ≤ ∑ n ∈ N, ∑ n' ∈ N, (W n ^ 2 / 2 * κ n n' + W n' ^ 2 / 2 * κ n' n) := by
    apply sum_le_sum; intro n _; apply sum_le_sum; intro n' _
    rw [← hκsymm n n']
    have := hκ0 n n'
    nlinarith [sq_nonneg (W n - W n')]
  have step4 : ∑ n ∈ N, ∑ n' ∈ N, (W n ^ 2 / 2 * κ n n' + W n' ^ 2 / 2 * κ n' n)
      = ∑ n ∈ N, W n ^ 2 * ∑ n' ∈ N, κ n n' := by
    simp only [sum_add_distrib]
    rw [sum_comm (f := fun n n' => W n' ^ 2 / 2 * κ n' n)]
    rw [← sum_add_distrib]
    apply sum_congr rfl; intro n _
    rw [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl; intro n' _
    ring
  have step5 : ∑ n ∈ N, W n ^ 2 * ∑ n' ∈ N, κ n n' ≤ ∑ n ∈ N, W n ^ 2 * 24 := by
    apply sum_le_sum; intro n _
    exact mul_le_mul_of_nonneg_left (hκsum n) (sq_nonneg _)
  rw [← sum_mul] at step5
  linarith [step1, step2, step3, step4, step5]

/-- Per-term telescoping inequality. -/
lemma log_sq_tail_term {k : ℝ} (hk : 3 ≤ k) :
    Real.log (k + 2) ^ 2 / (k - 1) ^ 2
      ≤ 24 * ((Real.log k ^ 2 + 4) / k - (Real.log (k + 1) ^ 2 + 4) / (k + 1)) := by
  have hk0 : 0 < k := by linarith
  set L := Real.log k with hL
  set L' := Real.log (k + 1) with hL'
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  have hLL' : L ≤ L' := Real.log_le_log hk0 (by linarith)
  have hdiff : L' - L ≤ 1 / k := by
    rw [hL', hL, ← Real.log_div (by linarith) hk0.ne']
    have := Real.log_le_sub_one_of_pos (show 0 < (k + 1) / k by positivity)
    have h2 : (k + 1) / k - 1 = 1 / k := by field_simp; ring
    linarith
  have hkd : k * (L' - L) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hdiff hk0.le
    rwa [mul_one_div_cancel hk0.ne'] at this
  have hL'le : L' ≤ L + 1 := by
    have : 1 / k ≤ 1 := by rw [div_le_one hk0]; linarith
    linarith
  have hk2 : k * (L' ^ 2 - L ^ 2) ≤ 2 * L + 1 := by
    have h0 : 0 ≤ k * (L' - L) := mul_nonneg hk0.le (by linarith)
    have : k * (L' ^ 2 - L ^ 2) = (k * (L' - L)) * (L' + L) := by ring
    rw [this]
    nlinarith
  have hlog2 : Real.log (k + 2) ≤ 2 * L := by
    calc Real.log (k + 2) ≤ Real.log (k ^ 2) := Real.log_le_log (by linarith) (by nlinarith)
      _ = 2 * L := by rw [Real.log_pow]; push_cast; ring
  have hlog2' : 0 ≤ Real.log (k + 2) := Real.log_nonneg (by linarith)
  have hA : Real.log (k + 2) ^ 2 ≤ 4 * L ^ 2 := by nlinarith
  have hkm : 0 < k - 1 := by linarith
  have hB : k * (k + 1) ≤ 3 * (k - 1) ^ 2 := by nlinarith
  have key : (L ^ 2 + 4) / k - (L' ^ 2 + 4) / (k + 1)
      = (L ^ 2 + 4 - k * (L' ^ 2 - L ^ 2)) / (k * (k + 1)) := by
    field_simp
    ring
  have hnum : L ^ 2 / 2 ≤ L ^ 2 + 4 - k * (L' ^ 2 - L ^ 2) := by
    nlinarith [sq_nonneg (L - 2)]
  rw [key]
  have hpos : 0 < k * (k + 1) := by positivity
  have hkm2 : 0 < (k - 1) ^ 2 := by positivity
  calc Real.log (k + 2) ^ 2 / (k - 1) ^ 2 ≤ 12 * L ^ 2 / (k * (k + 1)) := by
        rw [div_le_div_iff₀ hkm2 hpos]
        calc Real.log (k + 2) ^ 2 * (k * (k + 1)) ≤ (4 * L ^ 2) * (3 * (k - 1) ^ 2) :=
              mul_le_mul hA hB hpos.le (by positivity)
          _ = 12 * L ^ 2 * (k - 1) ^ 2 := by ring
    _ ≤ 24 * ((L ^ 2 + 4 - k * (L' ^ 2 - L ^ 2)) / (k * (k + 1))) := by
        rw [mul_div_assoc']
        apply (div_le_div_iff_of_pos_right hpos).mpr
        linarith

lemma sum_tail_log_sq_le (K : ℕ) (hK : 3 ≤ K) (M : ℕ) :
    ∑ k ∈ Ico K M, Real.log ((k : ℝ) + 2) ^ 2 / ((k : ℝ) - 1) ^ 2
      ≤ 24 * ((Real.log (K : ℝ) ^ 2 + 4) / K) := by
  set g : ℕ → ℝ := fun k => (Real.log (k : ℝ) ^ 2 + 4) / k with hg
  have hg0 : ∀ k, 0 ≤ g k := fun k => by simp only [hg]; positivity
  have hstep : ∀ M, K ≤ M →
      ∑ k ∈ Ico K M, Real.log ((k : ℝ) + 2) ^ 2 / ((k : ℝ) - 1) ^ 2 ≤ 24 * (g K - g M) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => simp
    | succ M hKM ih =>
      rw [sum_Ico_succ_top hKM]
      have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hK.trans hKM
      have := log_sq_tail_term hM3
      have e : g (M + 1) = (Real.log ((M : ℝ) + 1) ^ 2 + 4) / ((M : ℝ) + 1) := by
        simp only [hg]; push_cast; ring
      rw [e]
      simp only [hg] at ih ⊢
      linarith
  rcases le_or_gt K M with h | h
  · have := hstep M h
    linarith [hg0 M]
  · rw [Ico_eq_empty (by omega), sum_empty]
    exact mul_nonneg (by norm_num) (hg0 K)

end PPF.RH.KZ
