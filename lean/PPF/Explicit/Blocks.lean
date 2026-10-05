import PPF.Blocks

/-!
# Explicit bound: bad blocks from an explicit mean square

The shifting argument of `PPF.card_badBlocks_le`, with explicit hypotheses in place of
`SelbergMeanSquare` and the eventual threshold: the window mean square at
`(X, h) = (2^j, 2^b)` with constant `C`, and `8 log(3·2^j) ≤ ε 2^b`
(so the shift length `L = ⌊ε h/(4 log 3X)⌋ ≥ max 1 (ε h/(8 log 3X))`).
-/

namespace PPF.Explicit

open Finset

-- `hC` is part of the frozen interface; the proof does not need it.
set_option linter.unusedVariables false in
theorem card_badBlocks_explicit {C ε : ℝ} {j b X h : ℕ} (hX : X = 2 ^ j) (hh : h = 2 ^ b)
    (hC : 0 ≤ C) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hj : 2 ≤ j) (hb : 2 * b ≤ j)
    (hL : 8 * Real.log (3 * 2 ^ j) ≤ ε * 2 ^ b)
    (hMS : ∑ n ∈ Finset.Ico X (2 * X),
        (Chebyshev.theta ((n + h : ℕ) : ℝ) - Chebyshev.theta n - h) ^ 2
      ≤ C * h * X * Real.log X ^ 2) :
    (#(badBlocks ε j b) : ℝ) ≤ (64 * C * Real.log 2 ^ 3 / ε ^ 3) * (j : ℝ) ^ 3 * 2 ^ j / 4 ^ b := by
  subst hX hh
  have hbj' : b ≤ j := by omega
  set lg := Real.log 2 with hlg
  have hlg0 : 0 < lg := Real.log_pos (by norm_num)
  have hjR : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have hjpos : (0 : ℝ) < j := by linarith
  -- real quantities
  set hR : ℝ := (2 : ℝ) ^ b with hhR
  set XR : ℝ := (2 : ℝ) ^ j with hXR
  have hhR0 : 0 < hR := by positivity
  have hXR0 : 0 < XR := by positivity
  -- `log(3X) ≤ (j+2) lg ≤ 2 j lg`
  have hlog3 : Real.log (3 * XR) ≤ 2 * j * lg := by
    have h34 : 3 * XR ≤ (2 : ℝ) ^ (j + 2) := by
      rw [hXR, pow_add]; nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) j]
    calc Real.log (3 * XR) ≤ Real.log ((2 : ℝ) ^ (j + 2)) := Real.log_le_log (by positivity) h34
      _ = ((j : ℝ) + 2) * lg := by rw [Real.log_pow]; push_cast; ring
      _ ≤ 2 * j * lg := by nlinarith
  have hlog3pos : 1 ≤ Real.log (3 * XR) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have : (1 : ℝ) ≤ XR := one_le_pow₀ (by norm_num)
    have := Real.exp_one_lt_d9
    linarith
  -- the window length `L`
  set y : ℝ := ε * hR / (4 * Real.log (3 * XR)) with hy
  set L : ℕ := ⌊y⌋₊ with hLdef
  have hy0 : 0 ≤ y := by positivity
  have hLy : (L : ℝ) ≤ y := Nat.floor_le hy0
  -- `y ≥ 2`, from the hypothesis `8 log(3X) ≤ ε h`
  have hy2 : 2 ≤ y := by
    rw [hy, le_div_iff₀ (by positivity)]
    linarith
  have hLlow : y / 2 ≤ (L : ℝ) := by
    have := Nat.sub_one_lt_floor y
    linarith
  have hLlow' : ε * hR / (16 * j * lg) ≤ (L : ℝ) := by
    refine le_trans ?_ hLlow
    rw [hy, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 ≤ ε * hR := by positivity
    nlinarith
  have hLh : L ≤ 2 ^ b := by
    have : (L : ℝ) ≤ hR := by
      refine hLy.trans ?_
      rw [hy, div_le_iff₀ (by positivity)]
      nlinarith
    have h' : (L : ℝ) ≤ ((2 ^ b : ℕ) : ℝ) := by rw [Nat.cast_pow, Nat.cast_ofNat]; exact this
    exact_mod_cast h'
  have hLlog : (L : ℝ) * Real.log (3 * 2 ^ j) ≤ ε * 2 ^ b / 4 := by
    calc (L : ℝ) * Real.log (3 * XR) ≤ y * Real.log (3 * XR) :=
          mul_le_mul_of_nonneg_right hLy (by linarith)
      _ = ε * hR / 4 := by rw [hy]; field_simp
  set E : ℕ → ℝ := fun n =>
    (Chebyshev.theta ((n + 2 ^ b : ℕ) : ℝ) - Chebyshev.theta (n : ℕ) - ((2 ^ b : ℕ) : ℝ)) ^ 2
    with hE
  have hE0 : ∀ n, 0 ≤ E n := fun n => sq_nonneg _
  -- lower bound for the mean square by the bad blocks
  have hblocks : ∑ M ∈ Ico (2 ^ (j - b)) (2 ^ (j - b + 1)),
      ∑ n ∈ Ico (M * 2 ^ b) (M * 2 ^ b + 2 ^ b), E n
      = ∑ n ∈ Ico (2 ^ j) (2 * 2 ^ j), E n := by
    rw [BlocksAux.sum_Ico_blocks E (2 ^ b) _ _ (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _)),
      ← pow_add, ← pow_add, Nat.sub_add_cancel hbj', show j - b + 1 + b = j + 1 by omega,
      pow_succ, mul_comm]
  have hlower : (#(badBlocks ε j b) : ℝ) * ((L : ℝ) * (ε * hR / 2) ^ 2)
      ≤ ∑ n ∈ Ico (2 ^ j) (2 * 2 ^ j), E n := by
    rw [← hblocks]
    calc (#(badBlocks ε j b) : ℝ) * ((L : ℝ) * (ε * hR / 2) ^ 2)
        = ∑ _M ∈ badBlocks ε j b, (L : ℝ) * (ε * hR / 2) ^ 2 := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ M ∈ badBlocks ε j b, ∑ n ∈ Ico (M * 2 ^ b) (M * 2 ^ b + 2 ^ b), E n := by
          refine sum_le_sum fun M hM => ?_
          calc (L : ℝ) * (ε * hR / 2) ^ 2 = ∑ _n ∈ Ico (M * 2 ^ b) (M * 2 ^ b + L),
                (ε * hR / 2) ^ 2 := by
                rw [sum_const, nsmul_eq_mul, Nat.card_Ico, Nat.add_sub_cancel_left]
            _ ≤ ∑ n ∈ Ico (M * 2 ^ b) (M * 2 ^ b + L), E n := by
                refine sum_le_sum fun n hn => ?_
                rw [mem_Ico] at hn
                exact BlocksAux.window_error_large hM hbj' hLh hn.1 hn.2 hLlog hε0
            _ ≤ ∑ n ∈ Ico (M * 2 ^ b) (M * 2 ^ b + 2 ^ b), E n :=
                sum_le_sum_of_subset_of_nonneg
                  (Ico_subset_Ico le_rfl (by omega)) (fun n _ _ => hE0 n)
      _ ≤ ∑ M ∈ Ico (2 ^ (j - b)) (2 ^ (j - b + 1)),
            ∑ n ∈ Ico (M * 2 ^ b) (M * 2 ^ b + 2 ^ b), E n := by
          refine sum_le_sum_of_subset_of_nonneg ?_ (fun M _ _ => sum_nonneg fun n _ => hE0 n)
          intro M hM
          unfold badBlocks at hM
          exact (mem_filter.mp hM).1
  -- upper bound from the hypothesis
  have hupper : ∑ n ∈ Ico (2 ^ j) (2 * 2 ^ j), E n ≤ C * hR * XR * (j * lg) ^ 2 := by
    have hlogX : Real.log ((2 ^ j : ℕ) : ℝ) = j * lg := by push_cast; rw [Real.log_pow]
    simp only [hE]
    refine hMS.trans ?_
    rw [hlogX]
    push_cast
    rw [hhR, hXR]
  -- combine
  have hcomb := hlower.trans hupper
  set K : ℝ := (#(badBlocks ε j b) : ℝ)
  have hK0 : 0 ≤ K := by positivity
  have hfac : 0 < ε * hR / (16 * j * lg) * (ε * hR / 2) ^ 2 := by positivity
  have hK : K * (ε * hR / (16 * j * lg) * (ε * hR / 2) ^ 2) ≤ C * hR * XR * (j * lg) ^ 2 := by
    refine le_trans ?_ hcomb
    apply mul_le_mul_of_nonneg_left _ hK0
    exact mul_le_mul_of_nonneg_right hLlow' (sq_nonneg _)
  have h4b : (4 : ℝ) ^ b = hR ^ 2 := by rw [hhR, ← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h4b, le_div_iff₀ (by positivity)]
  rw [← le_div_iff₀ hfac] at hK
  calc K * hR ^ 2 ≤ C * hR * XR * (j * lg) ^ 2 /
        (ε * hR / (16 * j * lg) * (ε * hR / 2) ^ 2) * hR ^ 2 :=
        mul_le_mul_of_nonneg_right hK (sq_nonneg _)
    _ = 64 * C * lg ^ 3 / ε ^ 3 * (j : ℝ) ^ 3 * 2 ^ j := by
        rw [hXR]
        field_simp
        ring

end PPF.Explicit
