import PPF.Explicit.Final.Numerics

/-!
# Explicit bound: the series `Σ eE`, `Σ (j+1)^{5/4} gE`, `Σ j^{-5/4}`
-/

namespace PPF.Explicit.Fn

open PPF.Explicit Real Finset

lemma J_real : ((J : ℕ) : ℝ) = 2 ^ 44 := by unfold J; push_cast; ring

lemma J_ge_two : (2 : ℝ) ≤ (J : ℝ) := by rw [J_real]; norm_num

lemma eE_nonneg (j : ℕ) : 0 ≤ eE j := by
  unfold eE
  have := cE_pos
  have := C5_nonneg
  positivity

/-- Telescoping: `Σ_{i<n} 1/(i+J)² ≤ 1/(J−1) − 1/(n+J−1)`. -/
lemma sum_inv_sq_le (n : ℕ) :
    ∑ i ∈ range n, 1 / (((i + J : ℕ) : ℝ)) ^ 2
      ≤ 1 / ((J : ℝ) - 1) - 1 / (((n + J : ℕ) : ℝ) - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have hx : (2 : ℝ) ≤ ((n + J : ℕ) : ℝ) := by
      have := J_ge_two; push_cast; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    have key : 1 / (((n + J : ℕ) : ℝ)) ^ 2
        ≤ 1 / (((n + J : ℕ) : ℝ) - 1) - 1 / ((((n + 1) + J : ℕ) : ℝ) - 1) := by
      have e : (((n + 1) + J : ℕ) : ℝ) - 1 = ((n + J : ℕ) : ℝ) := by push_cast; ring
      rw [e]
      set x : ℝ := ((n + J : ℕ) : ℝ)
      have h1 : 0 < x - 1 := by linarith
      have h2 : 0 < x := by linarith
      rw [div_sub_div _ _ h1.ne' h2.ne', one_mul, mul_one]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

lemma sum_inv_sq_le' (n : ℕ) :
    ∑ i ∈ range n, 1 / (((i + J : ℕ) : ℝ)) ^ 2 ≤ 1 / ((J : ℝ) - 1) := by
  refine (sum_inv_sq_le n).trans ?_
  have hx : (2 : ℝ) ≤ ((n + J : ℕ) : ℝ) := by
    have := J_ge_two; push_cast; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have : 0 ≤ 1 / (((n + J : ℕ) : ℝ) - 1) := by
    apply div_nonneg zero_le_one; linarith
  linarith

lemma sum_eE_le (n : ℕ) : ∑ i ∈ range n, eE (i + J) ≤ 1 / 1000 := by
  have hnum : 2 * cE + 5 * C5 ≤ 13750004 := by
    have := cE_le_two; have := C5_le; linarith
  have hnum0 : 0 ≤ 2 * cE + 5 * C5 := by
    have := cE_pos; have := C5_nonneg; linarith
  have hrw : ∑ i ∈ range n, eE (i + J)
      = (2 * cE + 5 * C5) * ∑ i ∈ range n, 1 / (((i + J : ℕ) : ℝ)) ^ 2 := by
    rw [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    unfold eE; push_cast; ring
  rw [hrw]
  have hJ : (J : ℝ) - 1 = 2 ^ 44 - 1 := by rw [J_real]
  calc (2 * cE + 5 * C5) * ∑ i ∈ range n, 1 / (((i + J : ℕ) : ℝ)) ^ 2
      ≤ 13750004 * (1 / ((J : ℝ) - 1)) := by
        apply mul_le_mul hnum (sum_inv_sq_le' n)
          (sum_nonneg fun i _ => by positivity) (by norm_num)
    _ ≤ 1 / 1000 := by rw [hJ]; norm_num

end PPF.Explicit.Fn
