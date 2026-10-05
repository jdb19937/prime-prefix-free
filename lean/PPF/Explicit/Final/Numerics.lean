import PPF.Bootstrap
import PPF.Explicit.Defs

/-!
# Explicit bound: numerical facts about the frozen constants
-/

namespace PPF.Explicit.Fn

open PPF.Explicit Real

lemma log_two_gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
lemma log_two_lt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
lemma log_two_pos' : 0 < Real.log 2 := Real.log_pos one_lt_two
lemma log_two_ge_half : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [log_two_gt]
lemma log_two_le_one : Real.log 2 ≤ 1 := by linarith [log_two_lt]

lemma cE_pos : 0 < cE := by unfold cE; exact div_pos one_pos log_two_pos'

lemma cE_le_two : cE ≤ 2 := by
  unfold cE
  rw [div_le_iff₀ log_two_pos']
  linarith [log_two_ge_half]

lemma cE_ge : (1.4426 : ℝ) ≤ cE := by
  unfold cE
  rw [le_div_iff₀ log_two_pos']
  nlinarith [log_two_lt]

lemma cE_le : cE ≤ 1.4427 := by
  unfold cE
  rw [div_le_iff₀ log_two_pos']
  nlinarith [log_two_gt]

lemma exp_three_le : Real.exp 3 ≤ 20.0856 := by
  have h := Real.exp_one_lt_d9
  have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h3]
  have h0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  calc Real.exp 1 ^ 3 ≤ (2.7182818286 : ℝ) ^ 3 := by gcongr
    _ ≤ 20.0856 := by norm_num

lemma log_two_sq_ge : (0.48045 : ℝ) ≤ Real.log 2 ^ 2 := by
  have h := log_two_gt
  have : (0.6931471803 : ℝ) ^ 2 ≤ Real.log 2 ^ 2 := by gcongr
  nlinarith

lemma C5_nonneg : 0 ≤ C5 := by unfold C5; positivity

lemma C5_le : C5 ≤ 2750000 := by
  unfold C5
  have h1 := exp_three_le
  have h2 := log_two_sq_ge
  rw [div_le_iff₀ (by positivity)]
  nlinarith

lemma etaE_nonneg : 0 ≤ etaE := by
  unfold etaE epsE thetaE
  have := cE_pos
  have := C5_nonneg
  positivity

lemma etaE_le : etaE ≤ 0.0321 := by
  unfold etaE epsE thetaE
  have h1 := cE_le
  have h2 := C5_le
  have h3 := C5_nonneg
  norm_num
  nlinarith

lemma four_rpow_pos : 0 < (4 : ℝ) ^ (5 / 4 : ℝ) := by positivity

lemma four_rpow_le : (4 : ℝ) ^ (5 / 4 : ℝ) ≤ 5.66 := by
  have h : ((4 : ℝ) ^ (5 / 4 : ℝ)) ^ (4 : ℕ) = 1024 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  by_contra hc
  rw [not_le] at hc
  have : (5.66 : ℝ) ^ (4 : ℕ) < ((4 : ℝ) ^ (5 / 4 : ℝ)) ^ (4 : ℕ) := by
    gcongr
  rw [h] at this
  norm_num at this

lemma hcondE : (5 / 4 : ℝ) + (4 : ℝ) ^ (5 / 4 : ℝ) * etaE ≤ cE := by
  have h1 := four_rpow_le
  have h2 := etaE_le
  have h3 := etaE_nonneg
  have h4 := cE_ge
  have h5 := four_rpow_pos
  have : (4 : ℝ) ^ (5 / 4 : ℝ) * etaE ≤ 5.66 * 0.0321 :=
    mul_le_mul h1 h2 h3 (by norm_num)
  linarith

lemma C4_nonneg : 0 ≤ C4 := by unfold C4 CT epsE; positivity

lemma C4_le : C4 ≤ 2 ^ 89 := by
  unfold C4 CT epsE
  have h1 : Real.log 2 ^ 3 ≤ 1 := pow_le_one₀ log_two_pos'.le log_two_le_one
  have h0 : 0 ≤ Real.log 2 ^ 3 := by have := log_two_pos'; positivity
  norm_num
  nlinarith

end PPF.Explicit.Fn
