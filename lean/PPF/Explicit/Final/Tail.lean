import PPF.Explicit.Final.Sums

/-!
# Explicit bound: the weighted error series `Σ_{j ≥ J} (j+1)^{5/4} gE j ≤ 1`

`gE j = (cE+2)·C4·j³·2^{−j/2^32}`. With `β = log 2/2^33` we have `2^{−θ} = e^{−2β}`,
`j^5 ≤ 120·e^{βj}/β^5`, so `(j+1)^{5/4} gE j ≤ K₂ e^{−βj}` with `K₂ = 480(cE+2)C4/β^5`,
and the geometric tail from `J = 2^44` is `e^{−βJ}/(1−e^{−β}) ≤ 2^{−2048}·2/β`.
-/

namespace PPF.Explicit.Fn

open PPF.Explicit Real Finset

noncomputable def βE : ℝ := Real.log 2 / 2 ^ 33

lemma βE_pos : 0 < βE := by unfold βE; have := log_two_pos'; positivity

lemma βE_le_one : βE ≤ 1 := by
  unfold βE; rw [div_le_one (by positivity)]; linarith [log_two_le_one]

lemma inv_βE_le : 1 / βE ≤ 2 ^ 34 := by
  unfold βE
  rw [one_div_div, div_le_iff₀ log_two_pos']
  have := log_two_ge_half
  nlinarith

noncomputable def K2 : ℝ := 480 * (cE + 2) * C4 / βE ^ 5

lemma two_rpow_neg_theta : (2 : ℝ) ^ (-thetaE) = Real.exp (-(2 * βE)) := by
  rw [Real.rpow_def_of_pos two_pos]
  unfold thetaE βE
  congr 1
  ring

lemma gE_eq (j : ℕ) :
    gE j = (cE + 2) * C4 * (j : ℝ) ^ 3 * Real.exp ((j : ℝ) * (-(2 * βE))) := by
  unfold gE
  rw [two_rpow_neg_theta, Real.exp_nat_mul]

lemma pow_five_le (j : ℕ) : (j : ℝ) ^ 5 ≤ 120 * Real.exp (βE * j) / βE ^ 5 := by
  have hβ := βE_pos
  have h := Real.pow_div_factorial_le_exp (x := βE * j) (by positivity) 5
  have hf : ((Nat.factorial 5 : ℕ) : ℝ) = 120 := by norm_num [Nat.factorial]
  rw [hf, mul_pow, div_le_iff₀ (by norm_num)] at h
  rw [le_div_iff₀ (by positivity)]
  nlinarith [h]

lemma rpow_succ_le (j : ℕ) (hj : 1 ≤ j) : ((j : ℝ) + 1) ^ (5 / 4 : ℝ) ≤ 4 * (j : ℝ) ^ 2 := by
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have h1 : ((j : ℝ) + 1) ^ (5 / 4 : ℝ) ≤ ((j : ℝ) + 1) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  rw [Real.rpow_two] at h1
  nlinarith

lemma v_le (j : ℕ) (hj : 1 ≤ j) :
    ((j : ℝ) + 1) ^ (5 / 4 : ℝ) * gE j ≤ K2 * Real.exp (-βE * j) := by
  have hβ := βE_pos
  have hc := cE_pos
  have hC4 := C4_nonneg
  have hA : 0 ≤ (cE + 2) * C4 := by positivity
  rw [gE_eq]
  have hr := rpow_succ_le j hj
  have hp := pow_five_le j
  have hE0 : 0 ≤ Real.exp ((j : ℝ) * (-(2 * βE))) := (Real.exp_pos _).le
  have hj0 : (0 : ℝ) ≤ j := j.cast_nonneg
  calc ((j : ℝ) + 1) ^ (5 / 4 : ℝ) * ((cE + 2) * C4 * (j : ℝ) ^ 3 * Real.exp ((j : ℝ) * (-(2 * βE))))
      ≤ 4 * (j : ℝ) ^ 2 * ((cE + 2) * C4 * (j : ℝ) ^ 3 * Real.exp ((j : ℝ) * (-(2 * βE)))) := by
        gcongr
    _ = 4 * ((cE + 2) * C4) * ((j : ℝ) ^ 5 * Real.exp ((j : ℝ) * (-(2 * βE)))) := by ring
    _ ≤ 4 * ((cE + 2) * C4) * (120 * Real.exp (βE * j) / βE ^ 5 * Real.exp ((j : ℝ) * (-(2 * βE)))) := by
        gcongr
    _ = K2 * (Real.exp (βE * j) * Real.exp ((j : ℝ) * (-(2 * βE)))) := by
        unfold K2; field_simp; ring
    _ = K2 * Real.exp (-βE * j) := by
        rw [← Real.exp_add]; congr 2; ring

lemma exp_neg_βE_J : Real.exp (-βE) ^ J = 1 / 2 ^ 2048 := by
  rw [← Real.exp_nat_mul]
  have h : ((J : ℕ) : ℝ) * (-βE) = -((2048 : ℕ) * Real.log 2) := by
    rw [J_real]; unfold βE; push_cast; ring
  rw [h, Real.exp_neg, Real.exp_nat_mul, Real.exp_log two_pos]
  norm_num

lemma one_sub_exp_neg_ge : βE / 2 ≤ 1 - Real.exp (-βE) := by
  have hβ := βE_pos
  have hβ1 := βE_le_one
  have h1 : 1 + βE ≤ Real.exp βE := by linarith [Real.add_one_le_exp βE]
  have h2 : Real.exp (-βE) ≤ 1 / (1 + βE) := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by linarith) h1
  have h3 : βE / 2 ≤ 1 - 1 / (1 + βE) := by
    rw [show 1 - 1 / (1 + βE) = βE / (1 + βE) by field_simp; ring]
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    nlinarith
  linarith

set_option exponentiation.threshold 4096 in
lemma sum_v_le (n : ℕ) :
    ∑ i ∈ range n, (((i + J : ℕ) : ℝ) + 1) ^ (5 / 4 : ℝ) * gE (i + J) ≤ 1 := by
  have hβ := βE_pos
  set q : ℝ := Real.exp (-βE) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    rw [hq, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have hK2 : 0 ≤ K2 := by
    unfold K2; have := cE_pos; have := C4_nonneg; positivity
  have hterm : ∀ i ∈ range n, (((i + J : ℕ) : ℝ) + 1) ^ (5 / 4 : ℝ) * gE (i + J)
      ≤ K2 * q ^ (J + i) := by
    intro i _
    have hj : 1 ≤ i + J := by unfold J; omega
    refine (v_le (i + J) hj).trans (le_of_eq ?_)
    rw [hq, ← Real.exp_nat_mul]
    congr 2; push_cast; ring
  calc ∑ i ∈ range n, (((i + J : ℕ) : ℝ) + 1) ^ (5 / 4 : ℝ) * gE (i + J)
      ≤ ∑ i ∈ range n, K2 * q ^ (J + i) := sum_le_sum hterm
    _ = K2 * ∑ k ∈ Ico J (J + n), q ^ k := by
        rw [mul_sum, sum_Ico_eq_sum_range]; simp
    _ ≤ K2 * (q ^ J / (1 - q)) := by
        gcongr; exact geom_sum_Ico_le_of_lt_one hq0 hq1
    _ ≤ 1 := by
        rw [hq, exp_neg_βE_J]
        have h1 := one_sub_exp_neg_ge
        have hpos : 0 < 1 - Real.exp (-βE) := by linarith
        rw [div_div, mul_div_assoc', div_le_one (by positivity)]
        -- K2 ≤ 2^2048 · (1 − e^{−β}); suffices K2 ≤ 2^2048 · β/2
        refine le_trans ?_ (mul_le_mul_of_nonneg_left h1 (by positivity))
        unfold K2
        have hc2 : cE + 2 ≤ 4 := by linarith [cE_le_two]
        have hC4 := C4_le
        have hC40 := C4_nonneg
        have hinv := inv_βE_le
        have hinv6 : (1 / βE) ^ 6 ≤ (2 ^ 34 : ℝ) ^ 6 := by
          gcongr
        have hc0 : 0 ≤ cE + 2 := by linarith [cE_pos]
        have : 480 * (cE + 2) * C4 / βE ^ 5 * 1
            = (480 * (cE + 2) * C4 * (1 / βE) ^ 6) * (βE / 2) * 2 := by
          field_simp
        rw [this]
        have hb : 480 * (cE + 2) * C4 * (1 / βE) ^ 6 ≤ 480 * 4 * 2 ^ 89 * (2 ^ 34 : ℝ) ^ 6 := by
          gcongr
        have hβ2 : 0 ≤ βE / 2 := by positivity
        calc 480 * (cE + 2) * C4 * (1 / βE) ^ 6 * (βE / 2) * 2
            ≤ 480 * 4 * 2 ^ 89 * (2 ^ 34 : ℝ) ^ 6 * (βE / 2) * 2 := by gcongr
          _ ≤ 2 ^ 2048 * (βE / 2) := by
            have h305 : (480 * 4 * 2 ^ 89 * (2 ^ 34 : ℝ) ^ 6) * 2 ≤ 2 ^ 305 := by norm_num
            have h2048 : (2 : ℝ) ^ 305 ≤ 2 ^ 2048 :=
              pow_le_pow_right₀ (by norm_num) (by norm_num)
            nlinarith

end PPF.Explicit.Fn
