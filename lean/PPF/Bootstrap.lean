import Mathlib

/-!
# The bootstrap (L10)

A nonnegative antitone sequence obeying the delayed recurrence
`r (j+1) ≤ r j (1 − c/j) + (η/j + e j) · r ⌊j/3⌋ + g j`
with `6/5 + 4^{6/5} η ≤ c` decays like `j^{−6/5}`, hence is summable.

Proof: `s j = j^{6/5} r j` and `M j = max_{i ≤ j} s i` satisfy
`M (j+1) ≤ M j · exp(4^{6/5} e j) + (j+1)^{6/5} g j` for large `j`.
-/

namespace PPF

open Real

/-- `(x+1)^α ≤ x^α · exp(α/x)` for `x > 0`, `α ≥ 0`. -/
lemma add_one_rpow_le_rpow_mul_exp {x α : ℝ} (hx : 0 < x) (hα : 0 ≤ α) :
    (x + 1) ^ α ≤ x ^ α * Real.exp (α / x) := by
  have h1 : x + 1 ≤ x * Real.exp (1 / x) := by
    have := Real.add_one_le_exp (1 / x)
    calc x + 1 = x * (1 / x + 1) := by rw [mul_add, mul_one_div_cancel hx.ne', mul_one]; ring
      _ ≤ x * Real.exp (1 / x) := mul_le_mul_of_nonneg_left this hx.le
  calc (x + 1) ^ α ≤ (x * Real.exp (1 / x)) ^ α :=
        Real.rpow_le_rpow (by linarith) h1 hα
    _ = x ^ α * Real.exp (1 / x) ^ α := Real.mul_rpow hx.le (Real.exp_pos _).le
    _ = x ^ α * Real.exp (α / x) := by
        rw [← Real.exp_mul, show 1 / x * α = α / x by ring]

/-- The sequence `B 0 = K`, `B (n+1) = B n · exp(A e n) + v n`. -/
noncomputable def recSeq (K A : ℝ) (e v : ℕ → ℝ) : ℕ → ℝ
  | 0 => K
  | n + 1 => recSeq K A e v n * Real.exp (A * e n) + v n

lemma recSeq_bound (K A : ℝ) (e v : ℕ → ℝ) (hA : 0 ≤ A)
    (he0 : ∀ j, 0 ≤ e j) (hv0 : ∀ j, 0 ≤ v j) (j : ℕ) :
    recSeq K A e v j ≤
      (K + ∑ i ∈ Finset.range j, v i) * Real.exp (A * ∑ i ∈ Finset.range j, e i) := by
  induction j with
  | zero => simp [recSeq]
  | succ n ih =>
    rw [recSeq, Finset.sum_range_succ, Finset.sum_range_succ, mul_add, Real.exp_add]
    have hE : 1 ≤ Real.exp (A * ∑ i ∈ Finset.range n, e i) * Real.exp (A * e n) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      exact add_nonneg (mul_nonneg hA (Finset.sum_nonneg (fun i _ => he0 i)))
        (mul_nonneg hA (he0 n))
    have hpos : 0 ≤ Real.exp (A * e n) := (Real.exp_pos _).le
    calc recSeq K A e v n * Real.exp (A * e n) + v n
        ≤ (K + ∑ i ∈ Finset.range n, v i) * Real.exp (A * ∑ i ∈ Finset.range n, e i)
            * Real.exp (A * e n) + v n := by gcongr
      _ = (K + ∑ i ∈ Finset.range n, v i)
            * (Real.exp (A * ∑ i ∈ Finset.range n, e i) * Real.exp (A * e n)) + v n := by
          ring
      _ ≤ (K + ∑ i ∈ Finset.range n, v i)
            * (Real.exp (A * ∑ i ∈ Finset.range n, e i) * Real.exp (A * e n))
          + v n * (Real.exp (A * ∑ i ∈ Finset.range n, e i) * Real.exp (A * e n)) := by
          gcongr
          exact le_mul_of_one_le_right (hv0 n) hE
      _ = (K + (∑ i ∈ Finset.range n, v i + v n))
            * (Real.exp (A * ∑ i ∈ Finset.range n, e i) * Real.exp (A * e n)) := by ring

lemma recSeq_nonneg (K A : ℝ) (e v : ℕ → ℝ) (hK : 0 ≤ K) (hv0 : ∀ j, 0 ≤ v j) (n : ℕ) :
    0 ≤ recSeq K A e v n := by
  induction n with
  | zero => simpa [recSeq] using hK
  | succ n ih =>
    rw [recSeq]
    exact add_nonneg (mul_nonneg ih (Real.exp_pos _).le) (hv0 n)

lemma recSeq_mono (K A : ℝ) (e v : ℕ → ℝ) (hK : 0 ≤ K) (hA : 0 ≤ A)
    (he0 : ∀ j, 0 ≤ e j) (hv0 : ∀ j, 0 ≤ v j) : Monotone (recSeq K A e v) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [recSeq]
  have h0 := recSeq_nonneg K A e v hK hv0 n
  have h1 : 1 ≤ Real.exp (A * e n) := Real.one_le_exp (mul_nonneg hA (he0 n))
  nlinarith [hv0 n]

/-- One step of the bootstrap. -/
lemma step_bound (r e g : ℕ → ℝ) (c η α : ℝ) (hα : 0 ≤ α) (hr0 : ∀ j, 0 ≤ r j)
    (hη : 0 ≤ η) (he0 : ∀ j, 0 ≤ e j)
    (hcond : α + (4 : ℝ) ^ α * η ≤ c)
    (j : ℕ) (hj12 : 12 ≤ j) (hjc : c ≤ j)
    (hrec : r (j + 1) ≤ r j * (1 - c / j) + (η / j + e j) * r (j / 3) + g j)
    (b : ℝ) (hb : ∀ i ≤ j, (i : ℝ) ^ α * r i ≤ b) :
    ((j : ℝ) + 1) ^ α * r (j + 1)
      ≤ b * Real.exp ((4 : ℝ) ^ α * e j) + ((j : ℝ) + 1) ^ α * g j := by
  have h4 : 0 < (4 : ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) α
  have hjpos : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
  have hj12r : (12 : ℝ) ≤ j := by exact_mod_cast hj12
  set q := j / 3 with hq
  have hq_le : q ≤ j := Nat.div_le_self j 3
  have h3 : j ≤ 3 * q + 2 := by omega
  have h3r : (j : ℝ) ≤ 3 * (q : ℝ) + 2 := by exact_mod_cast h3
  have hq_lb : (j : ℝ) / 4 ≤ (q : ℝ) := by linarith
  have hbj : (j : ℝ) ^ α * r j ≤ b := hb j le_rfl
  have hbq : (q : ℝ) ^ α * r q ≤ b := hb q hq_le
  have hb0 : 0 ≤ b := le_trans (mul_nonneg (by positivity) (hr0 j)) hbj
  have hqα : ((j : ℝ) / 4) ^ α ≤ (q : ℝ) ^ α :=
    Real.rpow_le_rpow (by positivity) hq_lb hα
  have hjα : (j : ℝ) ^ α = (4 : ℝ) ^ α * ((j : ℝ) / 4) ^ α := by
    rw [Real.div_rpow hjpos.le (by norm_num)]
    field_simp
  have hjq : (j : ℝ) ^ α * r q ≤ (4 : ℝ) ^ α * b := by
    rw [hjα, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ h4.le
    calc ((j : ℝ) / 4) ^ α * r q ≤ (q : ℝ) ^ α * r q :=
          mul_le_mul_of_nonneg_right hqα (hr0 q)
      _ ≤ b := hbq
  -- the `g`-free part of the recurrence
  set X := r j * (1 - c / j) + (η / j + e j) * r q with hX
  have hcj : 0 ≤ 1 - c / j := sub_nonneg.mpr ((div_le_one hjpos).mpr hjc)
  have hcoef : 0 ≤ η / j + e j := add_nonneg (div_nonneg hη hjpos.le) (he0 j)
  have hX0 : 0 ≤ X := add_nonneg (mul_nonneg (hr0 j) hcj) (mul_nonneg hcoef (hr0 q))
  have hjX : (j : ℝ) ^ α * X ≤ b * (1 - c / j + (4 : ℝ) ^ α * (η / j + e j)) := by
    have : (j : ℝ) ^ α * X
        = ((j : ℝ) ^ α * r j) * (1 - c / j) + (η / j + e j) * ((j : ℝ) ^ α * r q) := by
      rw [hX]; ring
    rw [this]
    calc ((j : ℝ) ^ α * r j) * (1 - c / j) + (η / j + e j) * ((j : ℝ) ^ α * r q)
        ≤ b * (1 - c / j) + (η / j + e j) * ((4 : ℝ) ^ α * b) := by
          gcongr
      _ = b * (1 - c / j + (4 : ℝ) ^ α * (η / j + e j)) := by ring
  have hexp1 : 1 - c / j + (4 : ℝ) ^ α * (η / j + e j)
      ≤ Real.exp (-(c / j) + (4 : ℝ) ^ α * η / j + (4 : ℝ) ^ α * e j) := by
    have := Real.add_one_le_exp (-(c / j) + (4 : ℝ) ^ α * η / j + (4 : ℝ) ^ α * e j)
    have e1 : (4 : ℝ) ^ α * (η / j + e j) = (4 : ℝ) ^ α * η / j + (4 : ℝ) ^ α * e j := by
      ring
    linarith
  have hpow := add_one_rpow_le_rpow_mul_exp hjpos hα
  have hexp2 : α / j + (-(c / j) + (4 : ℝ) ^ α * η / j + (4 : ℝ) ^ α * e j)
      ≤ (4 : ℝ) ^ α * e j := by
    have : α / j + (-(c / j) + (4 : ℝ) ^ α * η / j + (4 : ℝ) ^ α * e j)
        = (α + (4 : ℝ) ^ α * η - c) / j + (4 : ℝ) ^ α * e j := by ring
    rw [this]
    have : (α + (4 : ℝ) ^ α * η - c) / j ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hjpos.le
    linarith
  have hXbound : ((j : ℝ) + 1) ^ α * X ≤ b * Real.exp ((4 : ℝ) ^ α * e j) := by
    calc ((j : ℝ) + 1) ^ α * X ≤ ((j : ℝ) ^ α * Real.exp (α / j)) * X :=
          mul_le_mul_of_nonneg_right hpow hX0
      _ = Real.exp (α / j) * ((j : ℝ) ^ α * X) := by ring
      _ ≤ Real.exp (α / j) * (b * (1 - c / j + (4 : ℝ) ^ α * (η / j + e j))) :=
          mul_le_mul_of_nonneg_left hjX (Real.exp_pos _).le
      _ ≤ Real.exp (α / j)
            * (b * Real.exp (-(c / j) + (4 : ℝ) ^ α * η / j + (4 : ℝ) ^ α * e j)) := by
          gcongr
      _ = b * Real.exp (α / j + (-(c / j) + (4 : ℝ) ^ α * η / j + (4 : ℝ) ^ α * e j)) := by
          rw [Real.exp_add (α / j)]; ring
      _ ≤ b * Real.exp ((4 : ℝ) ^ α * e j) := by
          gcongr
  have hr1 : r (j + 1) ≤ X + g j := by rw [hX]; exact hrec
  calc ((j : ℝ) + 1) ^ α * r (j + 1) ≤ ((j : ℝ) + 1) ^ α * (X + g j) :=
        mul_le_mul_of_nonneg_left hr1 (by positivity)
    _ = ((j : ℝ) + 1) ^ α * X + ((j : ℝ) + 1) ^ α * g j := by ring
    _ ≤ b * Real.exp ((4 : ℝ) ^ α * e j) + ((j : ℝ) + 1) ^ α * g j := by
        gcongr

-- `hanti` and `hc` are part of the frozen interface but not needed by the proof.
set_option linter.unusedVariables false in
theorem summable_of_recurrence (r e g : ℕ → ℝ) (c η : ℝ) (j₀ : ℕ)
    (hr0 : ∀ j, 0 ≤ r j) (hanti : Antitone r)
    (hc : 0 ≤ c) (hη : 0 ≤ η) (he0 : ∀ j, 0 ≤ e j) (hg0 : ∀ j, 0 ≤ g j)
    (he : Summable e) (hg : Summable (fun j : ℕ => ((j : ℝ) + 1) ^ (6 / 5 : ℝ) * g j))
    (hcond : (6 / 5 : ℝ) + (4 : ℝ) ^ (6 / 5 : ℝ) * η ≤ c)
    (hrec : ∀ j, j₀ ≤ j →
      r (j + 1) ≤ r j * (1 - c / j) + (η / j + e j) * r (j / 3) + g j) :
    Summable r := by
  have hα0 : (0 : ℝ) ≤ 6 / 5 := by norm_num
  have h4 : (0 : ℝ) ≤ (4 : ℝ) ^ (6 / 5 : ℝ) := by positivity
  obtain ⟨n, hn⟩ := exists_nat_ge c
  set J : ℕ := j₀ + 12 + n with hJdef
  have hJ0 : j₀ ≤ J := by omega
  have hJ12 : 12 ≤ J := by omega
  have hJc : c ≤ (J : ℝ) := by
    have : (n : ℝ) ≤ (J : ℝ) := by exact_mod_cast (by omega : n ≤ J)
    linarith
  set s : ℕ → ℝ := fun i => (i : ℝ) ^ (6 / 5 : ℝ) * r i with hs
  have hs0 : ∀ i, 0 ≤ s i := fun i => mul_nonneg (by positivity) (hr0 i)
  set K : ℝ := ∑ i ∈ Finset.range (J + 1), s i with hKdef
  have hK0 : 0 ≤ K := Finset.sum_nonneg (fun i _ => hs0 i)
  have hKs : ∀ i ≤ J, s i ≤ K := fun i hi =>
    Finset.single_le_sum (f := s) (fun k _ => hs0 k) (Finset.mem_range.mpr (by omega))
  set v : ℕ → ℝ := fun j => ((j : ℝ) + 1) ^ (6 / 5 : ℝ) * g j with hv
  have hv0 : ∀ j, 0 ≤ v j := fun j => mul_nonneg (by positivity) (hg0 j)
  set B : ℕ → ℝ := recSeq K ((4 : ℝ) ^ (6 / 5 : ℝ)) e v with hB
  have hBmono : Monotone B := recSeq_mono K _ e v hK0 h4 he0 hv0
  have hmain : ∀ j, J ≤ j → ∀ i ≤ j, s i ≤ B j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
      intro i hi
      have : B 0 ≤ B J := hBmono (Nat.zero_le J)
      have hB0 : B 0 = K := rfl
      linarith [hKs i hi]
    | succ m hm ih =>
      intro i hi
      rcases Nat.lt_or_ge i (m + 1) with h | h
      · exact (ih i (by omega)).trans (hBmono (Nat.le_succ m))
      · have hi' : i = m + 1 := by omega
        subst hi'
        have hm12 : 12 ≤ m := hJ12.trans hm
        have hmc : c ≤ (m : ℝ) := hJc.trans (by exact_mod_cast hm)
        have hstep := step_bound r e g c η (6 / 5) hα0 hr0 hη he0 hcond m hm12 hmc
          (hrec m (hJ0.trans hm)) (B m) ih
        have hBs : B (m + 1) = B m * Real.exp ((4 : ℝ) ^ (6 / 5 : ℝ) * e m) + v m := rfl
        rw [hBs]
        simp only [hs, hv]
        push_cast
        exact hstep
  -- uniform bound on `B`
  have hBD' : ∀ j, B j ≤ (K + ∑' i, v i) * Real.exp ((4 : ℝ) ^ (6 / 5 : ℝ) * ∑' i, e i) := by
    intro j
    refine (recSeq_bound K _ e v h4 he0 hv0 j).trans ?_
    have hvs : ∑ i ∈ Finset.range j, v i ≤ ∑' i, v i :=
      hg.sum_le_tsum _ (fun i _ => hv0 i)
    have hes : ∑ i ∈ Finset.range j, e i ≤ ∑' i, e i :=
      he.sum_le_tsum _ (fun i _ => he0 i)
    have hv' : 0 ≤ ∑' i, v i := tsum_nonneg hv0
    gcongr
  obtain ⟨D, hBD⟩ : ∃ D : ℝ, ∀ j, B j ≤ D := ⟨_, hBD'⟩
  -- decay `r j ≤ D j^{-6/5}` for `j ≥ J`, then compare with a p-series
  have hdecay : ∀ k : ℕ, r (k + J) ≤ D * (((k + J : ℕ) : ℝ) ^ (6 / 5 : ℝ))⁻¹ := by
    intro k
    have hpos : 0 < ((k + J : ℕ) : ℝ) ^ (6 / 5 : ℝ) := by
      apply Real.rpow_pos_of_pos
      exact_mod_cast (by omega : 0 < k + J)
    rw [le_mul_inv_iff₀ hpos]
    have := (hmain (k + J) (by omega) (k + J) le_rfl).trans (hBD (k + J))
    simp only [hs] at this
    linarith
  have hp : Summable (fun k : ℕ => D * (((k + J : ℕ) : ℝ) ^ (6 / 5 : ℝ))⁻¹) := by
    apply Summable.mul_left
    have := (Real.summable_nat_rpow_inv (p := (6 / 5 : ℝ))).mpr (by norm_num)
    exact (summable_nat_add_iff J).mpr this
  have : Summable (fun k : ℕ => r (k + J)) :=
    Summable.of_nonneg_of_le (fun k => hr0 _) hdecay hp
  exact (summable_nat_add_iff J).mp this

end PPF
