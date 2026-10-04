import PPF.Tree
import PPF.Blocks
import PPF.ShortGaps
import PPF.Bootstrap

/-!
# The conditional theorem (L6–L9)

From the two analytic inputs, the surviving mass `r` obeys the delayed
recurrence of `PPF.Bootstrap`, so it is summable.

For large `j`, with `d = ⌊j/2⌋` and `b₀ = ⌈θ j⌉`, the counting inequality
`count_ineq j d` is split at `b₀`:

* the main term (blocks of `S (j − d)`, `d` levels deep) is bounded below by the
  good blocks of `card_badBlocks_le` and `primeCount_ge_of_good`;
* long gaps `b₀ ≤ b ≤ d` are bounded above by `primeCount_le_of_good`, and their
  main part telescopes through `r_succ`;
* short gaps `b < b₀` are bounded by `short_gap_le`.

Dividing by `2^j` gives `r (j+1) ≤ r j (1 − c/j) + (η/j + e j) r ⌊j/3⌋ + g j`
with `c = 1/log 2`, `η = 2cε + 5 C₅ θ`, `e j = O(1/j²)` and `g j = O(j³ 2^{−θ j})`.
-/

namespace PPF

open Finset

/-! ### Bookkeeping on `S`, `P`, `r` -/

lemma cond_mem_level_of_mem_S {m n : ℕ} (h : n ∈ S m) : n ∈ level m :=
  (Finset.mem_filter.mp h).1

lemma cond_mem_S_of_mem_P {m n : ℕ} (h : n ∈ P m) : n ∈ S m :=
  (Finset.mem_filter.mp h).1

lemma cond_card_P_eq (m : ℕ) : (#(P m) : ℝ) = 2 ^ m * (r m - r (m + 1)) := by
  rw [r_succ]
  field_simp
  ring

lemma cond_card_S_eq (m : ℕ) : (#(S m) : ℝ) = 2 ^ m * r m := by
  unfold r
  field_simp

lemma cond_mem_badBlocks {ε : ℝ} {j b M : ℕ} (hM : M ∈ level (j - b))
    (h : ε * 2 ^ b < |thetaBlock M b - 2 ^ b|) : M ∈ badBlocks ε j b := by
  classical
  unfold badBlocks
  rw [Finset.mem_filter]
  exact ⟨hM, h⟩

lemma cond_good_of_not_bad {ε : ℝ} {j b M : ℕ} (hM : M ∈ level (j - b))
    (h : M ∉ badBlocks ε j b) : |thetaBlock M b - 2 ^ b| ≤ ε * 2 ^ b :=
  not_lt.mp fun h' => h (cond_mem_badBlocks hM h')

/-! ### The three pieces of the counting inequality -/

/-- Main term: good blocks of `S (j − d)` carry their expected number of primes. -/
lemma cond_main_lower (ε : ℝ) (hε1 : ε ≤ 1) (j d : ℕ) (hdj : d ≤ j) :
    ((#(S (j - d)) : ℝ) - #(badBlocks ε j d))
        * ((1 - ε) * 2 ^ d / (((j : ℝ) + 1) * Real.log 2))
      ≤ ((∑ N ∈ S (j - d), primeCount (block N d) : ℕ) : ℝ) := by
  classical
  set L := (1 - ε) * 2 ^ d / (((j : ℝ) + 1) * Real.log 2) with hL
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL0 : 0 ≤ L := by
    have : 0 ≤ 1 - ε := by linarith
    positivity
  have hcard : ((#(S (j - d)) : ℝ) - #(badBlocks ε j d))
      ≤ #(S (j - d) \ badBlocks ε j d) := by
    have h := Finset.card_le_card_sdiff_add_card (s := S (j - d)) (t := badBlocks ε j d)
    have h' : ((#(S (j - d)) : ℕ) : ℝ)
        ≤ ((#(S (j - d) \ badBlocks ε j d) : ℕ) : ℝ) + ((#(badBlocks ε j d) : ℕ) : ℝ) := by
      exact_mod_cast h
    linarith
  calc ((#(S (j - d)) : ℝ) - #(badBlocks ε j d)) * L
      ≤ (#(S (j - d) \ badBlocks ε j d) : ℝ) * L := mul_le_mul_of_nonneg_right hcard hL0
    _ = ∑ _N ∈ S (j - d) \ badBlocks ε j d, L := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ N ∈ S (j - d) \ badBlocks ε j d, (primeCount (block N d) : ℝ) := by
        apply Finset.sum_le_sum
        intro N hN
        rw [Finset.mem_sdiff] at hN
        have hNlev : N ∈ level (j - d) := cond_mem_level_of_mem_S hN.1
        exact primeCount_ge_of_good hNlev hdj (cond_good_of_not_bad hNlev hN.2)
    _ ≤ ∑ N ∈ S (j - d), (primeCount (block N d) : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
        intro _ _ _
        positivity
    _ = ((∑ N ∈ S (j - d), primeCount (block N d) : ℕ) : ℝ) := by push_cast; rfl

/-- Long gaps: good blocks carry at most their expected number of primes, bad
blocks at most `2^b`. -/
lemma cond_long_upper (ε : ℝ) (hε0 : 0 ≤ ε) (j b : ℕ) (hbj : b ≤ j) (hj : 1 ≤ j) :
    ((∑ p ∈ P (j - b), primeCount (block p b) : ℕ) : ℝ)
      ≤ #(P (j - b)) * ((1 + ε) * 2 ^ b / ((j : ℝ) * Real.log 2))
        + #(badBlocks ε j b) * 2 ^ b := by
  classical
  set U := (1 + ε) * 2 ^ b / ((j : ℝ) * Real.log 2) with hU
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hU0 : 0 ≤ U := by positivity
  have hterm : ∀ p ∈ P (j - b), (primeCount (block p b) : ℝ)
      ≤ U + (if p ∈ badBlocks ε j b then (2 : ℝ) ^ b else 0) := by
    intro p hp
    have hplev : p ∈ level (j - b) := cond_mem_level_of_mem_S (cond_mem_S_of_mem_P hp)
    by_cases hbad : p ∈ badBlocks ε j b
    · rw [if_pos hbad]
      have h1 : (primeCount (block p b) : ℝ) ≤ 2 ^ b := by
        exact_mod_cast primeCount_block_le p b
      linarith
    · rw [if_neg hbad, add_zero]
      exact primeCount_le_of_good hplev hbj hj (cond_good_of_not_bad hplev hbad)
  calc ((∑ p ∈ P (j - b), primeCount (block p b) : ℕ) : ℝ)
      = ∑ p ∈ P (j - b), (primeCount (block p b) : ℝ) := by push_cast; rfl
    _ ≤ ∑ p ∈ P (j - b), (U + (if p ∈ badBlocks ε j b then (2 : ℝ) ^ b else 0)) :=
        Finset.sum_le_sum hterm
    _ = #(P (j - b)) * U + ∑ p ∈ P (j - b) ∩ badBlocks ε j b, (2 : ℝ) ^ b := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.sum_ite_mem]
    _ = #(P (j - b)) * U + #(P (j - b) ∩ badBlocks ε j b) * 2 ^ b := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ #(P (j - b)) * U + #(badBlocks ε j b) * 2 ^ b := by
        gcongr
        exact Finset.inter_subset_right

/-- The main parts of the long gaps telescope. -/
lemma cond_sum_long_telescope (j b₀ d : ℕ) (hb₀d : b₀ ≤ d) (hdj : d ≤ j) :
    ∑ b ∈ Finset.Ico b₀ (d + 1), (#(P (j - b)) : ℝ) * 2 ^ b
      = 2 ^ j * (r (j - d) - r (j - b₀ + 1)) := by
  have hterm : ∀ b ∈ Finset.Ico b₀ (d + 1),
      (#(P (j - b)) : ℝ) * 2 ^ b = 2 ^ j * (r (j - b) - r (j - b + 1)) := by
    intro b hb
    have hbj : b ≤ j := by simp only [Finset.mem_Ico] at hb; omega
    rw [cond_card_P_eq]
    have : (2 : ℝ) ^ (j - b) * 2 ^ b = 2 ^ j := by
      rw [← pow_add, Nat.sub_add_cancel hbj]
    calc (2 : ℝ) ^ (j - b) * (r (j - b) - r (j - b + 1)) * 2 ^ b
        = ((2 : ℝ) ^ (j - b) * 2 ^ b) * (r (j - b) - r (j - b + 1)) := by ring
      _ = 2 ^ j * (r (j - b) - r (j - b + 1)) := by rw [this]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_Ico_eq_sum_range]
  set v : ℕ → ℝ := fun k => r (j - b₀ + 1 - k) with hv
  have hk : ∀ k ∈ Finset.range (d + 1 - b₀),
      r (j - (b₀ + k)) - r (j - (b₀ + k) + 1) = v (k + 1) - v k := by
    intro k hk
    simp only [Finset.mem_range] at hk
    simp only [hv]
    rw [show j - (b₀ + k) = j - b₀ + 1 - (k + 1) by omega,
      show j - b₀ + 1 - (k + 1) + 1 = j - b₀ + 1 - k by omega]
  rw [Finset.sum_congr rfl hk, Finset.sum_range_sub]
  simp only [hv]
  rw [show j - b₀ + 1 - (d + 1 - b₀) = j - d by omega, Nat.sub_zero]

/-- Short gaps. -/
lemma cond_short_upper (C₅ : ℝ) (hC₅ : 0 ≤ C₅)
    (hshort : ∀ j b d' : ℕ, 1 ≤ b → b ≤ d' → b + d' ≤ j →
      ((∑ p ∈ P (j - b), primeCount (block p b) : ℕ) : ℝ)
        ≤ C₅ * #(S (j - b - d')) * 2 ^ (b + d') / (d' : ℝ) ^ 2)
    (j d b₀ : ℕ) (hb₀d : b₀ ≤ d) (hidx : b₀ + d + j / 3 ≤ j) :
    ∑ b ∈ Finset.Ico 1 b₀, ((∑ p ∈ P (j - b), primeCount (block p b) : ℕ) : ℝ)
      ≤ b₀ * (C₅ * r (j / 3) * 2 ^ j / (d : ℝ) ^ 2) := by
  have hconst : 0 ≤ C₅ * r (j / 3) * 2 ^ j / (d : ℝ) ^ 2 := by
    have := r_nonneg (j / 3)
    positivity
  calc ∑ b ∈ Finset.Ico 1 b₀, ((∑ p ∈ P (j - b), primeCount (block p b) : ℕ) : ℝ)
      ≤ ∑ _b ∈ Finset.Ico 1 b₀, C₅ * r (j / 3) * 2 ^ j / (d : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro b hb
        simp only [Finset.mem_Ico] at hb
        refine le_trans (hshort j b d hb.1 (by omega) (by omega)) ?_
        rw [cond_card_S_eq]
        have hpow : (2 : ℝ) ^ (j - b - d) * 2 ^ (b + d) = 2 ^ j := by
          rw [← pow_add, show j - b - d + (b + d) = j by omega]
        have hr : r (j - b - d) ≤ r (j / 3) := r_antitone (by omega)
        have hd2 : 0 ≤ (d : ℝ) ^ 2 := by positivity
        calc C₅ * (2 ^ (j - b - d) * r (j - b - d)) * 2 ^ (b + d) / (d : ℝ) ^ 2
            = C₅ * r (j - b - d) * ((2 : ℝ) ^ (j - b - d) * 2 ^ (b + d)) / (d : ℝ) ^ 2 := by
              ring
          _ = C₅ * r (j - b - d) * 2 ^ j / (d : ℝ) ^ 2 := by rw [hpow]
          _ ≤ C₅ * r (j / 3) * 2 ^ j / (d : ℝ) ^ 2 := by gcongr
    _ = ((b₀ - 1 : ℕ) : ℝ) * (C₅ * r (j / 3) * 2 ^ j / (d : ℝ) ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ico]
    _ ≤ b₀ * (C₅ * r (j / 3) * 2 ^ j / (d : ℝ) ^ 2) := by
        gcongr
        exact_mod_cast Nat.sub_le b₀ 1

/-- Bad blocks along the long gaps. -/
lemma cond_bad_long_sum (ε C₄ : ℝ) (hC₄ : 0 ≤ C₄) (j b₀ n : ℕ)
    (hb : ∀ b ∈ Finset.Ico b₀ n,
      (#(badBlocks ε j b) : ℝ) ≤ C₄ * (j : ℝ) ^ 3 * 2 ^ j / 4 ^ b) :
    ∑ b ∈ Finset.Ico b₀ n, (#(badBlocks ε j b) : ℝ) * 2 ^ b
      ≤ 2 ^ j * (2 * C₄ * (j : ℝ) ^ 3 * (1 / 2) ^ b₀) := by
  have hK : 0 ≤ C₄ * (j : ℝ) ^ 3 * 2 ^ j := by positivity
  calc ∑ b ∈ Finset.Ico b₀ n, (#(badBlocks ε j b) : ℝ) * 2 ^ b
      ≤ ∑ b ∈ Finset.Ico b₀ n, C₄ * (j : ℝ) ^ 3 * 2 ^ j * (1 / 2) ^ b := by
        apply Finset.sum_le_sum
        intro b hbm
        have h4 : (4 : ℝ) ^ b = 2 ^ b * 2 ^ b := by
          rw [← mul_pow]; norm_num
        calc (#(badBlocks ε j b) : ℝ) * 2 ^ b
            ≤ C₄ * (j : ℝ) ^ 3 * 2 ^ j / 4 ^ b * 2 ^ b := by
              gcongr
              exact hb b hbm
          _ = C₄ * (j : ℝ) ^ 3 * 2 ^ j * (1 / 2) ^ b := by
              rw [h4, one_div_pow]
              field_simp
    _ = C₄ * (j : ℝ) ^ 3 * 2 ^ j * ∑ b ∈ Finset.Ico b₀ n, (1 / 2 : ℝ) ^ b := by
        rw [Finset.mul_sum]
    _ ≤ C₄ * (j : ℝ) ^ 3 * 2 ^ j * ((1 / 2 : ℝ) ^ b₀ / (1 - 1 / 2)) := by
        gcongr
        exact geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)
    _ = 2 ^ j * (2 * C₄ * (j : ℝ) ^ 3 * (1 / 2) ^ b₀) := by ring

/-- `2^{−b} ≤ (2^{−θ})^j` once `θ j ≤ b`. -/
lemma cond_half_pow_le (θ : ℝ) (j b : ℕ) (h : θ * j ≤ b) :
    (1 / 2 : ℝ) ^ b ≤ ((2 : ℝ) ^ (-θ)) ^ j := by
  rw [← Real.rpow_natCast ((2 : ℝ) ^ (-θ)), ← Real.rpow_mul (by norm_num)]
  have hb : (1 / 2 : ℝ) ^ b = (2 : ℝ) ^ (-(b : ℝ)) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, inv_pow]
  rw [hb]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  linarith

/-! ### The per-level recurrence -/

/-- Pure real algebra closing the recurrence step. -/
lemma cond_algebra (c ε θ C₄ C₅ J D B0 R B rj r3 x y q t Z : ℝ)
    (hc : 0 ≤ c) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hJ : 20 ≤ J) (hD : (J - 1) / 2 ≤ D)
    (hθ : 0 ≤ θ) (hB0 : B0 ≤ θ * J + 1) (hC₄ : 0 ≤ C₄) (hC₅ : 0 ≤ C₅)
    (hrj : 0 ≤ rj) (hrjB : rj ≤ B) (hBR : B ≤ R) (hR3 : R ≤ r3)
    (hx0 : 0 ≤ x) (hxq : x ≤ q) (hyq : y ≤ q) (ht : 0 ≤ t)
    (hZ : (1 - ε) * c * R / (J + 1) - (1 - ε) * c * C₄ * t * x / (J + 1)
        - B0 * C₅ * r3 / D ^ 2 - (1 + ε) * c * (R - B) / J - 2 * C₄ * t * y ≤ Z) :
    rj - Z ≤ rj * (1 - c / J)
      + ((2 * c * ε + 5 * C₅ * θ) / J + (2 * c + 5 * C₅) / J ^ 2) * r3
      + (c + 2) * C₄ * t * q := by
  have hJpos : 0 < J := by linarith
  have hB0' : 0 ≤ B := le_trans hrj hrjB
  have hR0 : 0 ≤ R := le_trans hB0' hBR
  have hr30 : 0 ≤ r3 := le_trans hR0 hR3
  -- (a) the main and long-gap terms
  have hk : (1 + ε) / J - (1 - ε) / (J + 1) ≤ 2 * ε / J + 2 / J ^ 2 := by
    have e : 2 * ε / J + 2 / J ^ 2 - ((1 + ε) / J - (1 - ε) / (J + 1))
        = (J + ε * J + 2) / (J ^ 2 * (J + 1)) := by
      field_simp
      ring
    have : 0 ≤ (J + ε * J + 2) / (J ^ 2 * (J + 1)) := by positivity
    linarith
  have h1 : (1 + ε) * (R - B) ≤ (1 + ε) * R - rj := by nlinarith
  have ha : (1 + ε) * c * (R - B) / J - (1 - ε) * c * R / (J + 1)
      ≤ -(c * rj / J) + c * (2 * ε / J + 2 / J ^ 2) * R := by
    have e1 : (1 + ε) * c * (R - B) / J - (1 - ε) * c * R / (J + 1)
        = c * ((1 + ε) * (R - B) / J - (1 - ε) * R / (J + 1)) := by ring
    have ha1 : (1 + ε) * (R - B) / J ≤ ((1 + ε) * R - rj) / J :=
      div_le_div_of_nonneg_right h1 hJpos.le
    have ha2 : R * ((1 + ε) / J - (1 - ε) / (J + 1)) ≤ R * (2 * ε / J + 2 / J ^ 2) :=
      mul_le_mul_of_nonneg_left hk hR0
    have e2 : ((1 + ε) * R - rj) / J - (1 - ε) * R / (J + 1)
        = -(rj / J) + R * ((1 + ε) / J - (1 - ε) / (J + 1)) := by ring
    rw [e1]
    calc c * ((1 + ε) * (R - B) / J - (1 - ε) * R / (J + 1))
        ≤ c * (((1 + ε) * R - rj) / J - (1 - ε) * R / (J + 1)) := by gcongr
      _ = c * (-(rj / J) + R * ((1 + ε) / J - (1 - ε) / (J + 1))) := by rw [e2]
      _ ≤ c * (-(rj / J) + R * (2 * ε / J + 2 / J ^ 2)) := by gcongr
      _ = -(c * rj / J) + c * (2 * ε / J + 2 / J ^ 2) * R := by ring
  -- (b) bad blocks in the main term
  have hb : (1 - ε) * c * C₄ * t * x / (J + 1) ≤ c * C₄ * t * q := by
    have hf : (1 - ε) / (J + 1) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    have hf0 : 0 ≤ (1 - ε) / (J + 1) := div_nonneg (by linarith) (by linarith)
    calc (1 - ε) * c * C₄ * t * x / (J + 1) = (c * C₄ * t) * x * ((1 - ε) / (J + 1)) := by
          ring
      _ ≤ (c * C₄ * t) * x * 1 := by gcongr
      _ ≤ (c * C₄ * t) * q := by rw [mul_one]; gcongr
  -- (c) short gaps
  have hD0 : 0 < D := by linarith
  have hDsq : J ^ 2 / 5 ≤ D ^ 2 := by
    have h0 : 0 ≤ (J - 1) / 2 := by linarith
    have : ((J - 1) / 2) ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ h0 hD 2
    nlinarith
  have hB0D : B0 / D ^ 2 ≤ 5 * θ / J + 5 / J ^ 2 := by
    have hnum : 0 ≤ θ * J + 1 := by positivity
    calc B0 / D ^ 2 ≤ (θ * J + 1) / D ^ 2 := div_le_div_of_nonneg_right hB0 (by positivity)
      _ ≤ (θ * J + 1) / (J ^ 2 / 5) := div_le_div_of_nonneg_left hnum (by positivity) hDsq
      _ = 5 * θ / J + 5 / J ^ 2 := by field_simp
  have hcc : B0 * C₅ * r3 / D ^ 2 ≤ C₅ * r3 * (5 * θ / J + 5 / J ^ 2) := by
    calc B0 * C₅ * r3 / D ^ 2 = C₅ * r3 * (B0 / D ^ 2) := by ring
      _ ≤ C₅ * r3 * (5 * θ / J + 5 / J ^ 2) := by gcongr
  -- (d), (e)
  have hd : c * (2 * ε / J + 2 / J ^ 2) * R ≤ c * (2 * ε / J + 2 / J ^ 2) * r3 := by
    gcongr
  have he : 2 * C₄ * t * y ≤ 2 * C₄ * t * q := by gcongr
  have key : rj * (1 - c / J)
      + ((2 * c * ε + 5 * C₅ * θ) / J + (2 * c + 5 * C₅) / J ^ 2) * r3
      + (c + 2) * C₄ * t * q
      = rj - c * rj / J + c * (2 * ε / J + 2 / J ^ 2) * r3
        + C₅ * r3 * (5 * θ / J + 5 / J ^ 2) + c * C₄ * t * q + 2 * C₄ * t * q := by
    ring
  rw [key]
  linarith

/-- One step of the recurrence, for `j` large. -/
lemma cond_rec_step {c ε θ C₄ C₅ : ℝ} {j₁ : ℕ} (hc : c = 1 / Real.log 2)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 1000)
    (hC₄ : 0 ≤ C₄) (hC₅ : 0 ≤ C₅)
    (hbad : ∀ j b : ℕ, j₁ ≤ j → θ * j ≤ b → 2 * b ≤ j →
      (#(badBlocks ε j b) : ℝ) ≤ C₄ * (j : ℝ) ^ 3 * 2 ^ j / 4 ^ b)
    (hshort : ∀ j b d' : ℕ, 1 ≤ b → b ≤ d' → b + d' ≤ j →
      ((∑ p ∈ P (j - b), primeCount (block p b) : ℕ) : ℝ)
        ≤ C₅ * #(S (j - b - d')) * 2 ^ (b + d') / (d' : ℝ) ^ 2)
    (j : ℕ) (hjj₁ : j₁ ≤ j) (hj20 : 20 ≤ j) :
    r (j + 1) ≤ r j * (1 - c / j)
      + ((2 * c * ε + 5 * C₅ * θ) / j + (2 * c + 5 * C₅) / (j : ℝ) ^ 2) * r (j / 3)
      + (c + 2) * C₄ * (j : ℝ) ^ 3 * ((2 : ℝ) ^ (-θ)) ^ j := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hJ : (20 : ℝ) ≤ j := by exact_mod_cast hj20
  have hJpos : (0 : ℝ) < j := by linarith
  set d := j / 2 with hd_def
  set b₀ := ⌈θ * j⌉₊ with hb₀_def
  -- sizes of `d` and `b₀`
  have hd_le : (d : ℝ) ≤ (j : ℝ) / 2 := Nat.cast_div_le
  have hd_ge : ((j : ℝ) - 1) / 2 ≤ d := by
    have : j ≤ 2 * d + 1 := by omega
    have : (j : ℝ) ≤ 2 * d + 1 := by exact_mod_cast this
    linarith
  have hθj0 : 0 ≤ θ * j := by positivity
  have hb₀_ge : θ * j ≤ b₀ := Nat.le_ceil _
  have hb₀_le : (b₀ : ℝ) ≤ θ * j + 1 := (Nat.ceil_lt_add_one hθj0).le
  have hb₀_pos : 1 ≤ b₀ := Nat.one_le_ceil_iff.mpr (by positivity)
  have hj3 : ((j / 3 : ℕ) : ℝ) ≤ (j : ℝ) / 3 := Nat.cast_div_le
  have hidx : b₀ + d + j / 3 ≤ j := by
    have : (b₀ : ℝ) + d + ((j / 3 : ℕ) : ℝ) ≤ j := by nlinarith
    exact_mod_cast this
  have hb₀d : b₀ ≤ d := by omega
  have hd1 : 1 ≤ d := by omega
  have h2d : 2 * d ≤ j := by omega
  have hdj : d ≤ j := by omega
  have hθd : θ * j ≤ d := by nlinarith
  -- the counting inequality, split at `b₀`
  set F : ℕ → ℕ := fun b => ∑ p ∈ P (j - b), primeCount (block p b) with hF
  set A : ℕ := ∑ N ∈ S (j - d), primeCount (block N d) with hA
  have hcount : A ≤ #(P j) + ∑ b ∈ Finset.Icc 1 d, F b := count_ineq j d (by omega) hd1 hdj
  have hIcc : Finset.Icc 1 d = Finset.Ico 1 (d + 1) := by
    ext b; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  have hsplit : ∑ b ∈ Finset.Icc 1 d, F b
      = ∑ b ∈ Finset.Ico 1 b₀, F b + ∑ b ∈ Finset.Ico b₀ (d + 1), F b := by
    rw [hIcc, Finset.sum_Ico_consecutive _ hb₀_pos (by omega)]
  rw [hsplit] at hcount
  have hcountR : (A : ℝ) ≤ (#(P j) : ℝ) + ∑ b ∈ Finset.Ico 1 b₀, (F b : ℝ)
      + ∑ b ∈ Finset.Ico b₀ (d + 1), (F b : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).mpr hcount
    push_cast at this
    linarith
  -- main term
  set R := r (j - d) with hR
  set B := r (j - b₀ + 1) with hB
  set r3 := r (j / 3) with hr3
  set x : ℝ := (1 / 2) ^ d with hx
  set y : ℝ := (1 / 2) ^ b₀ with hy
  set q : ℝ := ((2 : ℝ) ^ (-θ)) ^ j with hq
  set t : ℝ := (j : ℝ) ^ 3 with ht
  have hmain := cond_main_lower ε hε1 j d hdj
  have hbad_d := hbad j d hjj₁ hθd h2d
  have h2j : (2 : ℝ) ^ j = 2 ^ (j - d) * 2 ^ d := by rw [← pow_add, Nat.sub_add_cancel hdj]
  have h4d : (4 : ℝ) ^ d = 2 ^ d * 2 ^ d := by rw [← mul_pow]; norm_num
  have hL0 : 0 ≤ (1 - ε) * 2 ^ d / (((j : ℝ) + 1) * Real.log 2) := by
    have : 0 ≤ 1 - ε := by linarith
    positivity
  have hA_lower : (2 : ℝ) ^ j * ((1 - ε) * c * R / ((j : ℝ) + 1)
      - (1 - ε) * c * C₄ * t * x / ((j : ℝ) + 1)) ≤ (A : ℝ) := by
    have hS := cond_card_S_eq (j - d)
    have step : ((2 : ℝ) ^ (j - d) * R - C₄ * (j : ℝ) ^ 3 * 2 ^ j / 4 ^ d)
          * ((1 - ε) * 2 ^ d / (((j : ℝ) + 1) * Real.log 2))
        ≤ ((#(S (j - d)) : ℝ) - #(badBlocks ε j d))
          * ((1 - ε) * 2 ^ d / (((j : ℝ) + 1) * Real.log 2)) := by
      apply mul_le_mul_of_nonneg_right _ hL0
      rw [hS]
      linarith
    have eq : ((2 : ℝ) ^ (j - d) * R - C₄ * (j : ℝ) ^ 3 * 2 ^ j / 4 ^ d)
          * ((1 - ε) * 2 ^ d / (((j : ℝ) + 1) * Real.log 2))
        = (2 : ℝ) ^ j * ((1 - ε) * c * R / ((j : ℝ) + 1)
          - (1 - ε) * c * C₄ * t * x / ((j : ℝ) + 1)) := by
      rw [h2j, h4d, hx, ht, hc, one_div_pow]
      field_simp
    rw [← eq]
    exact le_trans step hmain
  -- long gaps
  have hLg : ∑ b ∈ Finset.Ico b₀ (d + 1), (F b : ℝ)
      ≤ (2 : ℝ) ^ j * ((1 + ε) * c * (R - B) / j) + (2 : ℝ) ^ j * (2 * C₄ * t * y) := by
    have hterm : ∀ b ∈ Finset.Ico b₀ (d + 1), (F b : ℝ)
        ≤ ((1 + ε) / ((j : ℝ) * Real.log 2)) * ((#(P (j - b)) : ℝ) * 2 ^ b)
          + (#(badBlocks ε j b) : ℝ) * 2 ^ b := by
      intro b hb
      simp only [Finset.mem_Ico] at hb
      have := cond_long_upper ε hε0 j b (by omega) (by omega)
      calc (F b : ℝ) ≤ _ := this
        _ = _ := by ring
    have hbadsum := cond_bad_long_sum ε C₄ hC₄ j b₀ (d + 1) (by
      intro b hb
      simp only [Finset.mem_Ico] at hb
      exact hbad j b hjj₁ (le_trans hb₀_ge (by exact_mod_cast hb.1)) (by omega))
    have htel := cond_sum_long_telescope j b₀ d hb₀d hdj
    calc ∑ b ∈ Finset.Ico b₀ (d + 1), (F b : ℝ)
        ≤ ∑ b ∈ Finset.Ico b₀ (d + 1), (((1 + ε) / ((j : ℝ) * Real.log 2))
            * ((#(P (j - b)) : ℝ) * 2 ^ b) + (#(badBlocks ε j b) : ℝ) * 2 ^ b) :=
          Finset.sum_le_sum hterm
      _ = ((1 + ε) / ((j : ℝ) * Real.log 2))
            * ∑ b ∈ Finset.Ico b₀ (d + 1), (#(P (j - b)) : ℝ) * 2 ^ b
          + ∑ b ∈ Finset.Ico b₀ (d + 1), (#(badBlocks ε j b) : ℝ) * 2 ^ b := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ ((1 + ε) / ((j : ℝ) * Real.log 2)) * (2 ^ j * (R - B))
          + 2 ^ j * (2 * C₄ * (j : ℝ) ^ 3 * (1 / 2) ^ b₀) := by
          rw [htel]
          linarith
      _ = (2 : ℝ) ^ j * ((1 + ε) * c * (R - B) / j) + (2 : ℝ) ^ j * (2 * C₄ * t * y) := by
          rw [hc, ht, hy]
          field_simp
  -- short gaps
  have hSh : ∑ b ∈ Finset.Ico 1 b₀, (F b : ℝ)
      ≤ (2 : ℝ) ^ j * ((b₀ : ℝ) * C₅ * r3 / (d : ℝ) ^ 2) := by
    have := cond_short_upper C₅ hC₅ hshort j d b₀ hb₀d hidx
    calc ∑ b ∈ Finset.Ico 1 b₀, (F b : ℝ) ≤ _ := this
      _ = _ := by rw [hr3]; ring
  -- lower bound for `#P j / 2^j`
  set Z := (#(P j) : ℝ) / 2 ^ j with hZ
  have h2jpos : (0 : ℝ) < 2 ^ j := by positivity
  have hZlow : (1 - ε) * c * R / ((j : ℝ) + 1) - (1 - ε) * c * C₄ * t * x / ((j : ℝ) + 1)
      - (b₀ : ℝ) * C₅ * r3 / (d : ℝ) ^ 2 - (1 + ε) * c * (R - B) / j - 2 * C₄ * t * y ≤ Z := by
    rw [hZ, le_div_iff₀ h2jpos]
    nlinarith [hcountR, hA_lower, hLg, hSh]
  have hrsucc : r (j + 1) = r j - Z := r_succ j
  rw [hrsucc]
  -- monotonicity facts
  have hrjB : r j ≤ B := r_antitone (by omega)
  have hBR : B ≤ R := r_antitone (by omega)
  have hR3 : R ≤ r3 := r_antitone (by omega)
  have hxq : x ≤ q := cond_half_pow_le θ j d hθd
  have hyq : y ≤ q := cond_half_pow_le θ j b₀ hb₀_ge
  have halg := cond_algebra c ε θ C₄ C₅ j d b₀ R B (r j) r3 x y q t Z hc0 hε0 hε1 hJ hd_ge
    hθ0.le hb₀_le hC₄ hC₅ (r_nonneg j) hrjB hBR hR3 (by positivity) hxq hyq (by positivity) hZlow
  calc r j - Z ≤ _ := halg
    _ = _ := by rw [hq, ht]


/-! ### Constants -/

lemma cond_four_rpow_le : (4 : ℝ) ^ (6 / 5 : ℝ) ≤ 6 := by
  have ha : 0 ≤ (4 : ℝ) ^ (6 / 5 : ℝ) := by positivity
  have h5 : ((4 : ℝ) ^ (6 / 5 : ℝ)) ^ (5 : ℕ) = 4096 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    rw [show (6 / 5 : ℝ) * ((5 : ℕ) : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  by_contra hlt
  rw [not_le] at hlt
  have : (6 : ℝ) ^ (5 : ℕ) < ((4 : ℝ) ^ (6 / 5 : ℝ)) ^ (5 : ℕ) :=
    pow_lt_pow_left₀ hlt (by norm_num) (by norm_num)
  rw [h5] at this
  norm_num at this

lemma cond_c_ge : (1.44 : ℝ) ≤ 1 / Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [le_div_iff₀ hlog]
  have := Real.log_two_lt_d9
  norm_num at this ⊢
  linarith

/-! ### The conditional theorem -/

theorem summable_of_inputs (h1 : SelbergMeanSquare) (h2 : PairSieve) :
    Summable (fun n : ℕ => if PrimePrefixFree n then (1 : ℝ) / n else 0) := by
  apply summable_of_summable_r
  obtain ⟨C₅, hC₅, hshort⟩ := short_gap_le h2
  set ε : ℝ := 1 / 200 with hε
  set θ : ℝ := 1 / (1000 * (C₅ + 1)) with hθ
  have hθ0 : 0 < θ := by positivity
  have hθC : θ * C₅ ≤ 1 / 1000 := by
    rw [hθ, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hθ1 : θ ≤ 1 / 1000 := by
    rw [hθ]
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith
  have hε0 : (0 : ℝ) < ε := by norm_num
  obtain ⟨C₄', j₁, hbad'⟩ := card_badBlocks_le h1 hθ0 hε0
  set C₄ := max C₄' 0 with hC₄def
  have hC₄ : 0 ≤ C₄ := le_max_right _ _
  have hbad : ∀ j b : ℕ, j₁ ≤ j → θ * j ≤ b → 2 * b ≤ j →
      (#(badBlocks ε j b) : ℝ) ≤ C₄ * (j : ℝ) ^ 3 * 2 ^ j / 4 ^ b := by
    intro j b hj hb hb2
    refine le_trans (hbad' j b hj hb hb2) ?_
    gcongr
    exact le_max_left _ _
  set c : ℝ := 1 / Real.log 2 with hc
  have hc0 : 0 ≤ c := le_trans (by norm_num) cond_c_ge
  set η : ℝ := 2 * c * ε + 5 * C₅ * θ with hη
  set ρ : ℝ := (2 : ℝ) ^ (-θ) with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hη0 : 0 ≤ η := by positivity
  have hcond : (6 / 5 : ℝ) + (4 : ℝ) ^ (6 / 5 : ℝ) * η ≤ c := by
    have h4 := cond_four_rpow_le
    have hc144 := cond_c_ge
    have hηle : η ≤ c / 100 + 1 / 200 := by
      rw [hη, hε]
      nlinarith
    have : (4 : ℝ) ^ (6 / 5 : ℝ) * η ≤ 6 * (c / 100 + 1 / 200) := by
      have h4' : 0 ≤ (4 : ℝ) ^ (6 / 5 : ℝ) := by positivity
      calc (4 : ℝ) ^ (6 / 5 : ℝ) * η ≤ (4 : ℝ) ^ (6 / 5 : ℝ) * (c / 100 + 1 / 200) := by
            gcongr
        _ ≤ 6 * (c / 100 + 1 / 200) := by
            gcongr
    linarith
  have he : Summable (fun j : ℕ => (2 * c + 5 * C₅) / (j : ℝ) ^ 2) := by
    have := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    exact (this.mul_left (2 * c + 5 * C₅)).congr (fun j => by ring)
  have he0 : ∀ j : ℕ, 0 ≤ (2 * c + 5 * C₅) / (j : ℝ) ^ 2 := fun j => by positivity
  have hg0 : ∀ j : ℕ, 0 ≤ (c + 2) * C₄ * (j : ℝ) ^ 3 * ρ ^ j := fun j => by positivity
  have hg : Summable (fun j : ℕ => ((j : ℝ) + 1) ^ (6 / 5 : ℝ)
      * ((c + 2) * C₄ * (j : ℝ) ^ 3 * ρ ^ j)) := by
    have hgeo : Summable (fun j : ℕ => (j : ℝ) ^ 5 * ρ ^ j) :=
      summable_pow_mul_geometric_of_norm_lt_one 5 (by rw [Real.norm_eq_abs, abs_of_pos hρ0]; exact hρ1)
    refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
      (hgeo.mul_left (4 * ((c + 2) * C₄)))
    have hK : 0 ≤ (c + 2) * C₄ := by positivity
    have hj1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      linarith
    have hpow : ((j : ℝ) + 1) ^ (6 / 5 : ℝ) ≤ ((j : ℝ) + 1) ^ 2 := by
      calc ((j : ℝ) + 1) ^ (6 / 5 : ℝ) ≤ ((j : ℝ) + 1) ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hj1 (by norm_num)
        _ = ((j : ℝ) + 1) ^ 2 := by rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hpoly : ((j : ℝ) + 1) ^ 2 * (j : ℝ) ^ 3 ≤ 4 * (j : ℝ) ^ 5 := by
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · subst h0; norm_num
      · have : (1 : ℝ) ≤ j := by exact_mod_cast hpos
        have h2 : ((j : ℝ) + 1) ^ 2 ≤ 4 * (j : ℝ) ^ 2 := by nlinarith
        have h3 : (0 : ℝ) ≤ (j : ℝ) ^ 3 := by positivity
        calc ((j : ℝ) + 1) ^ 2 * (j : ℝ) ^ 3 ≤ 4 * (j : ℝ) ^ 2 * (j : ℝ) ^ 3 := by gcongr
          _ = 4 * (j : ℝ) ^ 5 := by ring
    have hρj : 0 ≤ ρ ^ j := by positivity
    calc ((j : ℝ) + 1) ^ (6 / 5 : ℝ) * ((c + 2) * C₄ * (j : ℝ) ^ 3 * ρ ^ j)
        ≤ ((j : ℝ) + 1) ^ 2 * ((c + 2) * C₄ * (j : ℝ) ^ 3 * ρ ^ j) := by gcongr
      _ = ((c + 2) * C₄) * (((j : ℝ) + 1) ^ 2 * (j : ℝ) ^ 3) * ρ ^ j := by ring
      _ ≤ ((c + 2) * C₄) * (4 * (j : ℝ) ^ 5) * ρ ^ j := by gcongr
      _ = 4 * ((c + 2) * C₄) * ((j : ℝ) ^ 5 * ρ ^ j) := by ring
  refine summable_of_recurrence r (fun j => (2 * c + 5 * C₅) / (j : ℝ) ^ 2)
    (fun j => (c + 2) * C₄ * (j : ℝ) ^ 3 * ρ ^ j) c η (max j₁ 20) r_nonneg r_antitone
    hc0 hη0 he0 hg0 he hg hcond ?_
  intro j hj
  have hstep := cond_rec_step (c := c) (ε := ε) (θ := θ) (C₄ := C₄) (C₅ := C₅) (j₁ := j₁) hc
    (by norm_num) (by norm_num) hθ0 hθ1 hC₄ hC₅ hbad hshort j
    (le_trans (le_max_left _ _) hj) (le_trans (le_max_right _ _) hj)
  calc r (j + 1) ≤ _ := hstep
    _ = _ := by rw [hη, hρ]

end PPF
