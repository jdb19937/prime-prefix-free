import PPF.Tree

/-!
# Blocks with the expected number of primes (L6, L7)

`SelbergMeanSquare` bounds the number of blocks `[M 2^b, (M+1) 2^b)` at level `j`
whose θ-mass deviates from `2^b` by more than `ε 2^b` (shifting argument), and a
good block has `≈ 2^b / (j log 2)` primes.
-/

namespace PPF

open Finset Filter Topology

/-- θ-mass of a block. -/
noncomputable def thetaBlock (M b : ℕ) : ℝ :=
  ∑ p ∈ (block M b).filter Nat.Prime, Real.log p

open Classical in
/-- Blocks `b` levels below level `j − b` whose θ-mass is off by more than `ε 2^b`. -/
noncomputable def badBlocks (ε : ℝ) (j b : ℕ) : Finset ℕ :=
  (level (j - b)).filter (fun M => ε * 2 ^ b < |thetaBlock M b - 2 ^ b|)

end PPF

namespace PPF.BlocksAux

open Finset Filter Topology

/-! ### θ-mass of integer intervals -/

/-- Weight `log p` on primes, `0` elsewhere. -/
noncomputable def primeLogWt (p : ℕ) : ℝ := if p.Prime then Real.log p else 0

lemma primeLogWt_nonneg (p : ℕ) : 0 ≤ primeLogWt p := by
  unfold primeLogWt
  split_ifs with hp
  · exact Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  · exact le_rfl

lemma primeLogWt_le_log {p B : ℕ} (hp : p < B) : primeLogWt p ≤ Real.log B := by
  have hB : (1 : ℝ) ≤ B := by exact_mod_cast (show 1 ≤ B by omega)
  unfold primeLogWt
  split_ifs with hpr
  · exact Real.log_le_log (by exact_mod_cast hpr.pos) (by exact_mod_cast hp.le)
  · exact Real.log_nonneg hB

lemma sum_primeLogWt_nonneg (s : Finset ℕ) : 0 ≤ ∑ p ∈ s, primeLogWt p :=
  sum_nonneg fun p _ => primeLogWt_nonneg p

lemma sum_primeLogWt_Ico_le (A B : ℕ) :
    ∑ p ∈ Ico A B, primeLogWt p ≤ ((B - A : ℕ) : ℝ) * Real.log B := by
  calc ∑ p ∈ Ico A B, primeLogWt p ≤ ∑ _p ∈ Ico A B, Real.log B :=
        sum_le_sum fun p hp => primeLogWt_le_log (mem_Ico.mp hp).2
    _ = ((B - A : ℕ) : ℝ) * Real.log B := by rw [sum_const, Nat.card_Ico, nsmul_eq_mul]

lemma theta_natCast_eq (m : ℕ) :
    Chebyshev.theta (m : ℝ) = ∑ p ∈ Ico 0 (m + 1), primeLogWt p := by
  rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast, sum_filter]
  rfl

lemma theta_sub_theta (n h : ℕ) :
    Chebyshev.theta ((n + h : ℕ) : ℝ) - Chebyshev.theta (n : ℝ)
      = ∑ p ∈ Ico (n + 1) (n + h + 1), primeLogWt p := by
  rw [theta_natCast_eq, theta_natCast_eq,
    ← sum_Ico_consecutive _ (Nat.zero_le (n + 1)) (by omega : n + 1 ≤ n + h + 1)]
  ring

lemma thetaBlock_eq (M b : ℕ) :
    thetaBlock M b = ∑ p ∈ Ico (M * 2 ^ b) (M * 2 ^ b + 2 ^ b), primeLogWt p := by
  unfold thetaBlock block primeLogWt
  rw [sum_filter, show (M + 1) * 2 ^ b = M * 2 ^ b + 2 ^ b by ring]

/-- Summing over consecutive blocks of length `h`. -/
lemma sum_Ico_blocks (g : ℕ → ℝ) (h A : ℕ) : ∀ B, A ≤ B →
    ∑ M ∈ Ico A B, ∑ n ∈ Ico (M * h) (M * h + h), g n = ∑ n ∈ Ico (A * h) (B * h), g n := by
  intro B hAB
  induction B, hAB using Nat.le_induction with
  | base => simp
  | succ B hAB ih =>
    rw [sum_Ico_succ_top hAB, ih, show (B + 1) * h = B * h + h by ring,
      sum_Ico_consecutive _ (Nat.mul_le_mul_right h hAB) (Nat.le_add_right _ _)]

/-! ### Blocks at level `j` -/

lemma block_bounds {j b M : ℕ} (hM : M ∈ level (j - b)) (hbj : b ≤ j) :
    2 ^ j ≤ M * 2 ^ b ∧ (M + 1) * 2 ^ b ≤ 2 ^ (j + 1) := by
  unfold level at hM
  rw [mem_Ico] at hM
  constructor
  · calc 2 ^ j = 2 ^ (j - b) * 2 ^ b := by rw [← pow_add, Nat.sub_add_cancel hbj]
      _ ≤ M * 2 ^ b := Nat.mul_le_mul_right _ hM.1
  · calc (M + 1) * 2 ^ b ≤ 2 ^ (j - b + 1) * 2 ^ b := Nat.mul_le_mul_right _ hM.2
      _ = 2 ^ (j + 1) := by rw [← pow_add, show j - b + 1 + b = j + 1 by omega]

lemma mem_block_bounds {j b M p : ℕ} (hM : M ∈ level (j - b)) (hbj : b ≤ j)
    (hp : p ∈ block M b) : 2 ^ j ≤ p ∧ p < 2 ^ (j + 1) := by
  obtain ⟨h1, h2⟩ := block_bounds hM hbj
  unfold block at hp
  rw [mem_Ico] at hp
  exact ⟨h1.trans hp.1, lt_of_lt_of_le hp.2 h2⟩

lemma thetaBlock_le_count_mul {j b M : ℕ} (hM : M ∈ level (j - b)) (hbj : b ≤ j) :
    thetaBlock M b ≤ (primeCount (block M b) : ℝ) * (((j : ℝ) + 1) * Real.log 2) := by
  unfold thetaBlock primeCount
  calc ∑ p ∈ (block M b).filter Nat.Prime, Real.log p
      ≤ ∑ _p ∈ (block M b).filter Nat.Prime, ((j : ℝ) + 1) * Real.log 2 := by
        refine sum_le_sum fun p hp => ?_
        have hp' := (mem_filter.mp hp)
        have hb := mem_block_bounds hM hbj hp'.1
        have hpos : (0 : ℝ) < p := by exact_mod_cast hp'.2.pos
        calc Real.log p ≤ Real.log ((2 : ℝ) ^ (j + 1)) :=
              Real.log_le_log hpos (by exact_mod_cast hb.2.le)
          _ = ((j : ℝ) + 1) * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
    _ = _ := by rw [sum_const, nsmul_eq_mul]

lemma count_mul_le_thetaBlock {j b M : ℕ} (hM : M ∈ level (j - b)) (hbj : b ≤ j) :
    (primeCount (block M b) : ℝ) * ((j : ℝ) * Real.log 2) ≤ thetaBlock M b := by
  unfold thetaBlock primeCount
  calc (#((block M b).filter Nat.Prime) : ℝ) * ((j : ℝ) * Real.log 2)
      = ∑ _p ∈ (block M b).filter Nat.Prime, (j : ℝ) * Real.log 2 := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ p ∈ (block M b).filter Nat.Prime, Real.log p := by
        refine sum_le_sum fun p hp => ?_
        have hp' := (mem_filter.mp hp)
        have hb := mem_block_bounds hM hbj hp'.1
        calc (j : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ j) := by rw [Real.log_pow]
          _ ≤ Real.log p := Real.log_le_log (by positivity) (by exact_mod_cast hb.1)

/-! ### The shifting argument -/

/-- In a bad block, every window `(n, n+h]` with `n ∈ [Mh, Mh + L)` has a large error,
provided `L log(3X) ≤ εh/4`. -/
lemma window_error_large {ε : ℝ} {j b M L n : ℕ} (hM : M ∈ badBlocks ε j b) (hbj : b ≤ j)
    (hLh : L ≤ 2 ^ b) (hn1 : M * 2 ^ b ≤ n) (hn2 : n < M * 2 ^ b + L)
    (hL : (L : ℝ) * Real.log (3 * 2 ^ j) ≤ ε * 2 ^ b / 4) (hε : 0 < ε) :
    (ε * 2 ^ b / 2) ^ 2 ≤
      (Chebyshev.theta ((n + 2 ^ b : ℕ) : ℝ) - Chebyshev.theta (n : ℝ) - ((2 ^ b : ℕ) : ℝ)) ^ 2 := by
  unfold badBlocks at hM
  rw [mem_filter] at hM
  obtain ⟨hlev, hbad⟩ := hM
  set h := 2 ^ b with hh
  have hMup : M * h + h ≤ 2 * 2 ^ j := by
    have := (block_bounds hlev hbj).2
    rw [pow_succ, ← hh] at this
    linarith [show (M + 1) * h = M * h + h by ring]
  have hX : h ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hbj
  -- decompose the block and the window
  have hTB : thetaBlock M b = ∑ p ∈ Ico (M * h) (n + 1), primeLogWt p
      + ∑ p ∈ Ico (n + 1) (M * h + h), primeLogWt p := by
    rw [thetaBlock_eq, sum_Ico_consecutive _ (by omega) (by omega)]
  have hW : Chebyshev.theta ((n + h : ℕ) : ℝ) - Chebyshev.theta (n : ℝ)
      = ∑ p ∈ Ico (n + 1) (M * h + h), primeLogWt p
      + ∑ p ∈ Ico (M * h + h) (n + h + 1), primeLogWt p := by
    rw [theta_sub_theta, sum_Ico_consecutive _ (by omega) (by omega)]
  set S1 := ∑ p ∈ Ico (M * h) (n + 1), primeLogWt p
  set S2 := ∑ p ∈ Ico (M * h + h) (n + h + 1), primeLogWt p
  have hlog3 : 0 ≤ Real.log (3 * 2 ^ j) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    linarith)
  have hS1 : 0 ≤ S1 ∧ S1 ≤ ε * 2 ^ b / 4 := by
    refine ⟨sum_primeLogWt_nonneg _, ?_⟩
    calc S1 ≤ ((n + 1 - M * h : ℕ) : ℝ) * Real.log (n + 1 : ℕ) := sum_primeLogWt_Ico_le _ _
      _ ≤ (L : ℝ) * Real.log (3 * 2 ^ j) := by
          apply mul_le_mul
          · exact_mod_cast (show n + 1 - M * h ≤ L by omega)
          · exact Real.log_le_log (by positivity)
              (by exact_mod_cast (show n + 1 ≤ 3 * 2 ^ j by omega))
          · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ n + 1 by omega))
          · positivity
      _ ≤ ε * 2 ^ b / 4 := hL
  have hS2 : 0 ≤ S2 ∧ S2 ≤ ε * 2 ^ b / 4 := by
    refine ⟨sum_primeLogWt_nonneg _, ?_⟩
    calc S2 ≤ ((n + h + 1 - (M * h + h) : ℕ) : ℝ) * Real.log (n + h + 1 : ℕ) :=
          sum_primeLogWt_Ico_le _ _
      _ ≤ (L : ℝ) * Real.log (3 * 2 ^ j) := by
          apply mul_le_mul
          · exact_mod_cast (show n + h + 1 - (M * h + h) ≤ L by omega)
          · exact Real.log_le_log (by positivity)
              (by exact_mod_cast (show n + h + 1 ≤ 3 * 2 ^ j by omega))
          · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ n + h + 1 by omega))
          · positivity
      _ ≤ ε * 2 ^ b / 4 := hL
  have hhR : ((h : ℕ) : ℝ) = (2 : ℝ) ^ b := by rw [hh]; push_cast; ring
  rw [hW, hhR]
  have hb0 : (0 : ℝ) ≤ ε * 2 ^ b / 2 := by positivity
  have key : ε * 2 ^ b / 2 ≤
      |∑ p ∈ Ico (n + 1) (M * h + h), primeLogWt p + S2 - 2 ^ b| := by
    have hdiff : thetaBlock M b - 2 ^ b
        = (∑ p ∈ Ico (n + 1) (M * h + h), primeLogWt p + S2 - 2 ^ b) + (S1 - S2) := by
      rw [hTB]; ring
    rw [hdiff] at hbad
    have := abs_add_le (∑ p ∈ Ico (n + 1) (M * h + h), primeLogWt p + S2 - 2 ^ b) (S1 - S2)
    have hS12 : |S1 - S2| ≤ ε * 2 ^ b / 4 := by
      rw [abs_le]; constructor <;> linarith [hS1.1, hS1.2, hS2.1, hS2.2]
    have h2b : (0 : ℝ) < 2 ^ b := by positivity
    nlinarith
  calc (ε * 2 ^ b / 2) ^ 2
      ≤ |∑ p ∈ Ico (n + 1) (M * h + h), primeLogWt p + S2 - 2 ^ b| ^ 2 :=
        pow_le_pow_left₀ hb0 key 2
    _ = _ := sq_abs _

end PPF.BlocksAux

namespace PPF

open Finset Filter Topology BlocksAux

/-- L7, lower bound. -/
theorem primeCount_ge_of_good {ε : ℝ} {j b M : ℕ} (hM : M ∈ level (j - b)) (hbj : b ≤ j)
    (hgood : |thetaBlock M b - 2 ^ b| ≤ ε * 2 ^ b) :
    (1 - ε) * 2 ^ b / (((j : ℝ) + 1) * Real.log 2) ≤ primeCount (block M b) := by
  have hpos : 0 < ((j : ℝ) + 1) * Real.log 2 := by positivity
  rw [div_le_iff₀ hpos]
  have h1 := (abs_le.mp hgood).1
  have h2 := thetaBlock_le_count_mul hM hbj
  linarith

/-- L7, upper bound. -/
theorem primeCount_le_of_good {ε : ℝ} {j b M : ℕ} (hM : M ∈ level (j - b)) (hbj : b ≤ j)
    (hj : 1 ≤ j) (hgood : |thetaBlock M b - 2 ^ b| ≤ ε * 2 ^ b) :
    (primeCount (block M b) : ℝ) ≤ (1 + ε) * 2 ^ b / ((j : ℝ) * Real.log 2) := by
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hpos : 0 < (j : ℝ) * Real.log 2 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    positivity
  rw [le_div_iff₀ hpos]
  have h1 := (abs_le.mp hgood).2
  have h2 := count_mul_le_thetaBlock hM hbj
  linarith

/-- Trivial bound. -/
theorem primeCount_block_le (M b : ℕ) : primeCount (block M b) ≤ 2 ^ b := by
  unfold primeCount block
  calc #((Ico (M * 2 ^ b) ((M + 1) * 2 ^ b)).filter Nat.Prime)
      ≤ #(Ico (M * 2 ^ b) ((M + 1) * 2 ^ b)) := card_filter_le _ _
    _ = 2 ^ b := by rw [Nat.card_Ico, add_mul, one_mul, Nat.add_sub_cancel_left]

/-- L6. -/
theorem card_badBlocks_le (h1 : SelbergMeanSquare) {θ ε : ℝ} (hθ : 0 < θ) (hε : 0 < ε) :
    ∃ C : ℝ, ∃ j₁ : ℕ, ∀ j b : ℕ, j₁ ≤ j → θ * j ≤ b → 2 * b ≤ j →
      (#(badBlocks ε j b) : ℝ) ≤ C * (j : ℝ) ^ 3 * 2 ^ j / 4 ^ b := by
  obtain ⟨C₁, hC₁⟩ := h1 θ hθ
  set ε' := min ε 1 with hε'
  have hε'0 : 0 < ε' := lt_min hε one_pos
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  set lg := Real.log 2 with hlg
  have hlg0 : 0 < lg := Real.log_pos (by norm_num)
  set ρ : ℝ := (2 : ℝ) ^ θ with hρ
  have hρ1 : 1 < ρ := Real.one_lt_rpow (by norm_num) hθ
  have hρ0 : 0 < ρ := by linarith
  -- growth: eventually `24 lg j < ε' ρ^j`
  have htend := tendsto_pow_const_div_const_pow_of_one_lt 1 hρ1
  have hcpos : 0 < ε' / (24 * lg) := by positivity
  obtain ⟨j₂, hj₂⟩ := eventually_atTop.mp ((tendsto_order.1 htend).2 _ hcpos)
  set C₁' := max C₁ 0
  refine ⟨64 * C₁' * lg ^ 3 / (ε' * ε ^ 2), max j₂ 2, ?_⟩
  intro j b hj hθb hbj
  have hj2 : 2 ≤ j := le_trans (le_max_right _ _) hj
  have hjj₂ : j₂ ≤ j := le_trans (le_max_left _ _) hj
  have hbj' : b ≤ j := by omega
  have hjR : (2 : ℝ) ≤ j := by exact_mod_cast hj2
  have hjpos : (0 : ℝ) < j := by linarith
  -- real quantities
  set hR : ℝ := (2 : ℝ) ^ b with hhR
  set XR : ℝ := (2 : ℝ) ^ j with hXR
  have hhR0 : 0 < hR := by positivity
  have hXR0 : 0 < XR := by positivity
  -- `ρ^j ≤ h`
  have hρh : ρ ^ j ≤ hR := by
    rw [hρ, ← Real.rpow_mul_natCast (by norm_num), hhR, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hθb
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
  set y : ℝ := ε' * hR / (4 * Real.log (3 * XR)) with hy
  set L : ℕ := ⌊y⌋₊ with hL
  have hy0 : 0 ≤ y := by positivity
  have hLy : (L : ℝ) ≤ y := Nat.floor_le hy0
  -- `y ≥ 2`
  have hy2 : 2 ≤ y := by
    have h24 : (j : ℝ) / ρ ^ j < ε' / (24 * lg) := by
      have := hj₂ j hjj₂
      simpa using this
    rw [div_lt_div_iff₀ (by positivity) (by positivity)] at h24
    rw [hy, le_div_iff₀ (by positivity)]
    have : 24 * lg * j ≤ ε' * hR := by nlinarith
    nlinarith
  have hLlow : y / 2 ≤ (L : ℝ) := by
    have := Nat.sub_one_lt_floor y
    linarith
  have hLlow' : ε' * hR / (16 * j * lg) ≤ (L : ℝ) := by
    refine le_trans ?_ hLlow
    rw [hy, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 ≤ ε' * hR := by positivity
    nlinarith
  have hLpos : (0 : ℝ) < L := lt_of_lt_of_le (by positivity) hLlow'
  have hLh : L ≤ 2 ^ b := by
    have : (L : ℝ) ≤ hR := by
      refine hLy.trans ?_
      rw [hy, div_le_iff₀ (by positivity)]
      nlinarith
    have h' : (L : ℝ) ≤ ((2 ^ b : ℕ) : ℝ) := by rw [Nat.cast_pow, Nat.cast_ofNat]; exact this
    exact_mod_cast h'
  have hLlog : (L : ℝ) * Real.log (3 * 2 ^ j) ≤ ε * 2 ^ b / 4 := by
    have : (L : ℝ) * Real.log (3 * XR) ≤ ε' * hR / 4 := by
      calc (L : ℝ) * Real.log (3 * XR) ≤ y * Real.log (3 * XR) :=
            mul_le_mul_of_nonneg_right hLy (by linarith)
        _ = ε' * hR / 4 := by rw [hy]; field_simp
    calc (L : ℝ) * Real.log (3 * 2 ^ j) ≤ ε' * hR / 4 := this
      _ ≤ ε * 2 ^ b / 4 := by gcongr
  -- the mean-square hypothesis
  have hX2 : 2 ≤ 2 ^ j := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hXθ : ((2 ^ j : ℕ) : ℝ) ^ θ ≤ ((2 ^ b : ℕ) : ℝ) := by
    push_cast
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast (2 : ℝ) b]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hh2 : (2 ^ b) ^ 2 ≤ 2 ^ j := by
    rw [← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hMS := hC₁ (2 ^ j) (2 ^ b) hX2 hXθ hh2
  set E : ℕ → ℝ := fun n =>
    (Chebyshev.theta ((n + 2 ^ b : ℕ) : ℝ) - Chebyshev.theta (n : ℕ) - ((2 ^ b : ℕ) : ℝ)) ^ 2
    with hE
  have hE0 : ∀ n, 0 ≤ E n := fun n => sq_nonneg _
  -- lower bound for the mean square by the bad blocks
  have hblocks : ∑ M ∈ Ico (2 ^ (j - b)) (2 ^ (j - b + 1)),
      ∑ n ∈ Ico (M * 2 ^ b) (M * 2 ^ b + 2 ^ b), E n
      = ∑ n ∈ Ico (2 ^ j) (2 * 2 ^ j), E n := by
    rw [sum_Ico_blocks E (2 ^ b) _ _ (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _)),
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
                exact window_error_large hM hbj' hLh hn.1 hn.2 hLlog hε
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
  have hupper : ∑ n ∈ Ico (2 ^ j) (2 * 2 ^ j), E n ≤ C₁' * hR * XR * (j * lg) ^ 2 := by
    have hlogX : Real.log ((2 ^ j : ℕ) : ℝ) = j * lg := by push_cast; rw [Real.log_pow]
    have := hMS
    simp only [hE]
    refine this.trans ?_
    rw [hlogX]
    push_cast
    have : 0 ≤ (2 : ℝ) ^ b * 2 ^ j * (j * lg) ^ 2 := by positivity
    calc C₁ * 2 ^ b * 2 ^ j * (j * lg) ^ 2 = C₁ * ((2 : ℝ) ^ b * 2 ^ j * (j * lg) ^ 2) := by ring
      _ ≤ C₁' * ((2 : ℝ) ^ b * 2 ^ j * (j * lg) ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) this
      _ = C₁' * hR * XR * (j * lg) ^ 2 := by rw [hhR, hXR]; ring
  -- combine
  have hcomb := hlower.trans hupper
  set K : ℝ := (#(badBlocks ε j b) : ℝ)
  have hK0 : 0 ≤ K := by positivity
  have hC₁'0 : 0 ≤ C₁' := le_max_right _ _
  have hfac : 0 < ε' * hR / (16 * j * lg) * (ε * hR / 2) ^ 2 := by positivity
  have hK : K * (ε' * hR / (16 * j * lg) * (ε * hR / 2) ^ 2) ≤ C₁' * hR * XR * (j * lg) ^ 2 := by
    refine le_trans ?_ hcomb
    apply mul_le_mul_of_nonneg_left _ hK0
    exact mul_le_mul_of_nonneg_right hLlow' (sq_nonneg _)
  have h4b : (4 : ℝ) ^ b = hR ^ 2 := by rw [hhR, ← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h4b, le_div_iff₀ (by positivity)]
  rw [← le_div_iff₀ hfac] at hK
  calc K * hR ^ 2 ≤ C₁' * hR * XR * (j * lg) ^ 2 /
        (ε' * hR / (16 * j * lg) * (ε * hR / 2) ^ 2) * hR ^ 2 :=
        mul_le_mul_of_nonneg_right hK (sq_nonneg _)
    _ = 64 * C₁' * lg ^ 3 / (ε' * ε ^ 2) * (j : ℝ) ^ 3 * 2 ^ j := by
        rw [hXR]
        field_simp
        ring

end PPF
