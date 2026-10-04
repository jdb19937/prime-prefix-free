import PPF.Tree
import PPF.Vendor.TotientSumSq

/-!
# Short gaps (L8)

Primes `q` at level `j` whose ancestor `b` levels up lies in `P (j − b)`, for small
`b`. Writing `q = 2^b n + t` (`t < 2^b` odd), `n` runs over the blocks of
`S (j − b − d')`, and `PairSieve` bounds each `(n, 2^b n + t)` count; the factor
`(2t/φ t)²` is averaged over `t` by `sum_sq_div_totient_sq_le_linear`.
-/

namespace PPF

open Finset

/-! ### Mean value of `(t/φ t)²` -/

/-- Divisor-sum swap: `∑_{m ≤ T} ∑_{d ∣ m} f d = ∑_{d ≤ T} ⌊T/d⌋ f d`. -/
lemma sg_sum_Icc_sum_divisors_eq (f : ℕ → ℝ) (T : ℕ) :
    ∑ m ∈ Icc 1 T, ∑ d ∈ m.divisors, f d = ∑ d ∈ Icc 1 T, ((T / d : ℕ) : ℝ) * f d := by
  have hswap : ∑ m ∈ Icc 1 T, ∑ d ∈ m.divisors, f d
      = ∑ d ∈ Icc 1 T, ∑ _k ∈ Icc 1 (T / d), f d := by
    rw [Finset.sum_sigma', Finset.sum_sigma']
    refine Finset.sum_nbij' (fun x => ⟨x.2, x.1 / x.2⟩) (fun y => ⟨y.1 * y.2, y.1⟩)
      ?_ ?_ ?_ ?_ ?_
    · rintro ⟨m, d⟩ hx
      simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hx ⊢
      obtain ⟨⟨hm1, hmT⟩, hdvd, hm0⟩ := hx
      have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by omega)
      have hdm : d ≤ m := Nat.le_of_dvd (by omega) hdvd
      exact ⟨⟨hd0, hdm.trans hmT⟩, (Nat.one_le_div_iff hd0).mpr hdm, Nat.div_le_div_right hmT⟩
    · rintro ⟨d, k⟩ hy
      simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hy ⊢
      obtain ⟨⟨hd1, hdT⟩, hk1, hkT⟩ := hy
      have hdk : d * k ≤ T := by
        have h := (Nat.le_div_iff_mul_le (by omega : 0 < d)).mp hkT
        rw [mul_comm]
        exact h
      exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), hdk⟩,
        dvd_mul_right d k, Nat.mul_ne_zero (by omega) (by omega)⟩
    · rintro ⟨m, d⟩ hx
      simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hx
      obtain ⟨⟨hm1, hmT⟩, hdvd, hm0⟩ := hx
      simp only [Nat.mul_div_cancel' hdvd]
    · rintro ⟨d, k⟩ hy
      simp only [Finset.mem_sigma, Finset.mem_Icc] at hy
      obtain ⟨⟨hd1, hdT⟩, hk1, hkT⟩ := hy
      simp only [Nat.mul_div_cancel_left _ (by omega : 0 < d)]
    · rintro ⟨m, d⟩ _
      rfl
  rw [hswap]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]

/-- Mean value of `(t/φ t)²`. -/
theorem sum_sq_div_totient_sq_le_linear :
    ∃ C : ℝ, ∀ T : ℕ, ∑ t ∈ Finset.Icc 1 T, ((t : ℝ) / Nat.totient t) ^ 2 ≤ C * T := by
  refine ⟨Real.exp 3, fun T => ?_⟩
  calc ∑ t ∈ Icc 1 T, ((t : ℝ) / Nat.totient t) ^ 2
      ≤ ∑ t ∈ Icc 1 T, ∑ d ∈ t.divisors, Carmichael.sqf3 d := by
        refine Finset.sum_le_sum fun t ht => Carmichael.sq_le_sum_divisors_sqf3 ?_
        have := (mem_Icc.mp ht).1
        omega
    _ = ∑ d ∈ Icc 1 T, ((T / d : ℕ) : ℝ) * Carmichael.sqf3 d := sg_sum_Icc_sum_divisors_eq _ T
    _ ≤ ∑ d ∈ Icc 1 T, (T : ℝ) * (Carmichael.sqf3 d / d) := by
        refine Finset.sum_le_sum fun d hd => ?_
        have hd1 : 1 ≤ d := (mem_Icc.mp hd).1
        have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
        rw [mul_div_assoc', le_div_iff₀ hd0]
        have h1 : ((T / d : ℕ) : ℝ) * d ≤ T := by exact_mod_cast Nat.div_mul_le_self T d
        nlinarith [Carmichael.sqf3_nonneg d]
    _ = T * ∑ d ∈ Icc 1 T, Carmichael.sqf3 d / d := by rw [Finset.mul_sum]
    _ ≤ T * Real.exp 3 :=
        mul_le_mul_of_nonneg_left (Carmichael.sum_sqf3_div_le T) (by positivity)
    _ = Real.exp 3 * T := mul_comm _ _

/-! ### Block bookkeeping -/

lemma sg_div_pow_mem_level {p m d : ℕ} (hp : p ∈ level m) (hd : d ≤ m) :
    p / 2 ^ d ∈ level (m - d) := by
  unfold level at hp ⊢
  rw [Finset.mem_Ico] at hp ⊢
  have hpos : 0 < 2 ^ d := by positivity
  have e1 : 2 ^ (m - d) * 2 ^ d = 2 ^ m := by rw [← pow_add, Nat.sub_add_cancel hd]
  have e2 : 2 ^ (m - d + 1) * 2 ^ d = 2 ^ (m + 1) := by
    rw [← pow_add]
    congr 1
    omega
  constructor
  · rw [Nat.le_div_iff_mul_le hpos, e1]
    exact hp.1
  · rw [Nat.div_lt_iff_lt_mul hpos, e2]
    exact hp.2

lemma sg_div_pow_mem_S {p m d : ℕ} (hp : p ∈ S m) (hd : d ≤ m) : p / 2 ^ d ∈ S (m - d) := by
  unfold S at hp ⊢
  rw [Finset.mem_filter] at hp ⊢
  exact ⟨sg_div_pow_mem_level hp.1 hd, primePrefixFree_div_pow hp.2 d⟩

lemma sg_block_eq_Ico (N d : ℕ) : block N d = Ico (N * 2 ^ d) (N * 2 ^ d + 2 ^ d) := by
  unfold block
  rw [add_mul, one_mul]

lemma sg_pairwiseDisjoint_block (s : Finset ℕ) (d : ℕ) :
    (s : Set ℕ).PairwiseDisjoint (fun N => block N d) := by
  intro N _ N' _ hNN'
  refine Finset.disjoint_left.mpr fun n hn hn' => hNN' ?_
  rw [mem_block_iff] at hn hn'
  rw [← hn, ← hn']

/-- `primeCount` of a block as a sum over offsets. -/
lemma sg_primeCount_block_eq_sum (p b : ℕ) :
    primeCount (block p b) = ∑ t ∈ range (2 ^ b), if (2 ^ b * p + t).Prime then 1 else 0 := by
  unfold primeCount
  rw [sg_block_eq_Ico, Finset.card_filter, Finset.sum_Ico_eq_sum_range]
  rw [Nat.add_sub_cancel_left]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [mul_comm]

/-- `(2^b t)/φ(2^b t) = 2 t/φ t` for odd `t` and `b ≥ 1`. -/
lemma sg_two_pow_mul_div_totient {b t : ℕ} (hb : 1 ≤ b) (ht : Odd t) :
    ((2 ^ b * t : ℕ) : ℝ) / (Nat.totient (2 ^ b * t) : ℝ) = 2 * ((t : ℝ) / Nat.totient t) := by
  have hcop : Nat.Coprime (2 ^ b) t := (Nat.coprime_two_left.mpr ht).pow_left b
  have hφ : Nat.totient (2 ^ b * t) = 2 ^ (b - 1) * Nat.totient t := by
    rw [Nat.totient_mul hcop]
    obtain ⟨k, rfl⟩ : ∃ k, b = k + 1 := ⟨b - 1, by omega⟩
    rw [Nat.totient_prime_pow_succ Nat.prime_two]
    simp
  have ht0 : 0 < t := ht.pos
  have hφt : (0 : ℝ) < Nat.totient t := by exact_mod_cast Nat.totient_pos.mpr ht0
  have h2b : (2 : ℝ) ^ b = 2 * 2 ^ (b - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hφ]
  push_cast
  rw [h2b]
  field_simp

/-- L8. -/
theorem short_gap_le (h2 : PairSieve) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j b d' : ℕ, 1 ≤ b → b ≤ d' → b + d' ≤ j →
      ((∑ p ∈ P (j - b), primeCount (block p b) : ℕ) : ℝ)
        ≤ C * #(S (j - b - d')) * 2 ^ (b + d') / (d' : ℝ) ^ 2 := by
  obtain ⟨C₂, hC₂⟩ := h2
  obtain ⟨C₁, hC₁⟩ := sum_sq_div_totient_sq_le_linear
  set C₂' := max C₂ 0 with hC₂'
  have hC₂'0 : 0 ≤ C₂' := le_max_right _ _
  have hC₁0 : 0 ≤ C₁ := by
    have h := hC₁ 1
    simp at h
    linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨4 * C₂' * C₁ / Real.log 2 ^ 2, by positivity, ?_⟩
  intro j b d' hb hbd hbdj
  set m := j - b - d' with hm
  set U := (S m).biUnion (fun N => block N d') with hU
  -- every `p ∈ P (j − b)` lies in a block of `S m`
  have hPU : P (j - b) ⊆ U := by
    intro p hp
    have hpS : p ∈ S (j - b) := (Finset.mem_filter.mp hp).1
    have hdm : d' ≤ j - b := by omega
    have hmem := sg_div_pow_mem_S hpS hdm
    rw [show j - b - d' = m from rfl] at hmem
    exact Finset.mem_biUnion.mpr ⟨p / 2 ^ d', hmem, (mem_block_iff _ _ _).mpr rfl⟩
  -- the counting function
  let f : ℕ → ℕ → ℕ := fun t n => if n.Prime ∧ (2 ^ b * n + t).Prime then 1 else 0
  -- Step 1: rewrite the left side and enlarge the range of `p`.
  have step1 : ∑ p ∈ P (j - b), primeCount (block p b)
      ≤ ∑ t ∈ range (2 ^ b), ∑ N ∈ S m,
          #((block N d').filter (fun n => n.Prime ∧ (2 ^ b * n + t).Prime)) := by
    calc ∑ p ∈ P (j - b), primeCount (block p b)
        = ∑ p ∈ P (j - b), ∑ t ∈ range (2 ^ b), f t p := by
          refine Finset.sum_congr rfl fun p hp => ?_
          rw [sg_primeCount_block_eq_sum]
          have hpp : p.Prime := (Finset.mem_filter.mp hp).2.1
          refine Finset.sum_congr rfl fun t _ => ?_
          simp only [f, hpp, true_and]
      _ = ∑ t ∈ range (2 ^ b), ∑ p ∈ P (j - b), f t p := Finset.sum_comm
      _ ≤ ∑ t ∈ range (2 ^ b), ∑ n ∈ U, f t n := by
          refine Finset.sum_le_sum fun t _ => ?_
          exact Finset.sum_le_sum_of_subset_of_nonneg hPU fun _ _ _ => Nat.zero_le _
      _ = ∑ t ∈ range (2 ^ b), ∑ N ∈ S m, ∑ n ∈ block N d', f t n := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [hU, Finset.sum_biUnion (sg_pairwiseDisjoint_block _ _)]
      _ = ∑ t ∈ range (2 ^ b), ∑ N ∈ S m,
            #((block N d').filter (fun n => n.Prime ∧ (2 ^ b * n + t).Prime)) := by
          refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun N _ => ?_
          rw [Finset.card_filter]
  -- Step 2: bound each count.
  have hd'1 : 1 ≤ d' := le_trans hb hbd
  have hH : 2 ≤ 2 ^ d' := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ d' := Nat.pow_le_pow_right (by norm_num) hd'1
  set K : ℝ := C₂' * 4 * 2 ^ d' / ((d' : ℝ) * Real.log 2) ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have hlogH : Real.log ((2 ^ d' : ℕ) : ℝ) = d' * Real.log 2 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  have step2 : ∀ t ∈ range (2 ^ b), ∀ N ∈ S m,
      (#((block N d').filter (fun n => n.Prime ∧ (2 ^ b * n + t).Prime)) : ℝ)
        ≤ K * ((t : ℝ) / Nat.totient t) ^ 2 := by
    intro t _ N _
    rcases Nat.even_or_odd t with hte | hto
    · -- even offsets give no primes
      have hempty : (block N d').filter (fun n => n.Prime ∧ (2 ^ b * n + t).Prime) = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr fun n _ ⟨hnp, hqp⟩ => ?_
        have heven : Even (2 ^ b * n + t) := by
          refine Even.add ?_ hte
          exact (Nat.even_pow.mpr ⟨even_two, by omega⟩).mul_right n
        rcases hqp.eq_two_or_odd' with h2 | hodd
        · have hn2 := hnp.two_le
          have hb2 : 2 ≤ 2 ^ b := by
            calc 2 = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
          have : 4 ≤ 2 ^ b * n := by nlinarith
          omega
        · exact (Nat.not_even_iff_odd.mpr hodd) heven
      rw [hempty, Finset.card_empty, Nat.cast_zero]
      positivity
    · have ht1 : 1 ≤ t := hto.pos
      have hcop : Nat.Coprime (2 ^ b) t := (Nat.coprime_two_left.mpr hto).pow_left b
      have ha : 1 ≤ 2 ^ b := Nat.one_le_two_pow
      have h := hC₂ (N * 2 ^ d') (2 ^ d') (2 ^ b) t hH ha ht1 hcop
      rw [← sg_block_eq_Ico] at h
      rw [sg_two_pow_mul_div_totient hb hto, hlogH] at h
      refine h.trans ?_
      have hX : 0 ≤ (2 * ((t : ℝ) / Nat.totient t)) ^ 2 * ((2 ^ d' : ℕ) : ℝ)
          / ((d' : ℝ) * Real.log 2) ^ 2 := by positivity
      calc C₂ * (2 * ((t : ℝ) / Nat.totient t)) ^ 2 * ((2 ^ d' : ℕ) : ℝ)
            / ((d' : ℝ) * Real.log 2) ^ 2
          = C₂ * ((2 * ((t : ℝ) / Nat.totient t)) ^ 2 * ((2 ^ d' : ℕ) : ℝ)
            / ((d' : ℝ) * Real.log 2) ^ 2) := by ring
        _ ≤ C₂' * ((2 * ((t : ℝ) / Nat.totient t)) ^ 2 * ((2 ^ d' : ℕ) : ℝ)
            / ((d' : ℝ) * Real.log 2) ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hX
        _ = K * ((t : ℝ) / Nat.totient t) ^ 2 := by
          rw [hK]
          push_cast
          ring
  -- Step 3: sum over `t`.
  have step3 : ∑ t ∈ range (2 ^ b), (((t : ℕ) : ℝ) / Nat.totient t) ^ 2 ≤ C₁ * 2 ^ b := by
    have hsub : range (2 ^ b) ⊆ insert 0 (Icc (1 : ℕ) (2 ^ b)) := by
      intro t ht
      rw [Finset.mem_insert, Finset.mem_Icc]
      rw [Finset.mem_range] at ht
      omega
    calc ∑ t ∈ range (2 ^ b), (((t : ℕ) : ℝ) / Nat.totient t) ^ 2
        ≤ ∑ t ∈ insert 0 (Icc (1 : ℕ) (2 ^ b)), (((t : ℕ) : ℝ) / Nat.totient t) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
      _ = ∑ t ∈ Icc (1 : ℕ) (2 ^ b), (((t : ℕ) : ℝ) / Nat.totient t) ^ 2 := by
          rw [Finset.sum_insert (by simp)]
          simp
      _ ≤ C₁ * ((2 ^ b : ℕ) : ℝ) := hC₁ _
      _ = C₁ * 2 ^ b := by push_cast; ring
  -- Assemble.
  calc ((∑ p ∈ P (j - b), primeCount (block p b) : ℕ) : ℝ)
      ≤ ((∑ t ∈ range (2 ^ b), ∑ N ∈ S m,
          #((block N d').filter (fun n => n.Prime ∧ (2 ^ b * n + t).Prime)) : ℕ) : ℝ) := by
        exact_mod_cast step1
    _ = ∑ t ∈ range (2 ^ b), ∑ N ∈ S m,
          (#((block N d').filter (fun n => n.Prime ∧ (2 ^ b * n + t).Prime)) : ℝ) := by
        push_cast
        rfl
    _ ≤ ∑ t ∈ range (2 ^ b), ∑ _N ∈ S m, K * ((t : ℝ) / Nat.totient t) ^ 2 :=
        Finset.sum_le_sum fun t ht => Finset.sum_le_sum fun N hN => step2 t ht N hN
    _ = #(S m) * K * ∑ t ∈ range (2 ^ b), ((t : ℝ) / Nat.totient t) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ #(S m) * K * (C₁ * 2 ^ b) :=
        mul_le_mul_of_nonneg_left step3 (by positivity)
    _ = 4 * C₂' * C₁ / Real.log 2 ^ 2 * #(S m) * 2 ^ (b + d') / (d' : ℝ) ^ 2 := by
        have hd' : (d' : ℝ) ≠ 0 := by
          have : (1 : ℝ) ≤ d' := by exact_mod_cast hd'1
          linarith
        rw [hK, pow_add]
        field_simp

end PPF
