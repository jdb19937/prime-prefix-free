import PPF.Sieve
import PPF.ShortGaps
import PPF.Explicit.Defs

/-!
# Explicit bound: pair sieve, totient mean value, short gaps

Explicit versions of `PPF.pairSieve` (`16416`), `PPF.sum_sq_div_totient_sq_le_linear`
(`e³`) and `PPF.short_gap_le` (`C5 = 4·16416·e³/log² 2`).
-/

namespace PPF.Explicit

open Finset

theorem pairSieve_explicit :
    ∀ Y H a t : ℕ, 2 ≤ H → 1 ≤ a → 1 ≤ t → Nat.Coprime a t →
      (#((Finset.Ico Y (Y + H)).filter (fun n => n.Prime ∧ (a * n + t).Prime)) : ℝ)
        ≤ 16416 * ((a * t : ℕ) / (Nat.totient (a * t) : ℝ)) ^ 2 * H / Real.log H ^ 2 := by
  intro Y H a t hH ha ht _
  by_cases hbig : 2 ^ 64 ≤ H
  · exact PPF.Sieve.pair_type_bound_large Y H a t ha ht hbig
  · replace hbig := not_le.mp hbig
    have hH2 : (2 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
    have hlogpos : 0 < Real.log H := Real.log_pos (by linarith)
    have hlog_le : Real.log H ≤ 64 * Real.log 2 := by
      have h1 : Real.log H ≤ Real.log ((2 : ℝ) ^ 64) :=
        Real.log_le_log (by linarith) (by exact_mod_cast hbig.le)
      rwa [Real.log_pow, Nat.cast_ofNat] at h1
    have hlog2 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9
      linarith
    have hlogsq : (Real.log H) ^ 2 ≤ 16416 := by
      have h0 : Real.log H ≤ 64 := by nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
      nlinarith
    have hφ : (1 : ℝ) ≤ (((a * t : ℕ) : ℝ) / (Nat.totient (a * t) : ℝ)) ^ 2 := by
      have hpos : 0 < a * t := Nat.mul_pos (by omega) (by omega)
      have hφpos : (0 : ℝ) < (Nat.totient (a * t) : ℝ) := by
        exact_mod_cast Nat.totient_pos.mpr hpos
      have h1 : (Nat.totient (a * t) : ℝ) ≤ ((a * t : ℕ) : ℝ) := by
        exact_mod_cast Nat.totient_le (a * t)
      have h2 : (1 : ℝ) ≤ ((a * t : ℕ) : ℝ) / (Nat.totient (a * t) : ℝ) :=
        (one_le_div hφpos).mpr h1
      nlinarith
    have hcard : (#((Finset.Ico Y (Y + H)).filter (fun n => n.Prime ∧ (a * n + t).Prime)) : ℝ)
        ≤ H := by
      have : #((Finset.Ico Y (Y + H)).filter (fun n => n.Prime ∧ (a * n + t).Prime)) ≤ H := by
        calc _ ≤ #(Finset.Ico Y (Y + H)) := Finset.card_filter_le _ _
          _ = H := by rw [Nat.card_Ico]; omega
      exact_mod_cast this
    have hHnn : (0 : ℝ) ≤ H := by positivity
    calc (#((Finset.Ico Y (Y + H)).filter (fun n => n.Prime ∧ (a * n + t).Prime)) : ℝ)
        ≤ H := hcard
      _ = H * (Real.log H) ^ 2 / (Real.log H) ^ 2 := by field_simp
      _ ≤ 16416 * (((a * t : ℕ) : ℝ) / (Nat.totient (a * t) : ℝ)) ^ 2 * H
            / (Real.log H) ^ 2 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          nlinarith [mul_le_mul_of_nonneg_left hlogsq hHnn, mul_le_mul_of_nonneg_left hφ hHnn]

theorem totient_sq_explicit :
    ∀ T : ℕ, ∑ t ∈ Finset.Icc 1 T, ((t : ℝ) / Nat.totient t) ^ 2 ≤ Real.exp 3 * T := by
  intro T
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

theorem short_gap_explicit :
    ∀ j b d' : ℕ, 1 ≤ b → b ≤ d' → b + d' ≤ j →
      ((∑ p ∈ P (j - b), primeCount (block p b) : ℕ) : ℝ)
        ≤ C5 * #(S (j - b - d')) * 2 ^ (b + d') / (d' : ℝ) ^ 2 := by
  have hC₂ := pairSieve_explicit
  have hC₁ := totient_sq_explicit
  set C₂ : ℝ := 16416 with hC₂def
  set C₁ : ℝ := Real.exp 3 with hC₁def
  set C₂' := max C₂ 0 with hC₂'
  have hC₂'0 : 0 ≤ C₂' := le_max_right _ _
  have hC₁0 : 0 ≤ C₁ := (Real.exp_pos 3).le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC5 : C5 = 4 * C₂' * C₁ / Real.log 2 ^ 2 := by
    rw [C5, hC₂', hC₂def, hC₁def, max_eq_left (by norm_num)]
  rw [hC5]
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

end PPF.Explicit
