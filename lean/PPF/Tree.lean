import PPF.Interfaces

/-!
# The binary tree of prime-prefix-free numbers

Level `m` is `[2^m, 2^{m+1})`. `S m` is the set of prime-prefix-free numbers at
level `m`, `P m` its odd primes, and `r m = #S m / 2^m` the surviving mass.

* `primePrefixFree_two_mul_add` (L1): `n ↦ 2n + e` keeps the property iff `n` has it
  and is not an odd prime.
* `primePrefixFree_div_pow` (L2): the property passes to prefixes.
* `card_S_succ`, `r_succ`, `r_antitone` (L3): the level recursion.
* `summable_of_summable_r` (L4): summability of `r` gives the main summability.
* `count_ineq` (L5): the counting inequality behind the level recurrence.
-/

namespace PPF

open Finset

/-- `n` is an odd prime. -/
def OddPrime (n : ℕ) : Prop := n.Prime ∧ n ≠ 2

instance : DecidablePred OddPrime := fun n => inferInstanceAs (Decidable (n.Prime ∧ n ≠ 2))

/-- Prefixes `⌊n / 2^k⌋` with `k > n` vanish, so the defining quantifier is bounded. -/
theorem primePrefixFree_iff_bounded (n : ℕ) :
    PrimePrefixFree n ↔ ∀ k ∈ Finset.Icc 1 n, ¬ OddPrime (n / 2 ^ k) := by
  constructor
  · intro h k hk
    exact h k (Finset.mem_Icc.mp hk).1
  · intro h k hk
    by_cases hkn : k ≤ n
    · exact h k (Finset.mem_Icc.mpr ⟨hk, hkn⟩)
    · have hlt : n < 2 ^ k :=
        lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [Nat.div_eq_of_lt hlt]
      simp [Nat.not_prime_zero]

instance : DecidablePred PrimePrefixFree :=
  fun n => decidable_of_iff _ (primePrefixFree_iff_bounded n).symm

/-- Level `m`: the interval `[2^m, 2^{m+1})`. -/
def level (m : ℕ) : Finset ℕ := Finset.Ico (2 ^ m) (2 ^ (m + 1))

/-- Prime-prefix-free numbers at level `m`. -/
def S (m : ℕ) : Finset ℕ := (level m).filter PrimePrefixFree

/-- Odd primes among them. -/
def P (m : ℕ) : Finset ℕ := (S m).filter OddPrime

/-- Surviving mass at level `m`. -/
noncomputable def r (m : ℕ) : ℝ := (#(S m) : ℝ) / 2 ^ m

/-- Descendants of `M` lying `b` levels down: `[M 2^b, (M+1) 2^b)`. -/
def block (M b : ℕ) : Finset ℕ := Finset.Ico (M * 2 ^ b) ((M + 1) * 2 ^ b)

/-- Number of primes in a finite set. -/
def primeCount (s : Finset ℕ) : ℕ := #(s.filter Nat.Prime)

theorem mem_level {m n : ℕ} : n ∈ level m ↔ 2 ^ m ≤ n ∧ n < 2 ^ (m + 1) := Finset.mem_Ico

theorem mem_S {m n : ℕ} : n ∈ S m ↔ n ∈ level m ∧ PrimePrefixFree n := Finset.mem_filter

theorem mem_P {m n : ℕ} : n ∈ P m ↔ n ∈ S m ∧ OddPrime n := Finset.mem_filter

theorem div_pow_div_pow (n a c : ℕ) : n / 2 ^ a / 2 ^ c = n / 2 ^ (a + c) := by
  rw [Nat.div_div_eq_div_mul, ← pow_add]

theorem two_mul_add_div_two {n e : ℕ} (he : e < 2) : (2 * n + e) / 2 = n := by omega

theorem two_mul_add_div_pow_succ {n e : ℕ} (he : e < 2) (k : ℕ) :
    (2 * n + e) / 2 ^ (k + 1) = n / 2 ^ k := by
  rw [pow_succ', ← Nat.div_div_eq_div_mul, two_mul_add_div_two he]

/-- L1. -/
theorem primePrefixFree_two_mul_add (n e : ℕ) (he : e < 2) :
    PrimePrefixFree (2 * n + e) ↔ PrimePrefixFree n ∧ ¬ OddPrime n := by
  constructor
  · intro h
    refine ⟨fun k hk => ?_, ?_⟩
    · have := h (k + 1) (by omega)
      rwa [two_mul_add_div_pow_succ he] at this
    · have := h 1 le_rfl
      rw [pow_one, two_mul_add_div_two he] at this
      exact this
  · rintro ⟨h1, h2⟩ k hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [two_mul_add_div_pow_succ he]
    rcases Nat.eq_zero_or_pos k' with h0 | hpos
    · subst h0
      simpa [OddPrime] using h2
    · exact h1 k' hpos

/-- L2. -/
theorem primePrefixFree_div_pow {n : ℕ} (h : PrimePrefixFree n) (d : ℕ) :
    PrimePrefixFree (n / 2 ^ d) := by
  intro k hk
  rw [div_pow_div_pow]
  exact h (d + k) (by omega)

/-- Prefixes of a level-`m` number lie at the expected level. -/
theorem div_pow_mem_level {m n b : ℕ} (hn : n ∈ level m) (hb : b ≤ m) :
    n / 2 ^ b ∈ level (m - b) := by
  rw [mem_level] at hn ⊢
  have hpos : 0 < 2 ^ b := by positivity
  constructor
  · rw [Nat.le_div_iff_mul_le hpos, ← pow_add, Nat.sub_add_cancel hb]
    exact hn.1
  · rw [Nat.div_lt_iff_lt_mul hpos, ← pow_add, show m - b + 1 + b = m + 1 by omega]
    exact hn.2

/-- L3, counting form. -/
theorem card_S_succ (m : ℕ) : #(S (m + 1)) = 2 * (#(S m) - #(P m)) := by
  set A := (S m).filter (fun n => ¬ OddPrime n) with hA
  have hsplit : #(P m) + #A = #(S m) := card_filter_add_card_filter_not (s := S m) OddPrime
  have hAcard : #A = #(S m) - #(P m) := by omega
  have hp1 : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
  have hp2 : 2 ^ (m + 1 + 1) = 4 * 2 ^ m := by ring
  have hS : S (m + 1) = A.image (fun n => 2 * n) ∪ A.image (fun n => 2 * n + 1) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_image, hA, Finset.mem_filter, S, level,
      Finset.mem_Ico]
    constructor
    · rintro ⟨⟨hx1, hx2⟩, hx⟩
      have hx' := hx
      rw [show x = 2 * (x / 2) + x % 2 by omega,
        primePrefixFree_two_mul_add _ _ (Nat.mod_lt _ (by norm_num))] at hx'
      rcases Nat.mod_two_eq_zero_or_one x with h0 | h1
      · left
        exact ⟨x / 2, ⟨⟨⟨by omega, by omega⟩, hx'.1⟩, hx'.2⟩, by omega⟩
      · right
        exact ⟨x / 2, ⟨⟨⟨by omega, by omega⟩, hx'.1⟩, hx'.2⟩, by omega⟩
    · rintro (⟨n, ⟨⟨⟨hn1, hn2⟩, hn⟩, hno⟩, rfl⟩ | ⟨n, ⟨⟨⟨hn1, hn2⟩, hn⟩, hno⟩, rfl⟩)
      · refine ⟨⟨by omega, by omega⟩, ?_⟩
        have := (primePrefixFree_two_mul_add n 0 (by norm_num)).mpr ⟨hn, hno⟩
        simpa using this
      · exact ⟨⟨by omega, by omega⟩, (primePrefixFree_two_mul_add n 1 (by norm_num)).mpr ⟨hn, hno⟩⟩
  rw [hS, Finset.card_union_of_disjoint, Finset.card_image_of_injective,
    Finset.card_image_of_injective, hAcard]
  · ring
  · intro a b h; simp only at h; omega
  · intro a b h; simp only at h; omega
  · rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_image] at hx1 hx2
    obtain ⟨a, _, rfl⟩ := hx1
    obtain ⟨b, _, hb⟩ := hx2
    omega

theorem card_P_le_card_S (m : ℕ) : #(P m) ≤ #(S m) :=
  Finset.card_le_card (Finset.filter_subset _ _)

theorem card_S_le (m : ℕ) : #(S m) ≤ 2 ^ m := by
  calc #(S m) ≤ #(level m) := Finset.card_le_card (Finset.filter_subset _ _)
    _ = 2 ^ m := by
      rw [level, Nat.card_Ico, pow_succ]
      omega

/-- L3, mass form. -/
theorem r_succ (m : ℕ) : r (m + 1) = r m - (#(P m) : ℝ) / 2 ^ m := by
  unfold r
  rw [card_S_succ, Nat.cast_mul, Nat.cast_sub (card_P_le_card_S m), pow_succ]
  field_simp
  ring

theorem r_nonneg (m : ℕ) : 0 ≤ r m := by
  unfold r
  positivity

theorem r_le_one (m : ℕ) : r m ≤ 1 := by
  unfold r
  rw [div_le_one (by positivity)]
  exact_mod_cast card_S_le m

theorem r_antitone : Antitone r := by
  apply antitone_nat_of_succ_le
  intro m
  rw [r_succ]
  have : 0 ≤ (#(P m) : ℝ) / 2 ^ m := by positivity
  linarith

/-- L4. -/
theorem summable_of_summable_r (h : Summable r) :
    Summable (fun n : ℕ => if PrimePrefixFree n then (1 : ℝ) / n else 0) := by
  set f : ℕ → ℝ := fun n => if PrimePrefixFree n then (1 : ℝ) / n else 0 with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n => by
    simp only [hf]
    split_ifs <;> positivity
  have hlevel : ∀ m, ∑ i ∈ level m, f i ≤ r m := by
    intro m
    have hsum : ∑ i ∈ level m, f i = ∑ i ∈ S m, (1 : ℝ) / i := by
      rw [S, Finset.sum_filter]
    rw [hsum, r]
    calc ∑ i ∈ S m, (1 : ℝ) / i ≤ ∑ _i ∈ S m, (1 : ℝ) / 2 ^ m := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' := (mem_level.mp (mem_S.mp hi).1).1
          exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hi')
      _ = (#(S m) : ℝ) / 2 ^ m := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
  have hpow : ∀ N, ∑ i ∈ Finset.range (2 ^ N), f i ≤ ∑ m ∈ Finset.range N, r m := by
    intro N
    induction N with
    | zero => simp [hf]
    | succ N ih =>
      rw [Finset.sum_range_succ, ← Finset.sum_range_add_sum_Ico _
        (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ N))]
      have hI : Finset.Ico (2 ^ N) (2 ^ (N + 1)) = level N := rfl
      rw [hI]
      linarith [hlevel N]
  refine summable_of_sum_range_le hf0 (c := ∑' m, r m) (fun N => ?_)
  calc ∑ i ∈ Finset.range N, f i ≤ ∑ i ∈ Finset.range (2 ^ N), f i :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr Nat.lt_two_pow_self.le) (fun i _ _ => hf0 i)
    _ ≤ ∑ m ∈ Finset.range N, r m := hpow N
    _ ≤ ∑' m, r m := h.sum_le_tsum _ (fun i _ => r_nonneg i)

/-- Membership in a block is membership in the fibre of `n ↦ n / 2^b`. -/
theorem mem_block_iff (M b n : ℕ) : n ∈ block M b ↔ n / 2 ^ b = M := by
  have hpos : 0 < 2 ^ b := by positivity
  rw [block, Finset.mem_Ico]
  constructor
  · rintro ⟨h1, h2⟩
    apply le_antisymm
    · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hpos).mpr h2)
    · exact (Nat.le_div_iff_mul_le hpos).mpr h1
  · rintro rfl
    exact ⟨Nat.div_mul_le_self n _, (Nat.div_lt_iff_lt_mul hpos).mp (Nat.lt_succ_self _)⟩

/-- Blocks below a level-`(j - d)` node lie at level `j`. -/
theorem block_subset_level {N d j : ℕ} (hN : N ∈ level (j - d)) (hdj : d ≤ j) :
    block N d ⊆ level j := by
  intro q hq
  rw [block, Finset.mem_Ico] at hq
  rw [mem_level] at hN ⊢
  have e1 : 2 ^ (j - d) * 2 ^ d = 2 ^ j := by rw [← pow_add, Nat.sub_add_cancel hdj]
  have e2 : 2 ^ (j - d + 1) * 2 ^ d = 2 ^ (j + 1) := by
    rw [← pow_add, show j - d + 1 + d = j + 1 by omega]
  constructor
  · calc 2 ^ j = 2 ^ (j - d) * 2 ^ d := e1.symm
      _ ≤ N * 2 ^ d := Nat.mul_le_mul_right _ hN.1
      _ ≤ q := hq.1
  · calc q < (N + 1) * 2 ^ d := hq.2
      _ ≤ 2 ^ (j - d + 1) * 2 ^ d := Nat.mul_le_mul_right _ hN.2
      _ = 2 ^ (j + 1) := e2

-- `hd1` is part of the frozen interface; the proof does not need it.
set_option linter.unusedVariables false in
/-- L5, the counting inequality. A prime `q` at level `j` whose ancestor `d`
levels up is prime-prefix-free either lies in `P j`, or has a highest odd-prime
ancestor `p ∈ P (j - b)` with `1 ≤ b ≤ d`. -/
theorem count_ineq (j d : ℕ) (hj : 2 ≤ j) (hd1 : 1 ≤ d) (hdj : d ≤ j) :
    ∑ N ∈ S (j - d), primeCount (block N d)
      ≤ #(P j) + ∑ b ∈ Finset.Icc 1 d, ∑ p ∈ P (j - b), primeCount (block p b) := by
  set U := (S (j - d)).biUnion (fun N => (block N d).filter Nat.Prime) with hU
  set V := (Finset.Icc 1 d).biUnion
    (fun b => (P (j - b)).biUnion (fun p => (block p b).filter Nat.Prime)) with hV
  have hLHS : ∑ N ∈ S (j - d), primeCount (block N d) = #U := by
    rw [hU, Finset.card_biUnion]
    · rfl
    · intro x _ y _ hxy
      rw [Function.onFun, Finset.disjoint_left]
      intro q hqx hqy
      rw [Finset.mem_filter, mem_block_iff] at hqx hqy
      exact hxy (hqx.1.symm.trans hqy.1)
  have hV' : #V ≤ ∑ b ∈ Finset.Icc 1 d, ∑ p ∈ P (j - b), primeCount (block p b) :=
    Finset.card_biUnion_le.trans (Finset.sum_le_sum fun b _ => Finset.card_biUnion_le)
  have hsub : U ⊆ P j ∪ V := by
    intro q hq
    obtain ⟨N, hN, hqN⟩ := Finset.mem_biUnion.mp hq
    rw [Finset.mem_filter] at hqN
    obtain ⟨hqblock, hqprime⟩ := hqN
    obtain ⟨hNlev, hNppf⟩ := mem_S.mp hN
    have hqdiv : q / 2 ^ d = N := (mem_block_iff _ _ _).mp hqblock
    have hqlev : q ∈ level j := block_subset_level hNlev hdj hqblock
    have hqodd : OddPrime q := by
      refine ⟨hqprime, ?_⟩
      have h4 : 2 ^ 2 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
      have := (mem_level.mp hqlev).1
      omega
    -- odd-prime prefixes of `q` lie within `d` levels
    have key : ∀ k, d < k → ¬ OddPrime (q / 2 ^ k) := by
      intro k hk
      have : q / 2 ^ k = N / 2 ^ (k - d) := by
        rw [← hqdiv, div_pow_div_pow, show d + (k - d) = k by omega]
      rw [this]
      exact hNppf (k - d) (by omega)
    by_cases hq' : PrimePrefixFree q
    · exact Finset.mem_union_left _ (mem_P.mpr ⟨mem_S.mpr ⟨hqlev, hq'⟩, hqodd⟩)
    · apply Finset.mem_union_right
      have hex : ∃ k, 1 ≤ k ∧ OddPrime (q / 2 ^ k) := by
        unfold PrimePrefixFree at hq'
        push Not at hq'
        obtain ⟨k, hk, h⟩ := hq'
        exact ⟨k, hk, h⟩
      obtain ⟨k, hk1, hkp⟩ := hex
      set K := (Finset.Icc 1 d).filter (fun k => OddPrime (q / 2 ^ k)) with hK
      have hkd : k ≤ d := by
        by_contra hcon
        exact key k (by omega) hkp
      have hKne : K.Nonempty := ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hk1, hkd⟩, hkp⟩⟩
      have hbK : K.max' hKne ∈ K := K.max'_mem hKne
      have hmax : ∀ k ∈ K, k ≤ K.max' hKne := fun k hk => K.le_max' k hk
      obtain ⟨hbIcc, hbp⟩ := Finset.mem_filter.mp hbK
      obtain ⟨hb1, hbd⟩ := Finset.mem_Icc.mp hbIcc
      have hpPPF : PrimePrefixFree (q / 2 ^ K.max' hKne) := by
        intro k' hk' hodd'
        rw [div_pow_div_pow] at hodd'
        by_cases hbk : K.max' hKne + k' ≤ d
        · have hmem : K.max' hKne + k' ∈ K :=
            Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hbk⟩, hodd'⟩
          have := hmax _ hmem
          omega
        · exact key (K.max' hKne + k') (by omega) hodd'
      have hplev : q / 2 ^ K.max' hKne ∈ level (j - K.max' hKne) :=
        div_pow_mem_level hqlev (by omega)
      refine Finset.mem_biUnion.mpr ⟨K.max' hKne, Finset.mem_Icc.mpr ⟨hb1, hbd⟩, ?_⟩
      refine Finset.mem_biUnion.mpr ⟨q / 2 ^ K.max' hKne, mem_P.mpr ⟨mem_S.mpr ⟨hplev, hpPPF⟩, hbp⟩, ?_⟩
      exact Finset.mem_filter.mpr ⟨(mem_block_iff _ _ _).mpr rfl, hqprime⟩
  calc ∑ N ∈ S (j - d), primeCount (block N d) = #U := hLHS
    _ ≤ #(P j ∪ V) := Finset.card_le_card hsub
    _ ≤ #(P j) + #V := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add_left hV' _

end PPF
