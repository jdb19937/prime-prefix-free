import PPF.Bootstrap
import PPF.Explicit.Defs
import PPF.Explicit.Final.Tail

/-!
# Explicit bound: bootstrap with explicit constants and the final numeral

From the recurrence for `j ≥ J` (`r ≤ 1` below `J`, `α = 5/4`,
`α + 4^α·etaE ≤ cE`), `PPF.step_bound`/`PPF.recSeq_bound` give
`i^{5/4} r i ≤ M = (J^{5/4} + V)·exp(4^{5/4}·E)` for all `i`, with
`E ≥ Σ_{j ≥ J} eE j` (`E = 1/1000`), `V ≥ Σ_{j ≥ J} (j+1)^{5/4} gE j` (`V = 1`).
Then `Σ_{m<N} r m ≤ J + M (J^{-5/4} + 4 J^{-1/4}) ≤ 4.5·10^14`
(`J^{1/4} = 2^11`, `J^{5/4} = 2^55`; the true value is ≈ 8.9·10^13).
-/

namespace PPF.Explicit

namespace Fn

open Real Finset

lemma K_eq : ((J : ℕ) : ℝ) ^ (5 / 4 : ℝ) = 2 ^ 55 := by
  rw [J_real, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- `Σ_{k<N} (J+k)^{-5/4} ≤ 4 (J−1)^{-1/4}` by comparison with the integral. -/
lemma sum_rpow_le (N : ℕ) :
    ∑ k ∈ range N, (((J + k : ℕ) : ℝ)) ^ (-(5 / 4) : ℝ)
      ≤ 4 * ((J : ℝ) - 1) ^ (-(1 / 4) : ℝ) := by
  set x₀ : ℝ := (J : ℝ) - 1 with hx₀def
  have hx₀ : 0 < x₀ := by have := J_ge_two; rw [hx₀def]; linarith
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-(5 / 4) : ℝ)) (Set.Icc x₀ (x₀ + N)) :=
    fun x hx y _ hxy => Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le hx₀ hx.1) hxy (by norm_num)
  have hsum := hanti.sum_le_integral
  have hterms : ∀ i ∈ range N, (x₀ + ((i + 1 : ℕ) : ℝ)) ^ (-(5 / 4) : ℝ)
      = (((J + i : ℕ) : ℝ)) ^ (-(5 / 4) : ℝ) := by
    intro i _; congr 1; rw [hx₀def]; push_cast; ring
  rw [sum_congr rfl hterms] at hsum
  have h0 : (0 : ℝ) ∉ Set.uIcc x₀ (x₀ + N) := by
    rw [Set.mem_uIcc]; push Not
    have : (0 : ℝ) ≤ N := N.cast_nonneg
    constructor <;> intro h <;> linarith
  rw [integral_rpow (Or.inr ⟨by norm_num, h0⟩)] at hsum
  have hb : 0 ≤ (x₀ + N) ^ (-(5 / 4) + 1 : ℝ) := by
    apply Real.rpow_nonneg; have : (0 : ℝ) ≤ N := N.cast_nonneg; linarith
  have he : (-(5 / 4) + 1 : ℝ) = -(1 / 4) := by norm_num
  rw [he] at hsum hb
  have : ((x₀ + N) ^ (-(1 / 4) : ℝ) - x₀ ^ (-(1 / 4) : ℝ)) / (-(1 / 4) : ℝ)
      = 4 * x₀ ^ (-(1 / 4) : ℝ) - 4 * (x₀ + N) ^ (-(1 / 4) : ℝ) := by ring
  rw [this] at hsum
  linarith

lemma Jm1_rpow_le : ((J : ℝ) - 1) ^ (-(1 / 4) : ℝ) ≤ 1 / 1024 := by
  have h40 : (2 : ℝ) ^ (40 : ℕ) ≤ (J : ℝ) - 1 := by rw [J_real]; norm_num
  have h := Real.rpow_le_rpow_of_nonpos (by positivity) h40 (by norm_num : (-(1 / 4) : ℝ) ≤ 0)
  refine h.trans (le_of_eq ?_)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num [Real.rpow_neg]

end Fn

open Fn Real Finset

theorem partial_sum_r_le
    (hrec : ∀ j : ℕ, J ≤ j →
      r (j + 1) ≤ r j * (1 - cE / j) + (etaE / j + eE j) * r (j / 3) + gE j) :
    ∀ N : ℕ, ∑ m ∈ Finset.range N, r m ≤ (4.5 : ℝ) * 10 ^ 14 := by
  intro N
  set α : ℝ := 5 / 4 with hα
  set A : ℝ := (4 : ℝ) ^ α with hAdef
  set K : ℝ := ((J : ℕ) : ℝ) ^ α with hKdef
  set e' : ℕ → ℝ := fun i => eE (i + J) with he'
  set v' : ℕ → ℝ := fun i => (((i + J : ℕ) : ℝ) + 1) ^ α * gE (i + J) with hv'
  set B : ℕ → ℝ := PPF.recSeq K A e' v' with hB
  have hα0 : (0 : ℝ) ≤ α := by norm_num [hα]
  have hA0 : 0 ≤ A := by positivity
  have hK0 : 0 ≤ K := by positivity
  have he0 : ∀ i, 0 ≤ e' i := fun i => eE_nonneg _
  have hgE0 : ∀ j, 0 ≤ gE j := fun j => by
    unfold gE; have := cE_pos; have := C4_nonneg; positivity
  have hv0 : ∀ i, 0 ≤ v' i := fun i => mul_nonneg (by positivity) (hgE0 _)
  have hBmono : Monotone B := PPF.recSeq_mono K A e' v' hK0 hA0 he0 hv0
  have hJ12 : 12 ≤ J := by unfold J; norm_num
  have hcond : α + (4 : ℝ) ^ α * etaE ≤ cE := hcondE
  -- every `i ≤ n + J` satisfies `i^{5/4} r i ≤ B n`
  have hmain : ∀ n : ℕ, ∀ i ≤ n + J, (i : ℝ) ^ α * r i ≤ B n := by
    intro n
    induction n with
    | zero =>
      intro i hi
      have hB0 : B 0 = K := rfl
      rw [hB0]
      have hi' : (i : ℝ) ≤ ((J : ℕ) : ℝ) := by exact_mod_cast (by omega : i ≤ J)
      calc (i : ℝ) ^ α * r i ≤ (i : ℝ) ^ α * 1 :=
            mul_le_mul_of_nonneg_left (PPF.r_le_one i) (by positivity)
        _ = (i : ℝ) ^ α := mul_one _
        _ ≤ K := Real.rpow_le_rpow (by positivity) hi' hα0
    | succ n ih =>
      intro i hi
      rcases Nat.lt_or_ge i (n + J + 1) with h | h
      · exact (ih i (by omega)).trans (hBmono (Nat.le_succ n))
      · have hi' : i = (n + J) + 1 := by omega
        subst hi'
        have hm12 : 12 ≤ n + J := hJ12.trans (by omega)
        have hmc : cE ≤ ((n + J : ℕ) : ℝ) := by
          have h2 := cE_le_two
          have : (2 : ℝ) ≤ ((n + J : ℕ) : ℝ) := by
            have := J_ge_two; push_cast; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
          linarith
        have hstep := PPF.step_bound r eE gE cE etaE α hα0 PPF.r_nonneg etaE_nonneg eE_nonneg
          hcond (n + J) hm12 hmc (hrec (n + J) (by omega)) (B n) ih
        have hBs : B (n + 1) = B n * Real.exp (A * e' n) + v' n := rfl
        rw [hBs]
        simp only [he', hv', hAdef]
        push_cast at hstep ⊢
        exact hstep
  -- uniform bound `B n ≤ M`
  set M : ℝ := 3 * (2 ^ 55 + 1) with hM
  have hBM : ∀ n, B n ≤ M := by
    intro n
    refine (PPF.recSeq_bound K A e' v' hA0 he0 hv0 n).trans ?_
    have hv : ∑ i ∈ range n, v' i ≤ 1 := sum_v_le n
    have he : ∑ i ∈ range n, e' i ≤ 1 / 1000 := sum_eE_le n
    have hA : A ≤ 5.66 := four_rpow_le
    have hexp : Real.exp (A * ∑ i ∈ range n, e' i) ≤ 3 := by
      have h1 : A * ∑ i ∈ range n, e' i ≤ 1 := by
        have : A * ∑ i ∈ range n, e' i ≤ 5.66 * (1 / 1000) :=
          mul_le_mul hA he (sum_nonneg fun i _ => he0 i) (by norm_num)
        linarith
      calc Real.exp (A * ∑ i ∈ range n, e' i) ≤ Real.exp 1 := Real.exp_le_exp.mpr h1
        _ ≤ 3 := by have := Real.exp_one_lt_d9; linarith
    have hK : K = 2 ^ 55 := by rw [hKdef, hα]; exact K_eq
    have hS0 : 0 ≤ K + ∑ i ∈ range n, v' i := by
      have := sum_nonneg (fun i (_ : i ∈ range n) => hv0 i); linarith
    calc (K + ∑ i ∈ range n, v' i) * Real.exp (A * ∑ i ∈ range n, e' i)
        ≤ (K + ∑ i ∈ range n, v' i) * 3 := mul_le_mul_of_nonneg_left hexp hS0
      _ ≤ (2 ^ 55 + 1) * 3 := by rw [hK]; gcongr
      _ = M := by rw [hM]; ring
  -- pointwise decay `r m ≤ M m^{-5/4}`
  have hdecay : ∀ m : ℕ, 1 ≤ m → r m ≤ M * ((m : ℝ)) ^ (-(5 / 4) : ℝ) := by
    intro m hm
    have hpos : 0 < (m : ℝ) := by exact_mod_cast hm
    have h := (hmain m m (by omega)).trans (hBM m)
    rw [Real.rpow_neg hpos.le, ← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
    exact h
  -- split the partial sum at `J`
  have hr0 : ∀ m, 0 ≤ r m := PPF.r_nonneg
  calc ∑ m ∈ range N, r m ≤ ∑ m ∈ range (J + N), r m :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega)) (fun i _ _ => hr0 i)
    _ = ∑ m ∈ range J, r m + ∑ k ∈ range N, r (J + k) := sum_range_add _ _ _
    _ ≤ (J : ℝ) + M * (4 * ((J : ℝ) - 1) ^ (-(1 / 4) : ℝ)) := by
        gcongr
        · calc ∑ m ∈ range J, r m ≤ ∑ _m ∈ range J, (1 : ℝ) := sum_le_sum fun m _ => PPF.r_le_one m
            _ = J := by simp
        · calc ∑ k ∈ range N, r (J + k)
              ≤ ∑ k ∈ range N, M * (((J + k : ℕ) : ℝ)) ^ (-(5 / 4) : ℝ) :=
                sum_le_sum fun k _ => hdecay (J + k) (by unfold J; omega)
            _ = M * ∑ k ∈ range N, (((J + k : ℕ) : ℝ)) ^ (-(5 / 4) : ℝ) := by rw [mul_sum]
            _ ≤ M * (4 * ((J : ℝ) - 1) ^ (-(1 / 4) : ℝ)) := by
                gcongr
                exact sum_rpow_le N
    _ ≤ (2 : ℝ) ^ 44 + M * (4 * (1 / 1024)) := by
        rw [J_real]
        have := Jm1_rpow_le
        rw [J_real] at this
        gcongr
    _ ≤ (4.5 : ℝ) * 10 ^ 14 := by rw [hM]; norm_num

theorem tsum_le_of_partial_sum_r (R : ℝ) (h : ∀ N : ℕ, ∑ m ∈ Finset.range N, r m ≤ R) :
    ∑' n : ℕ, (if PrimePrefixFree n then (1 : ℝ) / n else 0) ≤ R := by
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
  refine Real.tsum_le_of_sum_range_le hf0 (fun N => ?_)
  calc ∑ i ∈ Finset.range N, f i ≤ ∑ i ∈ Finset.range (2 ^ N), f i :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr Nat.lt_two_pow_self.le) (fun i _ _ => hf0 i)
    _ ≤ ∑ m ∈ Finset.range N, r m := hpow N
    _ ≤ R := h N

end PPF.Explicit
