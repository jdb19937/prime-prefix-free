import PPF.Conditional
import PPF.Explicit.Defs
import PPF.Explicit.Blocks
import PPF.Explicit.Sieve
import PPF.Explicit.Selberg

/-!
# Explicit bound: the recurrence for `j ≥ J`

`PPF.cond_rec_step` with `c = cE`, `ε = epsE`, `θ = thetaE = 2^{-32}`, `C₄ = C4`, `C₅ = C5`,
`j₁ = J = 2^44`. Its hypotheses: `hbad` from `card_badBlocks_explicit` +
`theta_window_explicit` at `(2^j, 2^b)` (for `j ≥ J`, `θ j ≤ b`: `b ≥ 4096`, `j ≤ 2^32 b`,
so `2^b ≥ (j log 2)²` and `2^b ≥ 800·log(3·2^j)` by natural-number arithmetic);
`hshort` from `short_gap_explicit`.
-/

namespace PPF.Explicit

namespace Rc

open Finset

/-- `2^64 b² ≤ 2^b` for `b ≥ 128`. -/
lemma pow_ge_aux : ∀ b : ℕ, 128 ≤ b → 2 ^ 64 * b ^ 2 ≤ 2 ^ b := by
  intro b hb
  induction b, hb using Nat.le_induction with
  | base =>
    calc 2 ^ 64 * 128 ^ 2 = 2 ^ 78 := by norm_num
      _ ≤ 2 ^ 128 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  | succ n hn ih =>
    have h1 : (n + 1) ^ 2 ≤ 2 * n ^ 2 := by nlinarith
    calc 2 ^ 64 * (n + 1) ^ 2 ≤ 2 ^ 64 * (2 * n ^ 2) := Nat.mul_le_mul_left _ h1
      _ = 2 * (2 ^ 64 * n ^ 2) := by ring
      _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left _ ih
      _ = 2 ^ (n + 1) := by ring

/-- The bad-block hypothesis of `cond_rec_step`, from the explicit inputs. -/
lemma hbad (hRH : RiemannHypothesis) :
    ∀ j b : ℕ, J ≤ j → thetaE * j ≤ b → 2 * b ≤ j →
      (#(badBlocks epsE j b) : ℝ) ≤ C4 * (j : ℝ) ^ 3 * 2 ^ j / 4 ^ b := by
  intro j b hjJ hθb h2b
  have hJ' : (2 : ℕ) ^ 44 ≤ j := hjJ
  norm_num at hJ'
  -- `j ≤ 2^32 b`
  have hθb' : (j : ℝ) ≤ 2 ^ 32 * b := by
    have h := hθb
    unfold thetaE at h
    have h32 : (0 : ℝ) < 2 ^ 32 := by positivity
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ h32] at h
    linarith
  have hjb : j ≤ 2 ^ 32 * b := by exact_mod_cast hθb'
  norm_num at hjb
  have hb4096 : 4096 ≤ b := by omega
  have key : (2 : ℝ) ^ 64 * (b : ℝ) ^ 2 ≤ (2 : ℝ) ^ b := by
    exact_mod_cast pow_ge_aux b (by omega)
  have hj0 : (0 : ℝ) ≤ j := by positivity
  have hb0 : (4096 : ℝ) ≤ b := by exact_mod_cast hb4096
  have hj1 : (1 : ℝ) ≤ j := by
    have : 1 ≤ j := by omega
    exact_mod_cast this
  have hlog2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  -- `(2^32 b)² = 2^64 b²`
  have hsq : ((2 : ℝ) ^ 32 * b) ^ 2 = (2 : ℝ) ^ 64 * (b : ℝ) ^ 2 := by ring
  -- window range: `log² X ≤ h`
  have hlogX : Real.log ((2 ^ j : ℕ) : ℝ) = j * Real.log 2 := by
    push_cast
    rw [Real.log_pow]
  have hA : Real.log ((2 ^ j : ℕ) : ℝ) ^ 2 ≤ ((2 ^ b : ℕ) : ℝ) := by
    rw [hlogX]
    push_cast
    have hjl0 : 0 ≤ (j : ℝ) * Real.log 2 := by positivity
    have hjl : (j : ℝ) * Real.log 2 ≤ j := by nlinarith
    have h1 : ((j : ℝ) * Real.log 2) ^ 2 ≤ (j : ℝ) ^ 2 := by nlinarith
    have h2 : (j : ℝ) ^ 2 ≤ ((2 : ℝ) ^ 32 * b) ^ 2 := by nlinarith
    nlinarith
  -- `h ≤ X`
  have hle : 2 ^ b ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
  -- `100 ≤ X`
  have h100 : 100 ≤ 2 ^ j := by
    calc 100 ≤ 2 ^ 7 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
  -- shift condition: `8 log(3·2^j) ≤ ε 2^b`
  have hL : 8 * Real.log (3 * 2 ^ j) ≤ epsE * 2 ^ b := by
    have hlog3 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      linarith
    have hlog : Real.log (3 * 2 ^ j) = Real.log 3 + j * Real.log 2 := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    have hlj : Real.log (3 * 2 ^ j) ≤ 2 + j := by
      rw [hlog]
      nlinarith
    have hstep : (800 : ℝ) * (2 + j) ≤ 2 ^ b := by
      have h1 : (800 : ℝ) * (2 + j) ≤ 2400 * j := by nlinarith
      have h2 : (2400 : ℝ) * j ≤ 2400 * (2 ^ 32 * b) := by nlinarith
      have h3 : (2400 : ℝ) * (2 ^ 32 * b) ≤ (2 : ℝ) ^ 64 * (b : ℝ) ^ 2 := by nlinarith
      linarith
    unfold epsE
    nlinarith
  have hMS := theta_window_explicit hRH (2 ^ j) (2 ^ b) h100 hA hle
  exact card_badBlocks_explicit (C := CT) (ε := epsE) (j := j) (b := b) (X := 2 ^ j)
    (h := 2 ^ b) rfl rfl (by unfold CT; positivity) (by norm_num [epsE]) (by norm_num [epsE])
    (by omega) h2b hL hMS

end Rc

theorem rec_explicit (hRH : RiemannHypothesis) :
    ∀ j : ℕ, J ≤ j →
      r (j + 1) ≤ r j * (1 - cE / j) + (etaE / j + eE j) * r (j / 3) + gE j := by
  intro j hj
  have hj20 : 20 ≤ j := by
    have : (2 : ℕ) ^ 44 ≤ j := hj
    norm_num at this
    omega
  exact cond_rec_step (c := cE) (ε := epsE) (θ := thetaE) (C₄ := C4) (C₅ := C5) (j₁ := J)
    rfl (by norm_num [epsE]) (by norm_num [epsE]) (by norm_num [thetaE]) (by norm_num [thetaE])
    (by unfold C4 CT epsE; positivity) (by unfold C5; positivity)
    (Rc.hbad hRH) (fun j b d' h1 h2 h3 => short_gap_explicit j b d' h1 h2 h3) j hj hj20

end PPF.Explicit
