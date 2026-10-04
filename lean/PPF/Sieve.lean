import PPF.Interfaces
import PPF.Sieve.Pair

/-!
# The pair sieve

`PairSieve` holds unconditionally (Selberg's upper-bound sieve), with `C = 16416`:
for `t ≥ 2^64` this is `PPF.Sieve.pair_type_bound_large`; for `2 ≤ t < 2^64` the
trivial bound `#(…) ≤ t` suffices since `(log t)² < 64² (log 2)² < 16416`.
-/

namespace PPF

open Finset

theorem pairSieve : PairSieve := by
  refine ⟨16416, ?_⟩
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

end PPF
