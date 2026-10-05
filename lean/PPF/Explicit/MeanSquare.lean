import PPF.RH.MeanSquare
import PPF.Explicit.Zeros
import PPF.Explicit.MeanSquare.Kernel

/-!
# Explicit bound: the bump kernel and the mean square of the zero sum

Explicit versions of K1 (`70(4^α+2) + 175·4^{α+2}`, from `PPF.RH.KZ.norm_integral_bump_cpow_le'`)
and K4 (`4A + 8B ≤ 2·10^14` with `A = 857.5·21676032`, `B = 11620·1105477632`, `X₀ = 2`).
-/

namespace PPF.Explicit.MSx

open Complex PPF.RH PPF.RH.MS PPF.Explicit

theorem mean_square_explicit' (hRH : RiemannHypothesis) :
    ∀ X h : ℝ, 2 ≤ X → 1 ≤ h → h ≤ X →
      ∫ x in X..(2 * X),
          ‖∑ ρ ∈ zetaZeros (X ^ 2),
              (mult ρ : ℂ) * ((((x + h : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ)‖ ^ 2
        ≤ (4 * (max (857.5 : ℝ) 0 * max (21676032 : ℝ) 0)
            + 8 * (max (11620 : ℝ) 0 * max (1105477632 : ℝ) 0)) * h * X * Real.log X ^ 2 := by
  set K₁ : ℝ := 857.5 with hK₁def
  set K₂ : ℝ := 11620 with hK₂def
  set C₃ : ℝ := 21676032 with hC₃def
  set C₄ : ℝ := 1105477632 with hC₄def
  have hK₁ : ∀ X : ℝ, 1 ≤ X → ∀ τ : ℝ,
      ‖∫ u in (X / 2)..(4 * X), ((bump X u : ℝ) : ℂ) * ((u : ℂ) ^ (((-1 : ℝ) : ℂ) + τ * I))‖
        ≤ K₁ * X ^ ((-1 : ℝ) + 1) / (1 + τ ^ 2) := by
    intro X hX τ
    have h := kernel_explicit' (-1) le_rfl X hX τ
    have e : (70 * ((4 : ℝ) ^ (-1 : ℝ) + 2) + 175 * (4 : ℝ) ^ ((-1 : ℝ) + 2)) = K₁ := by
      rw [hK₁def, Real.rpow_neg_one, show ((-1 : ℝ) + 2) = 1 by norm_num, Real.rpow_one]
      norm_num
    rwa [e] at h
  have hK₂ : ∀ X : ℝ, 1 ≤ X → ∀ τ : ℝ,
      ‖∫ u in (X / 2)..(4 * X), ((bump X u : ℝ) : ℂ) * ((u : ℂ) ^ (((1 : ℝ) : ℂ) + τ * I))‖
        ≤ K₂ * X ^ ((1 : ℝ) + 1) / (1 + τ ^ 2) := by
    intro X hX τ
    have h := kernel_explicit' 1 (by norm_num) X hX τ
    have e : (70 * ((4 : ℝ) ^ (1 : ℝ) + 2) + 175 * (4 : ℝ) ^ ((1 : ℝ) + 2)) = K₂ := by
      rw [hK₂def, Real.rpow_one, show ((1 : ℝ) + 2) = ((3 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
      norm_num
    rwa [e] at h
  have hC₃ := low_pairs_explicit hRH
  have hC₄ := high_pairs_explicit hRH
  set A := max K₁ 0 * max C₃ 0 with hA
  set B := max K₂ 0 * max C₄ 0 with hB
  have hA0 : 0 ≤ A := mul_nonneg (le_max_right _ _) (le_max_right _ _)
  have hB0 : 0 ≤ B := mul_nonneg (le_max_right _ _) (le_max_right _ _)
  intro X h hX hh hhX
  have hX0 : 0 < X := by linarith
  set U := max (X / h) 2 with hUdef
  have hU : 2 ≤ U := le_max_right _ _
  have hU0 : 0 < U := by linarith
  set Z := zetaZeros (X ^ 2) with hZ
  set low := Z.filter (fun ρ => ¬ U < |ρ.im|) with hlow
  set high := Z.filter (fun ρ => U < |ρ.im|) with hhigh
  have hre : ∀ ρ ∈ Z, ρ.re = 1 / 2 := fun ρ hρ => re_eq_half_of_mem hRH hρ
  set T : ℂ → ℝ → ℂ := fun ρ x => (mult ρ : ℂ) * ((((x + h : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ)
    with hT
  -- pointwise splitting
  have hsplit : ∀ x : ℝ, ∑ ρ ∈ Z, T ρ x = ∑ ρ ∈ low, T ρ x + ∑ ρ ∈ high, T ρ x := by
    intro x
    rw [add_comm]
    exact (Finset.sum_filter_add_sum_filter_not Z (fun ρ => U < |ρ.im|) (fun ρ => T ρ x)).symm
  have hpt : ∀ x : ℝ, ‖∑ ρ ∈ Z, T ρ x‖ ^ 2
      ≤ 2 * ‖∑ ρ ∈ low, T ρ x‖ ^ 2 + 2 * ‖∑ ρ ∈ high, T ρ x‖ ^ 2 := by
    intro x
    rw [hsplit x]
    have := norm_add_le (∑ ρ ∈ low, T ρ x) (∑ ρ ∈ high, T ρ x)
    nlinarith [norm_nonneg (∑ ρ ∈ low, T ρ x + ∑ ρ ∈ high, T ρ x),
      norm_nonneg (∑ ρ ∈ low, T ρ x), norm_nonneg (∑ ρ ∈ high, T ρ x),
      sq_nonneg (‖∑ ρ ∈ low, T ρ x‖ - ‖∑ ρ ∈ high, T ρ x‖)]
  have hhh : (0 : ℝ) ≤ h := by linarith
  have hcont : ∀ W : Finset ℂ, IntervalIntegrable (fun x : ℝ => ‖∑ ρ ∈ W, T ρ x‖ ^ 2)
      MeasureTheory.volume X (2 * X) := fun W =>
    intervalIntegrable_of_continuousOn_Ioi
      ((continuousOn_window_sum W (fun ρ => (mult ρ : ℂ)) hhh).norm.pow 2) hX0 (by linarith)
  have hint : ∫ x in X..2 * X, ‖∑ ρ ∈ Z, T ρ x‖ ^ 2
      ≤ 2 * (∫ x in X..2 * X, ‖∑ ρ ∈ low, T ρ x‖ ^ 2)
        + 2 * ∫ x in X..2 * X, ‖∑ ρ ∈ high, T ρ x‖ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add ((hcont low).const_mul 2) ((hcont high).const_mul 2)]
    exact intervalIntegral.integral_mono_on (by linarith) (hcont Z)
      (((hcont low).const_mul 2).add ((hcont high).const_mul 2)) (fun x _ => hpt x)
  have hlowB := low_bound low (fun ρ => (mult ρ : ℂ))
    (fun ρ hρ => hre ρ (Finset.mem_filter.mp hρ).1) hX0 hhh hhX
  have hhighB := high_bound high (fun ρ => (mult ρ : ℂ)) hX0 hhh hhX
  -- the low quadratic form
  have hlowsub : low ⊆ zetaZeros U := by
    intro ρ hρ
    obtain ⟨hρZ, hρU⟩ := Finset.mem_filter.mp hρ
    obtain ⟨h1, h2, _, h4⟩ := (mem_zetaZeros hRH).mp hρZ
    exact (mem_zetaZeros hRH).mpr ⟨h1, h2, not_lt.mp hρU, h4⟩
  have hQlow : ∫ u in (X / 2)..(4 * X),
      bump X u * ‖∑ ρ ∈ low, (mult ρ : ℂ) * (u : ℂ) ^ (ρ - 1)‖ ^ 2
      ≤ A * (U * Real.log U ^ 2) := by
    have h1 := integral_weight_norm_sq_le low (fun ρ => (mult ρ : ℂ)) (fun ρ => ρ - 1) (-1)
      (by
        intro ρ hρ
        rw [Complex.sub_re, hre ρ (Finset.mem_filter.mp hρ).1, Complex.one_re]; norm_num)
      (by linarith : (0 : ℝ) < X / 2) (by linarith : X / 2 ≤ 4 * X)
      (bump_continuous X).continuousOn
      (fun τ => max K₁ 0 / (1 + τ ^ 2))
      (by
        intro τ
        have := hK₁ X (by linarith) τ
        simp only [show ((-1 : ℝ) + 1) = 0 by norm_num, Real.rpow_zero, mul_one] at this
        refine this.trans ?_
        exact div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
    refine h1.trans ?_
    have hsum : ∑ ρ ∈ low, ∑ ρ' ∈ low, ‖(mult ρ : ℂ)‖ * ‖(mult ρ' : ℂ)‖
          * (max K₁ 0 / (1 + ((ρ - 1).im - (ρ' - 1).im) ^ 2))
        = max K₁ 0 * ∑ ρ ∈ low, ∑ ρ' ∈ low,
            ((mult ρ : ℝ) * mult ρ') / (1 + (ρ.im - ρ'.im) ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ρ' _ => ?_
      simp only [Complex.norm_natCast, Complex.sub_im, Complex.one_im, sub_zero]
      ring
    rw [hsum, hA, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
    have hnn : ∀ ρ ρ' : ℂ, 0 ≤ ((mult ρ : ℝ) * mult ρ') / (1 + (ρ.im - ρ'.im) ^ 2) :=
      fun ρ ρ' => by positivity
    calc ∑ ρ ∈ low, ∑ ρ' ∈ low, ((mult ρ : ℝ) * mult ρ') / (1 + (ρ.im - ρ'.im) ^ 2)
        ≤ ∑ ρ ∈ zetaZeros U, ∑ ρ' ∈ zetaZeros U,
            ((mult ρ : ℝ) * mult ρ') / (1 + (ρ.im - ρ'.im) ^ 2) := by
          refine (Finset.sum_le_sum fun ρ _ =>
            Finset.sum_le_sum_of_subset_of_nonneg hlowsub (fun ρ' _ _ => hnn ρ ρ')).trans ?_
          exact Finset.sum_le_sum_of_subset_of_nonneg hlowsub
            (fun ρ _ _ => Finset.sum_nonneg fun ρ' _ => hnn ρ ρ')
      _ ≤ C₃ * U * Real.log U ^ 2 := hC₃ U hU
      _ ≤ max C₃ 0 * (U * Real.log U ^ 2) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  -- the high quadratic form
  have hQhigh : ∫ u in (X / 2)..(4 * X),
      bump X u * ‖∑ ρ ∈ high, (mult ρ : ℂ) / ρ * (u : ℂ) ^ ρ‖ ^ 2
      ≤ B * X ^ 2 * (Real.log U ^ 2 / U) := by
    have h1 := integral_weight_norm_sq_le high (fun ρ => (mult ρ : ℂ) / ρ) (fun ρ => ρ) 1
      (by
        intro ρ hρ
        show ρ.re = 1 / 2
        exact hre ρ (Finset.mem_filter.mp hρ).1)
      (by linarith : (0 : ℝ) < X / 2) (by linarith : X / 2 ≤ 4 * X)
      (bump_continuous X).continuousOn
      (fun τ => max K₂ 0 * X ^ 2 / (1 + τ ^ 2))
      (by
        intro τ
        have := hK₂ X (by linarith) τ
        simp only [show ((1 : ℝ) + 1) = 2 by norm_num, Real.rpow_two] at this
        refine this.trans ?_
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg X)) (by positivity))
    refine h1.trans ?_
    have hsum : ∑ ρ ∈ high, ∑ ρ' ∈ high, ‖(mult ρ : ℂ) / ρ‖ * ‖(mult ρ' : ℂ) / ρ'‖
          * (max K₂ 0 * X ^ 2 / (1 + (ρ.im - ρ'.im) ^ 2))
        = max K₂ 0 * X ^ 2 * ∑ ρ ∈ high, ∑ ρ' ∈ high,
            ((mult ρ : ℝ) * mult ρ') / (‖ρ‖ * ‖ρ'‖ * (1 + (ρ.im - ρ'.im) ^ 2)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ρ' _ => ?_
      simp only [norm_div, Complex.norm_natCast]
      simp only [div_eq_mul_inv, mul_inv]
      ring
    rw [hsum, hB]
    have hle := hC₄ U (X ^ 2) hU
    have hX2 : 0 ≤ max K₂ 0 * X ^ 2 := mul_nonneg (le_max_right _ _) (sq_nonneg _)
    calc max K₂ 0 * X ^ 2 * ∑ ρ ∈ high, ∑ ρ' ∈ high,
            ((mult ρ : ℝ) * mult ρ') / (‖ρ‖ * ‖ρ'‖ * (1 + (ρ.im - ρ'.im) ^ 2))
        ≤ max K₂ 0 * X ^ 2 * (C₄ * Real.log U ^ 2 / U) :=
          mul_le_mul_of_nonneg_left hle hX2
      _ ≤ max K₂ 0 * X ^ 2 * (max C₄ 0 * (Real.log U ^ 2 / U)) := by
          apply mul_le_mul_of_nonneg_left _ hX2
          rw [mul_div_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ = max K₂ 0 * max C₄ 0 * X ^ 2 * (Real.log U ^ 2 / U) := by ring
  -- assembly
  have hfin := final_arith hA0 hB0 hX (hh) hhX
  calc ∫ x in X..2 * X, ‖∑ ρ ∈ Z, T ρ x‖ ^ 2
      ≤ 2 * (∫ x in X..2 * X, ‖∑ ρ ∈ low, T ρ x‖ ^ 2)
        + 2 * ∫ x in X..2 * X, ‖∑ ρ ∈ high, T ρ x‖ ^ 2 := hint
    _ ≤ 2 * (h * (h * (A * (U * Real.log U ^ 2))))
        + 2 * (4 * (B * X ^ 2 * (Real.log U ^ 2 / U))) := by
      have e1 : ∫ x in X..2 * X, ‖∑ ρ ∈ low, T ρ x‖ ^ 2
          ≤ h * (h * (A * (U * Real.log U ^ 2))) := by
        refine hlowB.trans ?_
        apply mul_le_mul_of_nonneg_left _ hhh
        exact mul_le_mul_of_nonneg_left hQlow hhh
      have e2 : ∫ x in X..2 * X, ‖∑ ρ ∈ high, T ρ x‖ ^ 2
          ≤ 4 * (B * X ^ 2 * (Real.log U ^ 2 / U)) := by
        refine hhighB.trans ?_
        exact mul_le_mul_of_nonneg_left hQhigh (by norm_num)
      linarith
    _ ≤ (4 * A + 8 * B) * h * X * Real.log X ^ 2 := hfin

end PPF.Explicit.MSx

namespace PPF.Explicit

open Complex PPF.RH

theorem kernel_explicit (α : ℝ) (hα : -1 ≤ α) :
    ∀ X : ℝ, 1 ≤ X → ∀ τ : ℝ,
      ‖∫ u in (X / 2)..(4 * X), ((bump X u : ℝ) : ℂ) * ((u : ℂ) ^ ((α : ℂ) + τ * I))‖
        ≤ (70 * ((4 : ℝ) ^ α + 2) + 175 * (4 : ℝ) ^ (α + 2)) * X ^ (α + 1) / (1 + τ ^ 2) :=
  MSx.kernel_explicit' α hα

theorem mean_square_explicit (hRH : RiemannHypothesis) :
    ∀ X h : ℝ, 2 ≤ X → 1 ≤ h → h ≤ X →
      ∫ x in X..(2 * X),
          ‖∑ ρ ∈ zetaZeros (X ^ 2),
              (mult ρ : ℂ) * ((((x + h : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ)‖ ^ 2
        ≤ 2 * 10 ^ 14 * h * X * Real.log X ^ 2 := by
  intro X h hX hh hhX
  refine (MSx.mean_square_explicit' hRH X h hX hh hhX).trans ?_
  have hc : (4 * (max (857.5 : ℝ) 0 * max (21676032 : ℝ) 0)
      + 8 * (max (11620 : ℝ) 0 * max (1105477632 : ℝ) 0)) ≤ 2 * 10 ^ 14 := by
    rw [max_eq_left (by norm_num), max_eq_left (by norm_num), max_eq_left (by norm_num),
      max_eq_left (by norm_num)]
    norm_num
  have hnn : 0 ≤ h * X * Real.log X ^ 2 := by
    have : 0 ≤ h := by linarith
    have : 0 ≤ X := by linarith
    positivity
  calc (4 * (max (857.5 : ℝ) 0 * max (21676032 : ℝ) 0)
        + 8 * (max (11620 : ℝ) 0 * max (1105477632 : ℝ) 0)) * h * X * Real.log X ^ 2
      = (4 * (max (857.5 : ℝ) 0 * max (21676032 : ℝ) 0)
        + 8 * (max (11620 : ℝ) 0 * max (1105477632 : ℝ) 0)) * (h * X * Real.log X ^ 2) := by ring
    _ ≤ 2 * 10 ^ 14 * (h * X * Real.log X ^ 2) := mul_le_mul_of_nonneg_right hc hnn
    _ = 2 * 10 ^ 14 * h * X * Real.log X ^ 2 := by ring

end PPF.Explicit
