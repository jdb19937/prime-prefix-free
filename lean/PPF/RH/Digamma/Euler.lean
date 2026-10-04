import PPF.RH.Defs

/-!
# Euler's limit for `Γ` converges locally uniformly on `Re s > 0`

`GammaSeq s n = ∫_{(0,∞)} wt n x · x^{s−1}` with `0 ≤ wt n x ≤ e^{−x}`, `wt n x → e^{−x}`,
so on a strip `a ≤ Re s ≤ b` the error is at most the `s`-free quantity
`∫ |wt n x − e^{−x}| (x^{a−1} + x^{b−1}) dx → 0` (dominated convergence).
Consequently `ψ(w) = lim (log n − ∑_{j ≤ n} 1/(w+j))` for `Re w > 0`.
-/

namespace PPF.RH.Dg

open Complex Filter Topology MeasureTheory Set

/-- Truncated Euler weight `(1 − x/n)^n · 1_{(0,n]}`. -/
noncomputable def wt (n : ℕ) (x : ℝ) : ℝ :=
  (Ioc 0 (n : ℝ)).indicator (fun x => (1 - x / n) ^ n) x

lemma measurable_wt (n : ℕ) : Measurable (wt n) := by
  unfold wt
  exact (by fun_prop : Measurable (fun x : ℝ => (1 - x / n) ^ n)).indicator measurableSet_Ioc

lemma wt_nonneg (n : ℕ) (x : ℝ) : 0 ≤ wt n x := by
  unfold wt
  by_cases h : x ∈ Ioc 0 (n : ℝ)
  · rw [indicator_of_mem h]
    have hn : (0 : ℝ) < n := lt_of_lt_of_le h.1 h.2
    have : x / n ≤ 1 := (div_le_one hn).mpr h.2
    exact pow_nonneg (by linarith) n
  · rw [indicator_of_notMem h]

lemma wt_le_exp (n : ℕ) {x : ℝ} (_hx : 0 < x) : wt n x ≤ Real.exp (-x) := by
  unfold wt
  by_cases h : x ∈ Ioc 0 (n : ℝ)
  · rw [indicator_of_mem h]; exact Real.one_sub_div_pow_le_exp_neg h.2
  · rw [indicator_of_notMem h]; exact (Real.exp_pos _).le

lemma wt_tendsto {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => wt n x) atTop (𝓝 (Real.exp (-x))) := by
  refine (Real.tendsto_one_add_div_pow_exp (-x)).congr' ?_
  filter_upwards [eventually_ge_atTop ⌈x⌉₊] with n hn
  rw [Nat.ceil_le] at hn
  unfold wt
  rw [indicator_of_mem (show x ∈ Ioc 0 (n : ℝ) from ⟨hx, hn⟩), neg_div, ← sub_eq_add_neg]

lemma gammaSeq_eq_integral {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : n ≠ 0) :
    GammaSeq s n = ∫ x in Ioi (0 : ℝ), ((wt n x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1) := by
  rw [GammaSeq_eq_approx_Gamma_integral hs hn,
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ n)]
  have : ∀ x : ℝ, ((wt n x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1) = (Ioc 0 (n : ℝ)).indicator
      (fun x : ℝ => (((1 - x / n) ^ n : ℝ) : ℂ) * (x : ℂ) ^ (s - 1)) x := by
    intro x
    unfold wt
    by_cases h : x ∈ Ioc 0 (n : ℝ) <;> simp [h]
  simp_rw [this]
  rw [integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self]

/-- `x^{σ−1} ≤ x^{a−1} + x^{b−1}` for `x > 0`, `a ≤ σ ≤ b`. -/
lemma rpow_le_add {x a b σ : ℝ} (hx : 0 < x) (ha : a ≤ σ) (hb : σ ≤ b) :
    x ^ (σ - 1) ≤ x ^ (a - 1) + x ^ (b - 1) := by
  rcases le_total x 1 with h | h
  · have : x ^ (σ - 1) ≤ x ^ (a - 1) :=
      Real.rpow_le_rpow_of_exponent_ge hx h (by linarith)
    linarith [Real.rpow_nonneg hx.le (b - 1)]
  · have : x ^ (σ - 1) ≤ x ^ (b - 1) :=
      Real.rpow_le_rpow_of_exponent_le h (by linarith)
    linarith [Real.rpow_nonneg hx.le (a - 1)]

/-- The `s`-free error of the truncated Euler integral on the strip `a ≤ Re s ≤ b`. -/
noncomputable def err (a b : ℝ) (n : ℕ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), |wt n x - Real.exp (-x)| * (x ^ (a - 1) + x ^ (b - 1))

lemma integrable_dom {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun x : ℝ => Real.exp (-x) * (x ^ (a - 1) + x ^ (b - 1))) (Ioi 0) := by
  have := (Real.GammaIntegral_convergent ha).add (Real.GammaIntegral_convergent hb)
  refine this.congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply]; ring

lemma aesm_errIntegrand (a b : ℝ) (n : ℕ) :
    AEStronglyMeasurable
      (fun x : ℝ => |wt n x - Real.exp (-x)| * (x ^ (a - 1) + x ^ (b - 1)))
      (volume.restrict (Ioi 0)) := by
  have h1 : Measurable (fun x : ℝ => |wt n x - Real.exp (-x)|) :=
    ((measurable_wt n).sub (by fun_prop)).abs
  have h2 : Measurable (fun x : ℝ => x ^ (a - 1) + x ^ (b - 1)) := by fun_prop
  exact (h1.mul h2).aestronglyMeasurable

lemma errIntegrand_le {a b : ℝ} (n : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖|wt n x - Real.exp (-x)| * (x ^ (a - 1) + x ^ (b - 1))‖
      ≤ Real.exp (-x) * (x ^ (a - 1) + x ^ (b - 1)) := by
  have hpos : 0 ≤ x ^ (a - 1) + x ^ (b - 1) :=
    add_nonneg (Real.rpow_nonneg hx.le _) (Real.rpow_nonneg hx.le _)
  rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg hpos]
  gcongr
  have h0 := wt_nonneg n x
  have h1 := wt_le_exp n hx
  rw [abs_le]; constructor <;> linarith [Real.exp_pos (-x)]

lemma integrable_errIntegrand {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    IntegrableOn (fun x : ℝ => |wt n x - Real.exp (-x)| * (x ^ (a - 1) + x ^ (b - 1)))
      (Ioi 0) := by
  refine Integrable.mono' (integrable_dom ha hb) (aesm_errIntegrand a b n) ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  exact Eventually.of_forall fun x hx => errIntegrand_le n hx

lemma err_tendsto {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (err a b) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun (n : ℕ) (x : ℝ) => |wt n x - Real.exp (-x)| * (x ^ (a - 1) + x ^ (b - 1)))
    (f := fun _ => (0 : ℝ))
    (fun x => Real.exp (-x) * (x ^ (a - 1) + x ^ (b - 1)))
    (fun n => aesm_errIntegrand a b n) (integrable_dom ha hb)
    (fun n => by
      rw [ae_restrict_iff' measurableSet_Ioi]
      exact Eventually.of_forall fun x hx => errIntegrand_le n hx)
    (by
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun x hx => ?_
      have h1 : Tendsto (fun n : ℕ => |wt n x - Real.exp (-x)|) atTop (𝓝 0) := by
        have := ((wt_tendsto hx).sub_const (Real.exp (-x))).abs
        simpa using this
      simpa using h1.mul_const (x ^ (a - 1) + x ^ (b - 1)))
  show Tendsto (fun n : ℕ => ∫ x in Ioi (0 : ℝ),
    |wt n x - Real.exp (-x)| * (x ^ (a - 1) + x ^ (b - 1))) atTop (𝓝 0)
  simpa using h

lemma norm_Gamma_sub_gammaSeq_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {s : ℂ}
    (hs1 : a ≤ s.re) (hs2 : s.re ≤ b) {n : ℕ} (hn : n ≠ 0) :
    ‖Gamma s - GammaSeq s n‖ ≤ err a b n := by
  have hs : 0 < s.re := lt_of_lt_of_le ha hs1
  rw [Gamma_eq_integral hs, GammaIntegral, gammaSeq_eq_integral hs hn]
  have hI1 : IntegrableOn (fun x : ℝ => ((-x).exp : ℂ) * (x : ℂ) ^ (s - 1)) (Ioi 0) :=
    GammaIntegral_convergent hs
  have hmeas : AEStronglyMeasurable (fun x : ℝ => ((wt n x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1))
      (volume.restrict (Ioi 0)) := by
    have : Measurable (fun x : ℝ => ((wt n x : ℝ) : ℂ)) :=
      Complex.measurable_ofReal.comp (measurable_wt n)
    exact (this.mul (by fun_prop)).aestronglyMeasurable
  have hI2 : IntegrableOn (fun x : ℝ => ((wt n x : ℝ) : ℂ) * (x : ℂ) ^ (s - 1)) (Ioi 0) := by
    refine Integrable.mono hI1 hmeas ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun x hx => ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real]
    gcongr
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (wt_nonneg n x),
      abs_of_nonneg (Real.exp_pos _).le]
    exact wt_le_exp n hx
  rw [← integral_sub hI1 hI2]
  refine norm_integral_le_of_norm_le (integrable_errIntegrand ha hb n) ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun x hx => ?_
  rw [← sub_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hx, sub_re, one_re,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  gcongr
  exact rpow_le_add hx hs1 hs2

lemma tendstoUniformlyOn_strip {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    TendstoUniformlyOn (fun (n : ℕ) (s : ℂ) => GammaSeq s n) Gamma atTop
      (re ⁻¹' Icc a b) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(err_tendsto ha hb).eventually (gt_mem_nhds hε), eventually_ne_atTop 0]
    with n hn hn0 s hs
  rw [dist_eq_norm]
  exact lt_of_le_of_lt (norm_Gamma_sub_gammaSeq_le ha hb hs.1 hs.2 hn0) hn

lemma tendstoLocallyUniformlyOn_gammaSeq :
    TendstoLocallyUniformlyOn (fun (n : ℕ) (s : ℂ) => GammaSeq s n) Gamma atTop
      {s : ℂ | 0 < s.re} := by
  refine tendstoLocallyUniformlyOn_of_forall_exists_nhds fun x hx => ?_
  have hx' : 0 < x.re := hx
  refine ⟨re ⁻¹' Icc (x.re / 2) (x.re + 1), ?_,
    tendstoUniformlyOn_strip (by linarith) (by linarith)⟩
  apply mem_nhdsWithin_of_mem_nhds
  exact continuous_re.continuousAt.preimage_mem_nhds (Icc_mem_nhds (by linarith) (by linarith))

end PPF.RH.Dg
