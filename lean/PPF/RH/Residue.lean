import PPF.RH.ZeroCount
import PPF.Vendor.PerronKernel

/-!
# RT: the rectangle residue theorem for `−ζ′/ζ(s) · y^s/s` under RH

Rectangle `[−1/2, c] × [−t, t]`, `c > 1`, no zeros on the horizontal edges.
Under RH its only poles are `s = 1` (residue `y`), `s = 0` (residue `−ζ′/ζ(0)`)
and the zeros `ρ ∈ zetaZeros t` on `Re = 1/2` (residue `−mult ρ · y^ρ/ρ`).

Route: subtract the principal parts `r_p/(s − p)`; the remainder `G` agrees, on a
punctured neighbourhood of each pole, with a function analytic at the pole, so the
function `Gt` (equal to `G` off the poles and to its limit at the poles) is analytic on
the closed rectangle and `Carmichael.rectInt_eq_zero` kills it, while
`Carmichael.rectInt_cauchy` (constant numerator) gives `2πi·r_p` for each principal
part. Local expansions: `ζ = (s − ρ)^m g` with `g(ρ) ≠ 0` (Mathlib analytic order
API); `ζ(s) = k(s)/(s − 1)` with `k` entire, `k(1) = 1`.
-/

namespace PPF.RH

open Complex Filter Topology Set
open scoped Real Interval

namespace Res

/-- `y^s/s`. -/
noncomputable def u (y : ℝ) (s : ℂ) : ℂ := (y : ℂ) ^ s / s

/-- The integrand `−ζ′/ζ(s) · y^s/s`. -/
noncomputable def F (y : ℝ) (s : ℂ) : ℂ := -(deriv riemannZeta s / riemannZeta s) * u y s

/-- Residue at `0`. -/
noncomputable def r0 : ℂ := -(deriv riemannZeta 0 / riemannZeta 0)

/-- The sum of the principal parts. -/
noncomputable def PP (y t : ℝ) (s : ℂ) : ℂ :=
  (y : ℂ) / (s - 1) + r0 / s + ∑ ρ ∈ zetaZeros t, (-(mult ρ : ℂ) * u y ρ) / (s - ρ)

/-- The integrand minus its principal parts. -/
noncomputable def G (y t : ℝ) (s : ℂ) : ℂ := F y s - PP y t s

/-- The poles. -/
noncomputable def poles (t : ℝ) : Finset ℂ := insert 1 (insert 0 (zetaZeros t))

open Classical in
/-- `G` with its limits filled in at the poles. -/
noncomputable def Gt (y t : ℝ) (s : ℂ) : ℂ :=
  if s ∈ poles t then limUnder (𝓝[≠] s) (G y t) else G y t s

/-! ### Analyticity toolkit -/

lemma differentiable_cpow {y : ℝ} (hy : 0 < y) : Differentiable ℂ (fun z : ℂ => (y : ℂ) ^ z) :=
  fun _ => differentiableAt_id.const_cpow (Or.inl (by exact_mod_cast hy.ne'))

lemma analyticAt_cpow {y : ℝ} (hy : 0 < y) (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => (y : ℂ) ^ z) s :=
  (differentiable_cpow hy).analyticAt s

lemma analyticAt_u {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : s ≠ 0) : AnalyticAt ℂ (u y) s := by
  show AnalyticAt ℂ (fun z : ℂ => (y : ℂ) ^ z / z) s
  exact (analyticAt_cpow hy s).div analyticAt_id hs

lemma analyticAt_dslope {f : ℂ → ℂ} {p : ℂ} (hf : AnalyticAt ℂ f p) :
    AnalyticAt ℂ (dslope f p) p := by
  obtain ⟨U, hU, hUa⟩ := hf.eventually_analyticAt.exists_mem
  have hd : DifferentiableOn ℂ f U := fun z hz => (hUa z hz).differentiableAt.differentiableWithinAt
  have hd' : DifferentiableOn ℂ (dslope f p) U := (Complex.differentiableOn_dslope hU).mpr hd
  exact hd'.analyticAt hU

lemma analyticAt_const_div_sub (a : ℂ) {p q : ℂ} (h : p ≠ q) :
    AnalyticAt ℂ (fun s : ℂ => a / (s - q)) p :=
  analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr h)

lemma analyticAt_zeta {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s := by
  have hopen : IsOpen {z : ℂ | z ≠ 1} := isOpen_compl_singleton
  have hd : DifferentiableOn ℂ riemannZeta {z : ℂ | z ≠ 1} := fun z hz =>
    (differentiableAt_riemannZeta hz).differentiableWithinAt
  exact hd.analyticAt (hopen.mem_nhds hs)

lemma analyticAt_F {y : ℝ} (hy : 0 < y) {s : ℂ} (hs1 : s ≠ 1) (hs0 : s ≠ 0)
    (hζ : riemannZeta s ≠ 0) : AnalyticAt ℂ (F y) s := by
  have h1 := analyticAt_zeta hs1
  show AnalyticAt ℂ (fun z => -(deriv riemannZeta z / riemannZeta z) * u y z) s
  exact ((h1.deriv.div h1 hζ).neg).mul (analyticAt_u hy hs0)

lemma analyticAt_sum_div {S : Finset ℂ} (a : ℂ → ℂ) {p : ℂ} (hp : p ∉ S) :
    AnalyticAt ℂ (fun s : ℂ => ∑ ρ ∈ S, a ρ / (s - ρ)) p :=
  S.analyticAt_fun_sum (f := fun ρ s => a ρ / (s - ρ))
    (fun ρ hρ => analyticAt_const_div_sub (a ρ) (fun h => hp (by rw [h]; exact hρ)))

/-! ### Local expansions at the three kinds of poles -/

/-- The entire function `E(s) = ζ(s) − 1/((s−1) Γℝ(s))`. -/
lemma differentiable_E :
    Differentiable ℂ (fun s : ℂ => riemannZeta s - 1 / (s - 1) / Gammaℝ s) := by
  intro s
  rcases eq_or_ne s 1 with rfl | hs
  · exact HurwitzZeta.differentiableAt_hurwitzZetaEven_sub_one_div 0
  · have h1 : DifferentiableAt ℂ (fun s : ℂ => 1 / (s - 1)) s :=
      (differentiableAt_const _).div (differentiableAt_id.sub_const 1) (sub_ne_zero.mpr hs)
    have h2 : DifferentiableAt ℂ (fun s : ℂ => 1 / (s - 1) / Gammaℝ s) s := by
      have : (fun s : ℂ => 1 / (s - 1) / Gammaℝ s) = fun s => 1 / (s - 1) * (Gammaℝ s)⁻¹ := by
        funext z; rw [div_eq_mul_inv]
      rw [this]
      exact h1.mul (differentiable_Gammaℝ_inv s)
    exact (differentiableAt_riemannZeta hs).sub h2

/-- `k(s) = (s−1) ζ(s)`, made entire. -/
noncomputable def k (s : ℂ) : ℂ :=
  (s - 1) * (riemannZeta s - 1 / (s - 1) / Gammaℝ s) + (Gammaℝ s)⁻¹

lemma differentiable_k : Differentiable ℂ k :=
  ((differentiable_id.sub_const 1).mul differentiable_E).add differentiable_Gammaℝ_inv

lemma k_one : k 1 = 1 := by
  simp [k, Gammaℝ_one]

lemma zeta_eq_k_div {s : ℂ} (hs : s ≠ 1) : riemannZeta s = k s / (s - 1) := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have h : (s - 1) * (1 / (s - 1) / Gammaℝ s) = (Gammaℝ s)⁻¹ := by
    rw [one_div, div_eq_mul_inv, mul_inv_cancel_left₀ hs1]
  rw [eq_div_iff hs1, k, mul_sub (s - 1) (riemannZeta s), h]
  ring

lemma local_one {y : ℝ} (hy : 0 < y) :
    ∃ B : ℂ → ℂ, AnalyticAt ℂ B 1 ∧
      (fun s => F y s - (y : ℂ) / (s - 1)) =ᶠ[𝓝[≠] 1] B := by
  have hk := differentiable_k
  have hka : AnalyticAt ℂ k 1 := hk.analyticAt 1
  refine ⟨fun s => dslope (u y) 1 s - deriv k s / k s * u y s, ?_, ?_⟩
  · exact (analyticAt_dslope (analyticAt_u hy one_ne_zero)).sub
      ((hka.deriv.div hka (by rw [k_one]; exact one_ne_zero)).mul
        (analyticAt_u hy one_ne_zero))
  · have hkne : ∀ᶠ s in 𝓝 (1 : ℂ), k s ≠ 0 :=
      hka.continuousAt.eventually_ne (by rw [k_one]; exact one_ne_zero)
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hkne] with s hs hks
    have hs : s ≠ 1 := hs
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
    have hev : riemannZeta =ᶠ[𝓝 s] fun z => k z / (z - 1) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hs] with z hz
      exact zeta_eq_k_div hz
    have hD : HasDerivAt (fun z => k z / (z - 1)) ((deriv k s * (s - 1) - k s * 1) / (s - 1) ^ 2) s :=
      (hk s).hasDerivAt.div ((hasDerivAt_id s).sub_const 1) hs1
    have hderiv : deriv riemannZeta s = (deriv k s * (s - 1) - k s * 1) / (s - 1) ^ 2 := by
      rw [hev.deriv_eq]; exact hD.deriv
    have hu1 : u y 1 = (y : ℂ) := by simp [u]
    simp only [F]
    rw [dslope_of_ne _ hs, slope_def_field, hu1, hderiv, zeta_eq_k_div hs]
    field_simp
    ring

lemma zeta_zero_ne : riemannZeta 0 ≠ 0 := by
  rw [riemannZeta_zero]; norm_num

lemma local_zero {y : ℝ} (hy : 0 < y) :
    ∃ B : ℂ → ℂ, AnalyticAt ℂ B 0 ∧ (fun s => F y s - r0 / s) =ᶠ[𝓝[≠] 0] B := by
  have hζ := analyticAt_zeta (zero_ne_one : (0 : ℂ) ≠ 1)
  set v : ℂ → ℂ := fun s => -(deriv riemannZeta s / riemannZeta s) * (y : ℂ) ^ s with hv
  have hva : AnalyticAt ℂ v 0 :=
    ((hζ.deriv.div hζ zeta_zero_ne).neg).mul (analyticAt_cpow hy 0)
  refine ⟨dslope v 0, analyticAt_dslope hva, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs : s ≠ 0 := hs
  have hv0 : v 0 = r0 := by simp [hv, r0]
  rw [dslope_of_ne _ hs, slope_def_field, hv0]
  simp only [F, u, hv, r0, sub_zero]
  field_simp

lemma local_rho {y : ℝ} (hy : 0 < y) {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ ≠ 1) :
    ∃ B : ℂ → ℂ, AnalyticAt ℂ B ρ ∧
      (fun s => F y s - (-(mult ρ : ℂ) * u y ρ) / (s - ρ)) =ᶠ[𝓝[≠] ρ] B := by
  have hρne : ρ ≠ 0 := fun h => by rw [h, zero_re] at hρ0; exact lt_irrefl 0 hρ0
  have hζ := analyticAt_zeta hρ1
  have hne := Carmichael.analyticOrderAt_zeta_ne_top hρ0 hρ1
  obtain ⟨g, hg, hgρ, hfac⟩ := hζ.analyticOrderAt_ne_top.mp hne
  set m : ℕ := analyticOrderNatAt riemannZeta ρ with hm
  have hmult : (mult ρ : ℂ) = m := rfl
  refine ⟨fun s => -(m : ℂ) * dslope (u y) ρ s - deriv g s / g s * u y s, ?_, ?_⟩
  · exact ((analyticAt_const).mul (analyticAt_dslope (analyticAt_u hy hρne))).sub
      ((hg.deriv.div hg hgρ).mul (analyticAt_u hy hρne))
  · have h1 := hfac.eventuallyEq_nhds
    have h2 := hg.eventually_analyticAt
    have h3 := hg.continuousAt.eventually_ne hgρ
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds h1, nhdsWithin_le_nhds h2,
      nhdsWithin_le_nhds h3] with s hs hfs hgs hgs0
    have hs : s ≠ ρ := hs
    have hd : s - ρ ≠ 0 := sub_ne_zero.mpr hs
    have hD : HasDerivAt (fun z => (z - ρ) ^ m * g z)
        ((m : ℂ) * (s - ρ) ^ (m - 1) * 1 * g s + (s - ρ) ^ m * deriv g s) s :=
      (((hasDerivAt_id s).sub_const ρ).pow m).mul hgs.differentiableAt.hasDerivAt
    have hfs' : riemannZeta =ᶠ[𝓝 s] fun z => (z - ρ) ^ m * g z := by
      simpa only [smul_eq_mul] using hfs
    have hderiv : deriv riemannZeta s
        = (m : ℂ) * (s - ρ) ^ (m - 1) * 1 * g s + (s - ρ) ^ m * deriv g s := by
      rw [hfs'.deriv_eq]; exact hD.deriv
    have hval : riemannZeta s = (s - ρ) ^ m * g s := hfs'.self_of_nhds
    have hlog : deriv riemannZeta s / riemannZeta s = (m : ℂ) / (s - ρ) + deriv g s / g s := by
      rw [hderiv, hval]
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · rw [h0]; simp
      · obtain ⟨n, hn⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
        rw [hn, Nat.add_sub_cancel]
        field_simp
        push_cast
        ring
    simp only [F]
    rw [hlog, dslope_of_ne _ hs, slope_def_field, hmult]
    field_simp
    ring

/-! ### Global structure of `G` on the region `Re ≥ −1/2`, `|Im| ≤ t` -/

lemma mem_poles {t : ℝ} {s : ℂ} : s ∈ poles t ↔ s = 1 ∨ s = 0 ∨ s ∈ zetaZeros t := by
  simp [poles]

lemma zero_facts (hRH : RiemannHypothesis) {t : ℝ} {ρ : ℂ} (hρ : ρ ∈ zetaZeros t) :
    ρ.re = 1 / 2 ∧ ρ ≠ 1 ∧ ρ ≠ 0 ∧ riemannZeta ρ = 0 ∧ |ρ.im| ≤ t := by
  have hre := re_eq_half_of_mem hRH hρ
  have hm := (mem_zetaZeros hRH).mp hρ
  refine ⟨hre, ?_, ?_, hm.2.2.2, hm.2.2.1⟩
  · intro h; rw [h] at hre; norm_num at hre
  · intro h; rw [h] at hre; norm_num at hre

lemma zeta_ne_of_not_pole (hRH : RiemannHypothesis) {t : ℝ} {s : ℂ} (hre : -1 / 2 ≤ s.re)
    (him : |s.im| ≤ t) (hs : s ∉ poles t) : riemannZeta s ≠ 0 := by
  intro hz
  have hs1 : s ≠ 1 := fun h => hs (mem_poles.mpr (Or.inl h))
  have htriv : ¬∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, hn⟩
    have : s.re = -2 * ((n : ℝ) + 1) := by rw [hn]; simp
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hhalf : s.re = 1 / 2 := hRH s hz htriv hs1
  have hmem : s ∈ zetaZeros t :=
    (mem_zetaZeros hRH).mpr ⟨by rw [hhalf]; norm_num, by rw [hhalf]; norm_num, him, hz⟩
  exact hs (mem_poles.mpr (Or.inr (Or.inr hmem)))

lemma analyticAt_PP {y t : ℝ} {s : ℂ} (hs : s ∉ poles t) :
    AnalyticAt ℂ (PP y t) s := by
  have hs1 : s ≠ 1 := fun h => hs (mem_poles.mpr (Or.inl h))
  have hs0 : s ≠ 0 := fun h => hs (mem_poles.mpr (Or.inr (Or.inl h)))
  have hsz : s ∉ zetaZeros t := fun h => hs (mem_poles.mpr (Or.inr (Or.inr h)))
  have h0 : AnalyticAt ℂ (fun z : ℂ => r0 / z) s := analyticAt_const.div analyticAt_id hs0
  have := ((analyticAt_const_div_sub (y : ℂ) hs1).add h0).add
    (analyticAt_sum_div (S := zetaZeros t) (fun ρ => -(mult ρ : ℂ) * u y ρ) hsz)
  exact this

lemma analyticAt_G (hRH : RiemannHypothesis) {y t : ℝ} (hy : 0 < y) {s : ℂ}
    (hre : -1 / 2 ≤ s.re) (him : |s.im| ≤ t) (hs : s ∉ poles t) :
    AnalyticAt ℂ (G y t) s := by
  have hs1 : s ≠ 1 := fun h => hs (mem_poles.mpr (Or.inl h))
  have hs0 : s ≠ 0 := fun h => hs (mem_poles.mpr (Or.inr (Or.inl h)))
  exact (analyticAt_F hy hs1 hs0 (zeta_ne_of_not_pole hRH hre him hs)).sub
    (analyticAt_PP hs)

lemma G_local (hRH : RiemannHypothesis) {y t : ℝ} (hy : 0 < y) {p : ℂ} (hp : p ∈ poles t) :
    ∃ A : ℂ → ℂ, AnalyticAt ℂ A p ∧ G y t =ᶠ[𝓝[≠] p] A := by
  rcases mem_poles.mp hp with rfl | rfl | hρ
  · obtain ⟨B, hB, hFB⟩ := local_one hy
    have h1z : (1 : ℂ) ∉ zetaZeros t := fun h => (zero_facts hRH h).2.1 rfl
    have hR : AnalyticAt ℂ (fun s : ℂ => r0 / s + ∑ ρ ∈ zetaZeros t, (-(mult ρ : ℂ) * u y ρ) / (s - ρ)) 1 :=
      (analyticAt_const.div analyticAt_id one_ne_zero).add
        (analyticAt_sum_div (S := zetaZeros t) (fun ρ => -(mult ρ : ℂ) * u y ρ) h1z)
    refine ⟨fun s => B s - (r0 / s + ∑ ρ ∈ zetaZeros t, (-(mult ρ : ℂ) * u y ρ) / (s - ρ)),
      hB.sub hR, ?_⟩
    filter_upwards [hFB] with s hs
    simp only [G, PP] at hs ⊢
    rw [← hs]; ring
  · obtain ⟨B, hB, hFB⟩ := local_zero hy
    have h0z : (0 : ℂ) ∉ zetaZeros t := fun h => (zero_facts hRH h).2.2.1 rfl
    have hR : AnalyticAt ℂ (fun s : ℂ => (y : ℂ) / (s - 1)
        + ∑ ρ ∈ zetaZeros t, (-(mult ρ : ℂ) * u y ρ) / (s - ρ)) 0 :=
      (analyticAt_const_div_sub (y : ℂ) zero_ne_one).add
        (analyticAt_sum_div (S := zetaZeros t) (fun ρ => -(mult ρ : ℂ) * u y ρ) h0z)
    refine ⟨fun s => B s - ((y : ℂ) / (s - 1)
        + ∑ ρ ∈ zetaZeros t, (-(mult ρ : ℂ) * u y ρ) / (s - ρ)), hB.sub hR, ?_⟩
    filter_upwards [hFB] with s hs
    simp only [G, PP] at hs ⊢
    rw [← hs]; ring
  · obtain ⟨hre, hρ1, hρ0, -, -⟩ := zero_facts hRH hρ
    have hρpos : 0 < p.re := by rw [hre]; norm_num
    obtain ⟨B, hB, hFB⟩ := local_rho hy hρpos hρ1
    have hpe : p ∉ (zetaZeros t).erase p := Finset.notMem_erase p _
    have hR : AnalyticAt ℂ (fun s : ℂ => (y : ℂ) / (s - 1) + r0 / s
        + ∑ ρ ∈ (zetaZeros t).erase p, (-(mult ρ : ℂ) * u y ρ) / (s - ρ)) p :=
      ((analyticAt_const_div_sub (y : ℂ) hρ1).add
        (analyticAt_const.div analyticAt_id hρ0)).add
        (analyticAt_sum_div (S := (zetaZeros t).erase p) (fun ρ => -(mult ρ : ℂ) * u y ρ) hpe)
    refine ⟨fun s => B s - ((y : ℂ) / (s - 1) + r0 / s
        + ∑ ρ ∈ (zetaZeros t).erase p, (-(mult ρ : ℂ) * u y ρ) / (s - ρ)), hB.sub hR, ?_⟩
    filter_upwards [hFB] with s hs
    simp only [G, PP] at hs ⊢
    rw [← Finset.add_sum_erase _ _ hρ, ← hs]; ring

lemma Gt_eventually {y t : ℝ} {p : ℂ} (hp : p ∈ poles t) {A : ℂ → ℂ} (hA : AnalyticAt ℂ A p)
    (hGA : G y t =ᶠ[𝓝[≠] p] A) : Gt y t =ᶠ[𝓝 p] A := by
  have hlim : limUnder (𝓝[≠] p) (G y t) = A p :=
    ((hA.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hGA.symm).limUnder_eq
  have hfar : ∀ᶠ s in 𝓝 p, s ∉ (((poles t).erase p : Finset ℂ) : Set ℂ) :=
    ((poles t).erase p).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
  have hnear := eventually_nhdsWithin_iff.mp hGA
  filter_upwards [hfar, hnear] with s hs1 hs2
  by_cases hsp : s = p
  · subst hsp; simp [Gt, hp, hlim]
  · have hsn : s ∉ poles t := fun h => hs1 (by simp [hsp, h])
    simp [Gt, hsn, hs2 hsp]

lemma Gt_eq_near {y t : ℝ} {s : ℂ} (hs : s ∉ poles t) : Gt y t =ᶠ[𝓝 s] G y t := by
  have hfar : ∀ᶠ z in 𝓝 s, z ∉ ((poles t : Finset ℂ) : Set ℂ) :=
    (poles t).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simpa using hs)
  filter_upwards [hfar] with z hz
  have hz' : z ∉ poles t := by simpa using hz
  simp [Gt, hz']

lemma analyticAt_Gt (hRH : RiemannHypothesis) {y t : ℝ} (hy : 0 < y) {s : ℂ}
    (hre : -1 / 2 ≤ s.re) (him : |s.im| ≤ t) : AnalyticAt ℂ (Gt y t) s := by
  by_cases hs : s ∈ poles t
  · obtain ⟨A, hA, hGA⟩ := G_local hRH hy hs
    exact hA.congr (Gt_eventually hs hA hGA).symm
  · exact (analyticAt_G hRH hy hre him hs).congr (Gt_eq_near hs).symm

end Res

/-- RT. -/
theorem rectInt_logDeriv_zeta (hRH : RiemannHypothesis) {y c t : ℝ}
    (hy : 1 < y) (hc : 1 < c) (ht : 2 ≤ t)
    (hedge : ∀ σ : ℝ, -1 / 2 ≤ σ → σ ≤ c →
      riemannZeta ((σ : ℂ) + t * I) ≠ 0 ∧ riemannZeta ((σ : ℂ) - t * I) ≠ 0) :
    Carmichael.rectInt (fun s => -(deriv riemannZeta s / riemannZeta s) * ((y : ℂ) ^ s / s))
        (((-1 / 2 : ℝ) : ℂ) - (t : ℂ) * I) ((c : ℂ) + (t : ℂ) * I)
      = 2 * π * I * ((y : ℂ) - deriv riemannZeta 0 / riemannZeta 0
          - ∑ ρ ∈ zetaZeros t, (mult ρ : ℂ) * ((y : ℂ) ^ ρ / ρ)) := by
  have hy0 : 0 < y := by linarith
  set z : ℂ := ((-1 / 2 : ℝ) : ℂ) - (t : ℂ) * I with hz
  set w : ℂ := (c : ℂ) + (t : ℂ) * I with hw
  have hzre : z.re = -1 / 2 := by simp [hz]
  have hzim : z.im = -t := by simp [hz]
  have hwre : w.re = c := by simp [hw]
  have hwim : w.im = t := by simp [hw]
  have hct : (-1 / 2 : ℝ) ≤ c := by linarith
  have htt : -t ≤ t := by linarith
  -- points of the closed rectangle
  have hclosed : ∀ s ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]], -1 / 2 ≤ s.re ∧ |s.im| ≤ t := by
    intro s hs
    rw [Complex.mem_reProdIm, hzre, hwre, hzim, hwim, Set.uIcc_of_le hct,
      Set.uIcc_of_le htt] at hs
    exact ⟨hs.1.1, abs_le.mpr hs.2⟩
  -- the zeros of ζ on the line `Re = 1/2` avoid the horizontal edges
  have himne : ∀ ρ ∈ zetaZeros t, ρ.im ≠ t ∧ ρ.im ≠ -t := by
    intro ρ hρ
    obtain ⟨hre, -, -, hz0, -⟩ := Res.zero_facts hRH hρ
    have hh := hedge (1 / 2) (by norm_num) (by linarith)
    constructor
    · intro him
      apply hh.1
      have : ρ = ((1 / 2 : ℝ) : ℂ) + t * I := by
        apply Complex.ext <;> simp [hre, him]
      rw [← this]; exact hz0
    · intro him
      apply hh.2
      have : ρ = ((1 / 2 : ℝ) : ℂ) - t * I := by
        apply Complex.ext <;> simp [hre, him]
      rw [← this]; exact hz0
  -- frame points are not poles
  have hframe : ∀ s ∈ Carmichael.rectFrame z w, s ∉ Res.poles t := by
    intro s hs hp
    rcases Res.mem_poles.mp hp with rfl | rfl | hρ
    · rcases hs with ⟨-, h | h⟩ | ⟨-, h | h⟩
      · rw [hzim] at h; simp at h; linarith
      · rw [hwim] at h; simp at h; linarith
      · rw [hzre] at h; simp at h; linarith
      · rw [hwre] at h; simp at h; linarith
    · rcases hs with ⟨-, h | h⟩ | ⟨-, h | h⟩
      · rw [hzim] at h; simp at h; linarith
      · rw [hwim] at h; simp at h; linarith
      · rw [hzre] at h; norm_num at h
      · rw [hwre] at h; simp at h; linarith
    · obtain ⟨hre, -, -, -, -⟩ := Res.zero_facts hRH hρ
      rcases hs with ⟨-, h | h⟩ | ⟨-, h | h⟩
      · rw [hzim] at h; exact (himne s hρ).2 h
      · rw [hwim] at h; exact (himne s hρ).1 h
      · rw [hzre, hre] at h; norm_num at h
      · rw [hwre, hre] at h; linarith
  have hframe_reg : ∀ s ∈ Carmichael.rectFrame z w, -1 / 2 ≤ s.re ∧ |s.im| ≤ t :=
    fun s hs => hclosed s (Carmichael.rectFrame_subset z w hs)
  -- poles are strictly inside
  have hinside : ∀ p ∈ Res.poles t, z.re < p.re ∧ p.re < w.re ∧ z.im < p.im ∧ p.im < w.im := by
    intro p hp
    rw [hzre, hwre, hzim, hwim]
    rcases Res.mem_poles.mp hp with rfl | rfl | hρ
    · simp only [one_re, one_im]
      exact ⟨by norm_num, hc, by linarith, by linarith⟩
    · simp only [zero_re, zero_im]
      exact ⟨by norm_num, by linarith, by linarith, by linarith⟩
    · obtain ⟨hre, -, -, -, him⟩ := Res.zero_facts hRH hρ
      have hn := himne p hρ
      have h1 := (abs_le.mp him)
      refine ⟨by rw [hre]; norm_num, by rw [hre]; linarith, ?_, ?_⟩
      · exact lt_of_le_of_ne h1.1 (fun h => hn.2 h.symm)
      · exact lt_of_le_of_ne h1.2 hn.1
  -- Step 1: `∮ Gt = 0`
  have hGt0 : Carmichael.rectInt (Res.Gt y t) z w = 0 := by
    apply Carmichael.rectInt_eq_zero ∅ Set.countable_empty
    · intro s hs
      obtain ⟨h1, h2⟩ := hclosed s hs
      exact (Res.analyticAt_Gt hRH hy0 h1 h2).continuousAt.continuousWithinAt
    · intro s hs
      have hs' : s ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]] := by
        have hs1 := hs.1
        rw [Complex.mem_reProdIm, hzre, hwre, hzim, hwim, min_eq_left hct, max_eq_right hct,
          min_eq_left htt, max_eq_right htt] at hs1
        rw [Complex.mem_reProdIm, hzre, hwre, hzim, hwim, Set.uIcc_of_le hct,
          Set.uIcc_of_le htt]
        exact ⟨Set.Ioo_subset_Icc_self hs1.1, Set.Ioo_subset_Icc_self hs1.2⟩
      obtain ⟨h1, h2⟩ := hclosed s hs'
      exact (Res.analyticAt_Gt hRH hy0 h1 h2).differentiableAt
  -- Step 2: `∮ Gt = ∮ G`
  have hGtG : Carmichael.rectInt (Res.Gt y t) z w = Carmichael.rectInt (Res.G y t) z w :=
    Carmichael.rectInt_congr (fun s hs => by simp [Res.Gt, hframe s hs])
  -- continuity of the pieces on the frame
  have hGc : ContinuousOn (Res.G y t) (Carmichael.rectFrame z w) := fun s hs =>
    (Res.analyticAt_G hRH hy0 (hframe_reg s hs).1 (hframe_reg s hs).2
      (hframe s hs)).continuousAt.continuousWithinAt
  have hdivc : ∀ (a p : ℂ), p ∈ Res.poles t →
      ContinuousOn (fun s : ℂ => a / (s - p)) (Carmichael.rectFrame z w) := by
    intro a p hp s hs
    have hsp : s ≠ p := fun h => hframe s hs (h ▸ hp)
    exact (Res.analyticAt_const_div_sub a hsp).continuousAt.continuousWithinAt
  have h1p : (1 : ℂ) ∈ Res.poles t := Res.mem_poles.mpr (Or.inl rfl)
  have h0p : (0 : ℂ) ∈ Res.poles t := Res.mem_poles.mpr (Or.inr (Or.inl rfl))
  have hρp : ∀ ρ ∈ zetaZeros t, ρ ∈ Res.poles t :=
    fun ρ hρ => Res.mem_poles.mpr (Or.inr (Or.inr hρ))
  have hr0fun : (fun s : ℂ => Res.r0 / s) = fun s : ℂ => Res.r0 / (s - 0) := by
    funext s; rw [sub_zero]
  have hA : ContinuousOn (fun s : ℂ => (y : ℂ) / (s - 1)) (Carmichael.rectFrame z w) :=
    hdivc _ _ h1p
  have hB : ContinuousOn (fun s : ℂ => Res.r0 / s) (Carmichael.rectFrame z w) := by
    rw [hr0fun]; exact hdivc _ _ h0p
  have hC : ∀ ρ ∈ zetaZeros t, ContinuousOn
      (fun s : ℂ => (-(mult ρ : ℂ) * Res.u y ρ) / (s - ρ)) (Carmichael.rectFrame z w) :=
    fun ρ hρ => hdivc _ _ (hρp ρ hρ)
  have hPPc : ContinuousOn (Res.PP y t) (Carmichael.rectFrame z w) :=
    (hA.add hB).add (continuousOn_finsetSum _ hC)
  -- Step 3: the principal parts
  have hcauchy : ∀ (a p : ℂ), p ∈ Res.poles t →
      Carmichael.rectInt (fun s : ℂ => a / (s - p)) z w = 2 * π * I * a := by
    intro a p hp
    obtain ⟨h1, h2, h3, h4⟩ := hinside p hp
    exact Carmichael.rectInt_cauchy (differentiable_const a) h1 h2 h3 h4
  have hPP : Carmichael.rectInt (Res.PP y t) z w
      = 2 * π * I * (y : ℂ) + 2 * π * I * Res.r0
        + ∑ ρ ∈ zetaZeros t, 2 * π * I * (-(mult ρ : ℂ) * Res.u y ρ) := by
    have e1 : Res.PP y t = fun s => ((y : ℂ) / (s - 1) + Res.r0 / s)
        + ∑ ρ ∈ zetaZeros t, (-(mult ρ : ℂ) * Res.u y ρ) / (s - ρ) := rfl
    have hAB : ContinuousOn (fun s : ℂ => (y : ℂ) / (s - 1) + Res.r0 / s)
        (Carmichael.rectFrame z w) := hA.add hB
    have hCs : ContinuousOn (fun s : ℂ => ∑ ρ ∈ zetaZeros t, (-(mult ρ : ℂ) * Res.u y ρ) / (s - ρ))
        (Carmichael.rectFrame z w) := continuousOn_finsetSum _ hC
    rw [e1, Carmichael.rectInt_add hAB hCs,
      Carmichael.rectInt_add hA hB,
      Carmichael.rectInt_sum (f := fun ρ s => (-(mult ρ : ℂ) * Res.u y ρ) / (s - ρ)) _ hC,
      hcauchy _ _ h1p, hr0fun, hcauchy _ _ h0p]
    congr 1
    exact Finset.sum_congr rfl (fun ρ hρ => hcauchy _ _ (hρp ρ hρ))
  -- Step 4: assemble
  have hF : Carmichael.rectInt (Res.F y) z w
      = Carmichael.rectInt (Res.G y t) z w + Carmichael.rectInt (Res.PP y t) z w := by
    rw [← Carmichael.rectInt_add hGc hPPc]
    apply Carmichael.rectInt_congr
    intro s _
    simp [Res.G]
  show Carmichael.rectInt (Res.F y) z w = _
  have hsum : ∑ ρ ∈ zetaZeros t, 2 * π * I * (-(mult ρ : ℂ) * Res.u y ρ)
      = -(2 * π * I * ∑ ρ ∈ zetaZeros t, (mult ρ : ℂ) * ((y : ℂ) ^ ρ / ρ)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro ρ _
    simp only [Res.u]
    ring
  rw [hF, ← hGtG, hGt0, hPP, zero_add, hsum, Res.r0]
  ring

end PPF.RH
