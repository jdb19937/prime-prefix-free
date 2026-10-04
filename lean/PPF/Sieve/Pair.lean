/-
The pair sieve in an interval.

For `a, c ≥ 1` and an interval `[Y, Y + t)` the number of `n` with `n` and
`a n + c` both prime is at most `16416 · (ac/φ(ac))² · t / (log t)²`. This is
the dimension-two Selberg sieve applied to `n(an+c)`, `n ∈ [Y, Y + t)`, sifted
by the primes `p ≤ z`, `p ∤ 2ac`, with `z = t^{1/16}`. It follows the proof of
`Carmichael.twin_type_bound` (vendored `PPF.Vendor.TwinSieve`): the sifting
primes, density and level coincide with those of `Carmichael.twinSieve (a*c)`,
so the lower bound for the Selberg bounding sum is reused verbatim; only the
support, the root count of `X(aX+c)` and the residue-class count in an interval
change.
-/
import Mathlib
import PPF.Vendor.TwinSieve

set_option autoImplicit false

namespace PPF.Sieve

noncomputable section

open Finset Nat ArithmeticFunction BoundingSieve Carmichael

open scoped ArithmeticFunction.omega ArithmeticFunction.Omega

/-! ### A residue class in an interval -/

lemma add_mod_eq_iff_modEq (Y k : ℕ) {d r : ℕ} (hd : 0 < d) (hr : r < d) :
    (Y + k) % d = r ↔ k ≡ r + d - Y % d [MOD d] := by
  have hYd : Y % d < d := Nat.mod_lt Y hd
  have hsum : r + d - Y % d + Y % d = r + d := by omega
  have hY : Y % d ≡ Y [MOD d] := Nat.mod_modEq Y d
  have hrd : r + d ≡ r [MOD d] := by
    unfold Nat.ModEq
    rw [Nat.add_mod_right]
  constructor
  · intro h
    have h1 : Y + k ≡ r [MOD d] := by
      unfold Nat.ModEq
      rw [h, Nat.mod_eq_of_lt hr]
    apply Nat.ModEq.add_right_cancel' (Y % d)
    rw [hsum]
    calc k + Y % d ≡ k + Y [MOD d] := Nat.ModEq.add_left k hY
      _ = Y + k := add_comm _ _
      _ ≡ r [MOD d] := h1
      _ ≡ r + d [MOD d] := hrd.symm
  · intro h
    have h2 : k + Y % d ≡ r + d [MOD d] := by
      rw [← hsum]
      exact Nat.ModEq.add_right _ h
    have h3 : Y + k ≡ r [MOD d] := by
      calc Y + k = k + Y := add_comm _ _
        _ ≡ k + Y % d [MOD d] := Nat.ModEq.add_left k hY.symm
        _ ≡ r + d [MOD d] := h2
        _ ≡ r [MOD d] := hrd
    unfold Nat.ModEq at h3
    rw [h3, Nat.mod_eq_of_lt hr]

/-- The number of `n ∈ [Y, Y + t)` in a fixed residue class mod `d` differs
from `t/d` by at most `1`. -/
lemma card_Ico_filter_mod (Y t : ℕ) {d r : ℕ} (hd : 0 < d) (hr : r < d) :
    |(#((Ico Y (Y + t)).filter (fun n => n % d = r)) : ℝ) - t / d| ≤ 1 := by
  set v := r + d - Y % d with hv
  have hset : (Ico Y (Y + t)).filter (fun n => n % d = r)
      = ((range t).filter (fun k => k ≡ v [MOD d])).map (addLeftEmbedding Y) := by
    ext n
    simp only [mem_filter, mem_Ico, mem_map, mem_range, addLeftEmbedding_apply]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨n - Y, ⟨by omega, ?_⟩, by omega⟩
      rw [← add_mod_eq_iff_modEq Y (n - Y) hd hr, Nat.add_sub_cancel' h1]
      exact h3
    · rintro ⟨k, ⟨hk, hkv⟩, rfl⟩
      exact ⟨⟨by omega, by omega⟩, (add_mod_eq_iff_modEq Y k hd hr).mpr hkv⟩
  have hcount : #((range t).filter (fun k => k ≡ v [MOD d]))
      = t / d + if v % d < t % d then 1 else 0 := by
    rw [← Nat.count_eq_card_filter_range]
    exact Nat.count_modEq_card t hd v
  rw [hset, Finset.card_map, hcount]
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have key : (t : ℝ) = d * ((t / d : ℕ) : ℝ) + ((t % d : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod t d).symm
  have hmod : ((t % d : ℕ) : ℝ) < d := by exact_mod_cast Nat.mod_lt t hd
  have hmod0 : (0 : ℝ) ≤ ((t % d : ℕ) : ℝ) := by positivity
  have hdiv : (t : ℝ) / d = ((t / d : ℕ) : ℝ) + ((t % d : ℕ) : ℝ) / d := by
    rw [key]
    field_simp
  have hfrac0 : (0 : ℝ) ≤ ((t % d : ℕ) : ℝ) / d := by positivity
  have hfrac1 : ((t % d : ℕ) : ℝ) / d ≤ 1 := by
    rw [div_le_one hdR]
    exact hmod.le
  rw [hdiv]
  split_ifs
  · push_cast
    rw [abs_le]
    constructor <;> linarith
  · push_cast
    rw [abs_le]
    constructor <;> linarith

/-! ### Root counting for `n(an+c) mod d` -/

/-- Divisibility of `n(an+c)` only depends on `n` mod `d`. -/
lemma dvd_pair_iff_of_modEq (a c : ℕ) {d r n : ℕ} (h : r ≡ n [MOD d]) :
    d ∣ r * (a * r + c) ↔ d ∣ n * (a * n + c) := by
  have h2 : r * (a * r + c) ≡ n * (a * n + c) [MOD d] :=
    h.mul ((h.mul_left a).add_right c)
  constructor
  · intro hd
    exact Nat.modEq_zero_iff_dvd.mp (h2.symm.trans (Nat.modEq_zero_iff_dvd.mpr hd))
  · intro hd
    exact Nat.modEq_zero_iff_dvd.mp (h2.trans (Nat.modEq_zero_iff_dvd.mpr hd))

/-- The number of roots of `X(aX+c)` modulo `d`. -/
def pairRootCount (a c d : ℕ) : ℕ := #((range d).filter (fun r => d ∣ r * (a * r + c)))

lemma pairRootCount_one (a c : ℕ) : pairRootCount a c 1 = 1 := by
  simp [pairRootCount, Finset.range_one]

/-- For a prime `p ∤ ac` the polynomial `X(aX+c)` has exactly two roots mod
`p`, namely `0` and `-c a⁻¹`. -/
lemma pairRootCount_prime {a c p : ℕ} (hp : p.Prime) (hpa : ¬p ∣ a) (hpc : ¬p ∣ c) :
    pairRootCount a c p = 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have ha0 : (a : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hpa
  have hc0 : (c : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hpc
  have hsol : ∀ x : ZMod p, x * ((a : ZMod p) * x + c) = 0 ↔
      x = 0 ∨ x = -(c : ZMod p) * (a : ZMod p)⁻¹ := by
    intro x
    rw [_root_.mul_eq_zero]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · right
        have hax : (a : ZMod p) * x = -c := by linear_combination h
        calc x = (a : ZMod p)⁻¹ * ((a : ZMod p) * x) := by
              rw [← mul_assoc, inv_mul_cancel₀ ha0, one_mul]
          _ = -(c : ZMod p) * (a : ZMod p)⁻¹ := by rw [hax]; ring
    · rintro (h | h)
      · exact Or.inl h
      · right
        rw [h]
        have : (a : ZMod p) * (-(c : ZMod p) * (a : ZMod p)⁻¹) = -c := by
          rw [mul_comm (-(c : ZMod p)), ← mul_assoc, mul_inv_cancel₀ ha0, one_mul]
        rw [this]
        ring
  have hcard : pairRootCount a c p
      = #(Finset.univ.filter (fun x : ZMod p => x * ((a : ZMod p) * x + c) = 0)) := by
    unfold pairRootCount
    apply Finset.card_bij (fun (r : ℕ) _ => (Nat.cast r : ZMod p))
    · intro r hr
      rw [mem_filter, mem_range] at hr
      rw [mem_filter]
      refine ⟨mem_univ _, ?_⟩
      have hz : ((r * (a * r + c) : ℕ) : ZMod p) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).mpr hr.2
      push_cast at hz
      exact hz
    · intro r₁ hr₁ r₂ hr₂ he
      rw [mem_filter, mem_range] at hr₁ hr₂
      have := congrArg ZMod.val he
      rwa [ZMod.val_cast_of_lt hr₁.1, ZMod.val_cast_of_lt hr₂.1] at this
    · intro x hx
      rw [mem_filter] at hx
      refine ⟨x.val, ?_, ?_⟩
      · rw [mem_filter, mem_range]
        refine ⟨ZMod.val_lt x, ?_⟩
        rw [← ZMod.natCast_eq_zero_iff]
        push_cast
        rw [ZMod.natCast_val, ZMod.cast_id]
        exact hx.2
      · rw [ZMod.natCast_val, ZMod.cast_id]
  rw [hcard,
    show Finset.univ.filter (fun x : ZMod p => x * ((a : ZMod p) * x + c) = 0)
      = {0, -(c : ZMod p) * (a : ZMod p)⁻¹} by
        ext x
        simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
        exact hsol x]
  rw [Finset.card_insert_of_notMem, Finset.card_singleton]
  rw [mem_singleton]
  intro hcz
  have h1 : (c : ZMod p) * (a : ZMod p)⁻¹ = 0 := by
    have := hcz.symm
    rw [neg_mul, neg_eq_zero] at this
    exact this
  rcases _root_.mul_eq_zero.mp h1 with h | h
  · exact hc0 h
  · exact ha0 (inv_eq_zero.mp h)

/-- Root counts are multiplicative in coprime moduli (CRT). -/
lemma pairRootCount_mul (a c : ℕ) {d₁ d₂ : ℕ} (h : Nat.Coprime d₁ d₂)
    (h₁ : 0 < d₁) (h₂ : 0 < d₂) :
    pairRootCount a c (d₁ * d₂) = pairRootCount a c d₁ * pairRootCount a c d₂ := by
  unfold pairRootCount
  rw [← Finset.card_product]
  have hD : 0 < d₁ * d₂ := Nat.mul_pos h₁ h₂
  rw [show ((range d₁).filter (fun r => d₁ ∣ r * (a * r + c))) ×ˢ
      ((range d₂).filter (fun r => d₂ ∣ r * (a * r + c)))
      = ((range d₁) ×ˢ (range d₂)).filter
        (fun q => d₁ ∣ q.1 * (a * q.1 + c) ∧ d₂ ∣ q.2 * (a * q.2 + c)) by
    ext q
    simp only [mem_product, mem_filter, mem_range]
    tauto]
  apply Finset.card_bij (fun r _ => ((r % d₁ : ℕ), (r % d₂ : ℕ)))
  · intro r hr
    rw [mem_filter, mem_range] at hr
    rw [mem_filter, mem_product, mem_range, mem_range]
    refine ⟨⟨Nat.mod_lt r h₁, Nat.mod_lt r h₂⟩, ?_, ?_⟩
    · rw [dvd_pair_iff_of_modEq a c (Nat.mod_modEq r d₁)]
      exact dvd_trans (Dvd.intro d₂ rfl) hr.2
    · rw [dvd_pair_iff_of_modEq a c (Nat.mod_modEq r d₂)]
      exact dvd_trans (Dvd.intro_left d₁ rfl) hr.2
  · intro r₁ hr₁ r₂ hr₂ he
    rw [mem_filter, mem_range] at hr₁ hr₂
    have he1 : r₁ % d₁ = r₂ % d₁ := congrArg Prod.fst he
    have he2 : r₁ % d₂ = r₂ % d₂ := congrArg Prod.snd he
    have hmod : r₁ ≡ r₂ [MOD d₁ * d₂] :=
      (Nat.modEq_and_modEq_iff_modEq_mul h).mp ⟨he1, he2⟩
    calc r₁ = r₁ % (d₁ * d₂) := (Nat.mod_eq_of_lt hr₁.1).symm
      _ = r₂ % (d₁ * d₂) := hmod
      _ = r₂ := Nat.mod_eq_of_lt hr₂.1
  · intro q hq
    rw [mem_filter, mem_product, mem_range, mem_range] at hq
    obtain ⟨⟨hq1, hq2⟩, hd1, hd2⟩ := hq
    obtain ⟨x, hx1, hx2⟩ := Nat.chineseRemainder h q.1 q.2
    refine ⟨x % (d₁ * d₂), ?_, ?_⟩
    · rw [mem_filter, mem_range]
      refine ⟨Nat.mod_lt x hD, ?_⟩
      have hxq1 : x % (d₁ * d₂) ≡ q.1 [MOD d₁] :=
        ((Nat.mod_modEq x (d₁ * d₂)).of_dvd (Dvd.intro d₂ rfl)).trans hx1
      have hxq2 : x % (d₁ * d₂) ≡ q.2 [MOD d₂] :=
        ((Nat.mod_modEq x (d₁ * d₂)).of_dvd (Dvd.intro_left d₁ rfl)).trans hx2
      apply Nat.Coprime.mul_dvd_of_dvd_of_dvd h
      · rw [dvd_pair_iff_of_modEq a c hxq1.symm] at hd1
        exact hd1
      · rw [dvd_pair_iff_of_modEq a c hxq2.symm] at hd2
        exact hd2
    · have hxq1 : x % (d₁ * d₂) ≡ q.1 [MOD d₁] :=
        ((Nat.mod_modEq x (d₁ * d₂)).of_dvd (Dvd.intro d₂ rfl)).trans hx1
      have hxq2 : x % (d₁ * d₂) ≡ q.2 [MOD d₂] :=
        ((Nat.mod_modEq x (d₁ * d₂)).of_dvd (Dvd.intro_left d₁ rfl)).trans hx2
      have e1 : x % (d₁ * d₂) % d₁ = q.1 := by
        have := hxq1
        unfold Nat.ModEq at this
        rwa [Nat.mod_eq_of_lt hq1] at this
      have e2 : x % (d₁ * d₂) % d₂ = q.2 := by
        have := hxq2
        unfold Nat.ModEq at this
        rwa [Nat.mod_eq_of_lt hq2] at this
      rw [e1, e2]

/-- The root count of a product of distinct primes avoiding `ac` is `2^#s`. -/
lemma pairRootCount_prod (a c : ℕ) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ ¬p ∣ a ∧ ¬p ∣ c) :
    pairRootCount a c (∏ p ∈ s, p) = 2 ^ #s := by
  induction s using Finset.cons_induction with
  | empty => simpa using pairRootCount_one a c
  | cons q s hq ih =>
    have hqp : q.Prime := (hs q (mem_cons_self q s)).1
    have hsp : ∀ p ∈ s, p.Prime ∧ ¬p ∣ a ∧ ¬p ∣ c := fun p hp => hs p (mem_cons_of_mem hp)
    have hcop : Nat.Coprime q (∏ p ∈ s, p) :=
      Nat.Coprime.prod_right fun p hp =>
        (Nat.coprime_primes hqp (hsp p hp).1).mpr (by rintro rfl; exact hq hp)
    have hprod_pos : 0 < ∏ p ∈ s, p :=
      Finset.prod_pos fun p hp => (hsp p hp).1.pos
    rw [prod_cons, pairRootCount_mul a c hcop hqp.pos hprod_pos,
      pairRootCount_prime hqp (hs q (mem_cons_self q s)).2.1 (hs q (mem_cons_self q s)).2.2,
      ih hsp, Finset.card_cons, pow_succ]
    ring

/-! ### The pair sieve -/

/-- The pair Selberg sieve: support `n(an+c)` for `n ∈ [Y, Y + t)`, sifting
primes `p ≤ z` with `p ∤ 2ac`, density `ν(d) = 2^{ω(d)}/d`, level `z²`.
Everything but the support coincides with `Carmichael.twinSieve (a*c) z t`. -/
def pairSieveS (a c z Y t : ℕ) (hz : 1 ≤ z) : SelbergSieve where
  support := (Ico Y (Y + t)).image (fun n => n * (a * n + c))
  prodPrimes := twinProdPrimes (a * c) z
  prodPrimes_squarefree := twinProdPrimes_squarefree (a * c) z
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := t
  nu := ArithmeticFunction.prodPrimeFactors (fun p => 2 / (p : ℝ))
  nu_mult := by arith_mult
  nu_pos_of_prime := by
    intro p hp _
    rw [ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero, hp.primeFactors,
      Finset.prod_singleton]
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    positivity
  nu_lt_one_of_prime := by
    intro p hp hdvd
    rw [ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero, hp.primeFactors,
      Finset.prod_singleton]
    have h3 : 3 ≤ p := three_le_of_mem_twinPrimeSet (mem_twinPrimeSet_of_dvd hp hdvd)
    rw [div_lt_one (by positivity)]
    exact_mod_cast h3
  level := ((z : ℕ) : ℝ) ^ 2
  one_le_level := by
    have : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
    nlinarith

variable {a c z Y t : ℕ}

/-- The bounding sum only sees the primes, the density and the level. -/
lemma pairSieveS_boundingSum_eq (hz : 1 ≤ z) :
    selbergBoundingSum (pairSieveS a c z Y t hz)
      = selbergBoundingSum (twinSieve (a * c) z t hz) := rfl

lemma pairSieveS_nu_eq (hz : 1 ≤ z) {d : ℕ} (hd : d ∣ twinProdPrimes (a * c) z) :
    (pairSieveS a c z Y t hz).nu d = (2 : ℝ) ^ (#d.primeFactors) / d :=
  twinSieve_nu_eq (m := a * c) (t := t) hz hd

/-- The map `n ↦ n(an+c)` is strictly monotone for `c ≥ 1`. -/
lemma pairMap_strictMono (a : ℕ) {c : ℕ} (hc : 1 ≤ c) :
    StrictMono (fun n : ℕ => n * (a * n + c)) := by
  intro x y hxy
  simp only
  have h1 : a * x + c ≤ a * y + c := by
    have := Nat.mul_le_mul (le_refl a) hxy.le
    omega
  calc x * (a * x + c) < y * (a * x + c) :=
        mul_lt_mul_of_pos_right hxy (by omega)
    _ ≤ y * (a * y + c) := Nat.mul_le_mul le_rfl h1

lemma pairSieveS_multSum (hc : 1 ≤ c) (hz : 1 ≤ z) (d : ℕ) :
    (pairSieveS a c z Y t hz).multSum d
      = ∑ n ∈ Ico Y (Y + t), if d ∣ n * (a * n + c) then (1 : ℝ) else 0 := by
  show (∑ k ∈ (Ico Y (Y + t)).image (fun n => n * (a * n + c)),
      if d ∣ k then (1 : ℝ) else 0) = _
  rw [Finset.sum_image]
  intro x _ y _ hxy
  exact (pairMap_strictMono a hc).injective hxy

lemma pairSieveS_siftedSum (hc : 1 ≤ c) (hz : 1 ≤ z) :
    (pairSieveS a c z Y t hz).siftedSum
      = ∑ n ∈ Ico Y (Y + t),
          if Nat.Coprime (twinProdPrimes (a * c) z) (n * (a * n + c)) then (1 : ℝ) else 0 := by
  show (∑ k ∈ (Ico Y (Y + t)).image (fun n => n * (a * n + c)),
      if Nat.Coprime (twinProdPrimes (a * c) z) k then (1 : ℝ) else 0) = _
  rw [Finset.sum_image]
  intro x _ y _ hxy
  exact (pairMap_strictMono a hc).injective hxy

/-- The count of prime pairs is at most `z` plus the sifted sum. -/
lemma pair_count_le_siftedSum_add (ha : 1 ≤ a) (hc : 1 ≤ c) (hz : 1 ≤ z) :
    ((#((Ico Y (Y + t)).filter (fun n => n.Prime ∧ (a * n + c).Prime))) : ℝ)
      ≤ (pairSieveS a c z Y t hz).siftedSum + z := by
  classical
  set T := (Ico Y (Y + t)).filter (fun n => n.Prime ∧ (a * n + c).Prime) with hT
  set T' := T.filter (fun q => z < q) with hT'
  have hsplit : T ⊆ T' ∪ Icc 1 z := by
    intro q hq
    rcases le_or_gt q z with h | h
    · refine mem_union_right _ (mem_Icc.mpr ⟨?_, h⟩)
      have := (mem_filter.mp hq).2.1.two_le
      omega
    · exact mem_union_left _ (mem_filter.mpr ⟨hq, h⟩)
  have hcard : #T ≤ #T' + z := by
    calc #T ≤ #(T' ∪ Icc 1 z) := Finset.card_le_card hsplit
      _ ≤ #T' + #(Icc 1 z) := Finset.card_union_le _ _
      _ = #T' + z := by rw [Nat.card_Icc, Nat.add_sub_cancel]
  have hsurvive : (#T' : ℝ) ≤ (pairSieveS a c z Y t hz).siftedSum := by
    rw [pairSieveS_siftedSum hc hz]
    have hsub : ∀ n ∈ T', (if Nat.Coprime (twinProdPrimes (a * c) z) (n * (a * n + c))
        then (1 : ℝ) else 0) = 1 := by
      intro q hq
      rw [mem_filter, hT, mem_filter] at hq
      obtain ⟨⟨_, hqp, hmqp⟩, hqz⟩ := hq
      rw [if_pos]
      apply Nat.coprime_of_dvd
      intro k hk hkP hkq
      have hkset := mem_twinPrimeSet_of_dvd hk hkP
      have hkz : k ≤ z := (mem_twinPrimeSet.mp hkset).1
      rcases (Nat.Prime.dvd_mul hk).mp hkq with h | h
      · have : k = q := (Nat.prime_dvd_prime_iff_eq hk hqp).mp h
        omega
      · have : k = a * q + c := (Nat.prime_dvd_prime_iff_eq hk hmqp).mp h
        have : q ≤ a * q := Nat.le_mul_of_pos_left q (by omega)
        omega
    calc (#T' : ℝ) = ∑ n ∈ T', (1 : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = ∑ n ∈ T', if Nat.Coprime (twinProdPrimes (a * c) z) (n * (a * n + c))
            then (1 : ℝ) else 0 := (Finset.sum_congr rfl hsub).symm
      _ ≤ ∑ n ∈ Ico Y (Y + t), if Nat.Coprime (twinProdPrimes (a * c) z) (n * (a * n + c))
            then (1 : ℝ) else 0 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro q hq
            exact (mem_filter.mp ((mem_filter.mp hq).1)).1
          · intro q _ _
            positivity
  have hcast : (#T : ℝ) ≤ (#T' : ℝ) + z := by exact_mod_cast hcard
  linarith

/-! ### The remainder bound -/

/-- The root count of a squarefree divisor of the sifting product is
`2^{ω(d)}`. -/
lemma pairRootCount_of_dvd {d : ℕ} (hd : d ∣ twinProdPrimes (a * c) z) :
    pairRootCount a c d = 2 ^ (#d.primeFactors) := by
  have hsq : Squarefree d := (twinProdPrimes_squarefree (a * c) z).squarefree_of_dvd hd
  have hrepr : d = ∏ p ∈ d.primeFactors, p :=
    (Nat.prod_primeFactors_of_squarefree hsq).symm
  conv_lhs => rw [hrepr]
  apply pairRootCount_prod
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpP : p ∣ twinProdPrimes (a * c) z := (Nat.dvd_of_mem_primeFactors hp).trans hd
  have hset := mem_twinPrimeSet.mp (mem_twinPrimeSet_of_dvd hpp hpP)
  refine ⟨hpp, fun hc => hset.2.2 ?_, fun hc => hset.2.2 ?_⟩
  · exact hc.trans (Dvd.intro (2 * c) (by ring))
  · exact hc.trans (Dvd.intro (2 * a) (by ring))

/-- The remainder of the pair sieve at a divisor `d` of the sifting product
is at most `2^{ω(d)} ≤ d` in absolute value. -/
lemma pairSieveS_abs_rem_le (hc : 1 ≤ c) (hz : 1 ≤ z) {d : ℕ}
    (hd : d ∣ twinProdPrimes (a * c) z) :
    |(pairSieveS a c z Y t hz).rem d| ≤ (d : ℝ) := by
  classical
  have hsq : Squarefree d := (twinProdPrimes_squarefree (a * c) z).squarefree_of_dvd hd
  have hd0 : 0 < d := Nat.pos_of_ne_zero hsq.ne_zero
  have hfib : ∀ n : ℕ, n ∈ Ico Y (Y + t) → n % d ∈ range d :=
    fun n _ => mem_range.mpr (Nat.mod_lt n hd0)
  have hmult : (pairSieveS a c z Y t hz).multSum d
      = ∑ r ∈ (range d).filter (fun r => d ∣ r * (a * r + c)),
          (#((Ico Y (Y + t)).filter (fun n => n % d = r)) : ℝ) := by
    rw [pairSieveS_multSum hc hz,
      ← Finset.sum_fiberwise_of_maps_to hfib
        (fun n => if d ∣ n * (a * n + c) then (1 : ℝ) else 0)]
    rw [Finset.sum_filter]
    refine sum_congr rfl fun r _ => ?_
    have hinner : ∀ n ∈ (Ico Y (Y + t)).filter (fun n => n % d = r),
        (if d ∣ n * (a * n + c) then (1 : ℝ) else 0)
          = (if d ∣ r * (a * r + c) then (1 : ℝ) else 0) := by
      intro n hn
      have hr : n % d = r := (mem_filter.mp hn).2
      have hcong : r ≡ n [MOD d] := hr ▸ Nat.mod_modEq n d
      exact if_congr (dvd_pair_iff_of_modEq a c hcong).symm rfl rfl
    rw [Finset.sum_congr rfl hinner]
    split_ifs with h
    · rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    · rw [Finset.sum_const, smul_zero]
  have hnut : (pairSieveS a c z Y t hz).nu d * (pairSieveS a c z Y t hz).totalMass
      = ∑ _r ∈ (range d).filter (fun r => d ∣ r * (a * r + c)), ((t : ℝ) / d) := by
    rw [Finset.sum_const, show (pairSieveS a c z Y t hz).totalMass = (t : ℝ) from rfl,
      pairSieveS_nu_eq hz hd]
    have hcard : #((range d).filter (fun r => d ∣ r * (a * r + c)))
        = 2 ^ (#d.primeFactors) := pairRootCount_of_dvd hd
    rw [hcard, nsmul_eq_mul]
    push_cast
    have hdR : ((d : ℝ)) ≠ 0 := by positivity
    field_simp
  have hrem : (pairSieveS a c z Y t hz).rem d
      = ∑ r ∈ (range d).filter (fun r => d ∣ r * (a * r + c)),
          ((#((Ico Y (Y + t)).filter (fun n => n % d = r)) : ℝ) - (t : ℝ) / d) := by
    rw [rem, hmult, hnut, Finset.sum_sub_distrib]
  rw [hrem]
  calc |∑ r ∈ (range d).filter (fun r => d ∣ r * (a * r + c)),
        ((#((Ico Y (Y + t)).filter (fun n => n % d = r)) : ℝ) - (t : ℝ) / d)|
      ≤ ∑ r ∈ (range d).filter (fun r => d ∣ r * (a * r + c)),
          |(#((Ico Y (Y + t)).filter (fun n => n % d = r)) : ℝ) - (t : ℝ) / d| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ (range d).filter (fun r => d ∣ r * (a * r + c)), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro r hr
        have hrd : r < d := mem_range.mp (mem_filter.mp hr).1
        exact card_Ico_filter_mod Y t hd0 hrd
    _ ≤ (d : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        show ((pairRootCount a c d : ℕ) : ℝ) ≤ (d : ℝ)
        rw [pairRootCount_of_dvd hd]
        exact_mod_cast two_pow_card_primeFactors_le hsq

/-- The sieve error term is at most `z⁸`. -/
lemma pairSieveS_errSum_le (hc : 1 ≤ c) (hz : 1 ≤ z) :
    (∑ d ∈ divisors (pairSieveS a c z Y t hz).prodPrimes,
      if (d : ℝ) ≤ (pairSieveS a c z Y t hz).level then
        (3 : ℝ) ^ ω d * |(pairSieveS a c z Y t hz).rem d| else 0)
      ≤ ((z : ℕ) : ℝ) ^ 8 := by
  classical
  rw [show (pairSieveS a c z Y t hz).prodPrimes = twinProdPrimes (a * c) z from rfl,
    show (pairSieveS a c z Y t hz).level = ((z : ℕ) : ℝ) ^ 2 from rfl]
  have hzR : (0 : ℝ) ≤ (z : ℝ) := by positivity
  calc (∑ d ∈ divisors (twinProdPrimes (a * c) z),
      if (d : ℝ) ≤ ((z : ℕ) : ℝ) ^ 2 then
        (3 : ℝ) ^ (ω d) * |(pairSieveS a c z Y t hz).rem d| else 0)
      ≤ ∑ d ∈ divisors (twinProdPrimes (a * c) z),
          (if (d : ℝ) ≤ ((z : ℕ) : ℝ) ^ 2 then ((z : ℝ) ^ 2) ^ 3 else 0) := by
        apply Finset.sum_le_sum
        intro d hd
        obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hd
        have hsq : Squarefree d :=
          (twinProdPrimes_squarefree (a * c) z).squarefree_of_dvd hdvd
        split_ifs with h
        · have h3 : (3 : ℝ) ^ (ω d) ≤ (d : ℝ) ^ 2 := by
            rw [cardDistinctFactors_eq_card_primeFactors]
            exact_mod_cast three_pow_card_primeFactors_le hsq
          have hrem : |(pairSieveS a c z Y t hz).rem d| ≤ (d : ℝ) :=
            pairSieveS_abs_rem_le hc hz hdvd
          have hd0 : (0 : ℝ) ≤ (d : ℝ) := by positivity
          calc (3 : ℝ) ^ (ω d) * |(pairSieveS a c z Y t hz).rem d|
              ≤ (d : ℝ) ^ 2 * (d : ℝ) := by
                apply mul_le_mul h3 hrem (abs_nonneg _) (by positivity)
            _ = (d : ℝ) ^ 3 := by ring
            _ ≤ ((z : ℝ) ^ 2) ^ 3 := by
                apply pow_le_pow_left₀ hd0 h
        · exact le_refl 0
    _ = (#((divisors (twinProdPrimes (a * c) z)).filter
          (fun d : ℕ => (d : ℝ) ≤ ((z : ℕ) : ℝ) ^ 2)) : ℝ) * ((z : ℝ) ^ 2) ^ 3 := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((z : ℝ) ^ 2) * ((z : ℝ) ^ 2) ^ 3 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hsub : (divisors (twinProdPrimes (a * c) z)).filter
            (fun d : ℕ => (d : ℝ) ≤ ((z : ℕ) : ℝ) ^ 2) ⊆ Icc 1 (z ^ 2) := by
          intro d hd
          rw [mem_filter, Nat.mem_divisors] at hd
          rw [mem_Icc]
          constructor
          · exact Nat.pos_of_ne_zero fun hc =>
              hd.1.2 (by simpa [hc] using hd.1.1)
          · exact_mod_cast hd.2
        calc (#((divisors (twinProdPrimes (a * c) z)).filter
              (fun d : ℕ => (d : ℝ) ≤ ((z : ℕ) : ℝ) ^ 2)) : ℝ)
            ≤ (#(Icc 1 (z ^ 2)) : ℝ) := by
              exact_mod_cast Finset.card_le_card hsub
          _ = ((z : ℝ)) ^ 2 := by
              rw [Nat.card_Icc, Nat.add_sub_cancel]
              push_cast
              ring
    _ = ((z : ℕ) : ℝ) ^ 8 := by ring

set_option maxHeartbeats 1600000 in
/-- **The pair sieve upper bound** for intervals of length `t ≥ 2^64`. -/
theorem pair_type_bound_large (Y t a c : ℕ) (ha : 1 ≤ a) (hc : 1 ≤ c) (ht : 2 ^ 64 ≤ t) :
    ((#((Finset.Ico Y (Y + t)).filter (fun n => n.Prime ∧ (a * n + c).Prime))) : ℝ)
      ≤ 16416 * (((a * c : ℕ) : ℝ) / (Nat.totient (a * c))) ^ 2 * t / (Real.log t) ^ 2 := by
  have hm : 1 ≤ a * c := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  set t1 := t.sqrt with ht1
  set t2 := t1.sqrt with ht2
  set t3 := t2.sqrt with ht3
  set z := t3.sqrt with hzdef
  set w := z.sqrt with hwdef
  -- ℕ-level inequalities between the iterated square roots
  have b1 : t < (t1 + 1) ^ 2 := by
    simpa [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt' t
  have b2 : t1 < (t2 + 1) ^ 2 := by
    simpa [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt' t1
  have b3 : t2 < (t3 + 1) ^ 2 := by
    simpa [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt' t2
  have b4 : t3 < (z + 1) ^ 2 := by
    simpa [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt' t3
  have b5 : z < (w + 1) ^ 2 := by
    simpa [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt' z
  have sq1 : z ^ 2 ≤ t3 := Nat.sqrt_le' t3
  have sq2 : t3 ^ 2 ≤ t2 := Nat.sqrt_le' t2
  have sq3 : t2 ^ 2 ≤ t1 := Nat.sqrt_le' t1
  have sq0 : t1 ^ 2 ≤ t := Nat.sqrt_le' t
  have hwz : w ≤ z := Nat.sqrt_le_self z
  -- from here on the defining equations are no longer needed, and keeping
  -- the local definitions transparent makes `whnf`-heavy tactics time out
  clear_value w z t3 t2 t1
  have hC4 : t < (t2 + 1) ^ 4 := by
    calc t < (t1 + 1) ^ 2 := b1
      _ ≤ ((t2 + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left b2 2
      _ = (t2 + 1) ^ 4 := by ring
  have hB : t < (w + 1) ^ 32 := by
    calc t < (t2 + 1) ^ 4 := hC4
      _ ≤ ((t3 + 1) ^ 2) ^ 4 := Nat.pow_le_pow_left b3 4
      _ = (t3 + 1) ^ 8 := by ring
      _ ≤ ((z + 1) ^ 2) ^ 8 := Nat.pow_le_pow_left b4 8
      _ = (z + 1) ^ 16 := by ring
      _ ≤ ((w + 1) ^ 2) ^ 16 := Nat.pow_le_pow_left b5 16
      _ = (w + 1) ^ 32 := by ring
  have hw2 : 2 ≤ w := by
    by_contra hc
    have h1 : (w + 1) ^ 32 ≤ 2 ^ 32 := Nat.pow_le_pow_left (by omega) 32
    have h2 : (2 : ℕ) ^ 32 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    omega
  have hz1 : 1 ≤ z := by omega
  have ht2pos : 2 ≤ t := by
    have h2 : (2 : ℕ) ≤ 2 ^ 64 := by norm_num
    omega
  have hA : z ^ 8 ≤ t1 := by
    calc z ^ 8 = (z ^ 2) ^ 4 := by ring
      _ ≤ t3 ^ 4 := Nat.pow_le_pow_left sq1 4
      _ = (t3 ^ 2) ^ 2 := by ring
      _ ≤ t2 ^ 2 := Nat.pow_le_pow_left sq2 2
      _ ≤ t1 := sq3
  have hzt1 : z ≤ t1 := le_trans (Nat.le_self_pow (by norm_num) z) hA
  -- transfer everything needed to ℝ, in term mode (hypotheses containing
  -- `(x+1)^k` over ℕ send context-scanning tactics into `whnf` divergence)
  have hlog64 : Real.log t ≤ 64 * Real.log w := by
    calc Real.log t ≤ (32 : ℕ) * Real.log ((w : ℝ) + 1) :=
          log_le_mul_log_succ_of_lt_pow (by omega) hB
      _ ≤ (32 : ℕ) * (2 * Real.log w) :=
          mul_le_mul_of_nonneg_left (log_succ_le_two_log hw2) (by norm_num)
      _ = 64 * Real.log w := by push_cast; ring
  have hlog4t2 : Real.log t ≤ 4 * (t2 : ℝ) := by
    calc Real.log t ≤ (4 : ℕ) * Real.log ((t2 : ℝ) + 1) :=
          log_le_mul_log_succ_of_lt_pow (by omega) hC4
      _ ≤ (4 : ℕ) * (t2 : ℝ) :=
          mul_le_mul_of_nonneg_left (log_succ_le_self t2) (by norm_num)
      _ = 4 * (t2 : ℝ) := by push_cast; ring
  have hz8R : ((z : ℕ) : ℝ) ^ 8 ≤ (t1 : ℝ) := by exact_mod_cast hA
  have hzt1R : ((z : ℕ) : ℝ) ≤ (t1 : ℝ) := by exact_mod_cast hzt1
  have ht1tR : ((t1 : ℕ) : ℝ) ^ 2 ≤ (t : ℝ) := by exact_mod_cast sq0
  have ht2t1R : ((t2 : ℕ) : ℝ) ^ 2 ≤ (t1 : ℝ) := by exact_mod_cast sq3
  have htR : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht2pos
  -- discard the ℕ-power hypotheses
  clear b1 b2 b3 b4 b5 hC4 hB hA sq0 sq1 sq2 sq3 hwz hzt1 ht
  have hlogt_pos : 0 < Real.log t := Real.log_pos (by linarith)
  have hlog_sq : (Real.log t) ^ 2 ≤ 16 * (t1 : ℝ) := by
    have h1 : (Real.log t) ^ 2 ≤ (4 * (t2 : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hlogt_pos.le hlog4t2 2
    nlinarith [ht2t1R]
  -- apply the sieve
  have hcount := pair_count_le_siftedSum_add (Y := Y) (t := t) ha hc hz1
  have hsel := selberg_bound (pairSieveS a c z Y t hz1)
  have herr := pairSieveS_errSum_le (a := a) (c := c) (Y := Y) (t := t) hc hz1
  -- lower bound for the bounding sum
  set S := selbergBoundingSum (pairSieveS a c z Y t hz1) with hSdef
  have hSpos : 0 < S := selbergBoundingSum_pos _
  set γ : ℝ := (Nat.totient (a * c) : ℝ) / ((a * c : ℕ) : ℝ) * Real.log t / 128 with hγdef
  have hφm_pos : (0 : ℝ) < (Nat.totient (a * c) : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hm_pos : (0 : ℝ) < ((a * c : ℕ) : ℝ) := by exact_mod_cast hm
  have hγpos : 0 < γ := by
    rw [hγdef]
    positivity
  have hw1R : (1 : ℝ) ≤ (w : ℝ) := by exact_mod_cast (by omega : 1 ≤ w)
  have hlogw_nonneg : 0 ≤ Real.log w := Real.log_nonneg hw1R
  have h2m_pos : (0 : ℝ) < ((2 * (a * c) : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < 2 * (a * c))
  have hSγ : γ ^ 2 ≤ S := by
    have hβ := selbergBoundingSum_ge (t := t) (z := z) hm hz1
    rw [← pairSieveS_boundingSum_eq (Y := Y) hz1] at hβ
    rw [← hwdef] at hβ
    have hγβ : γ ≤ (Nat.totient (2 * (a * c)) : ℝ) / ((2 * (a * c) : ℕ) : ℝ) * Real.log (w : ℝ) := by
      have hfrac : (Nat.totient (a * c) : ℝ) / ((2 * (a * c) : ℕ) : ℝ)
          ≤ (Nat.totient (2 * (a * c)) : ℝ) / ((2 * (a * c) : ℕ) : ℝ) := by
        gcongr
        exact_mod_cast totient_le_totient_two_mul (a * c) hm
      have hlogw_ge : Real.log t / 64 ≤ Real.log w := by linarith
      calc γ = ((Nat.totient (a * c) : ℝ) / ((2 * (a * c) : ℕ) : ℝ)) * (Real.log t / 64) := by
            rw [hγdef]
            push_cast
            ring
        _ ≤ ((Nat.totient (2 * (a * c)) : ℝ) / ((2 * (a * c) : ℕ) : ℝ)) * Real.log w := by
            apply mul_le_mul hfrac hlogw_ge (by positivity) (by positivity)
    exact le_trans (pow_le_pow_left₀ hγpos.le hγβ 2) hβ
  -- combine the main term
  have hupper : (pairSieveS a c z Y t hz1).siftedSum
      ≤ (t : ℝ) / S + ((z : ℕ) : ℝ) ^ 8 :=
    le_trans hsel (add_le_add (le_of_eq rfl) herr)
  have hmain : (t : ℝ) / S ≤ (t : ℝ) / γ ^ 2 := by
    gcongr
  have hγident : (t : ℝ) / γ ^ 2
      = 16384 * (((a * c : ℕ) : ℝ) / (Nat.totient (a * c))) ^ 2 * t / (Real.log t) ^ 2 := by
    rw [hγdef]
    field_simp
    ring
  have hmain' : (t : ℝ) / S
      ≤ 16384 * (((a * c : ℕ) : ℝ) / (Nat.totient (a * c))) ^ 2 * t / (Real.log t) ^ 2 :=
    hγident ▸ hmain
  -- combine the error and small-prime terms
  have ht1_nonneg : (0 : ℝ) ≤ (t1 : ℝ) := by positivity
  have h2t1 : 2 * (t1 : ℝ)
      ≤ 32 * (((a * c : ℕ) : ℝ) / (Nat.totient (a * c))) ^ 2 * t / (Real.log t) ^ 2 := by
    have hX1 : (1 : ℝ) ≤ (((a * c : ℕ) : ℝ) / (Nat.totient (a * c))) ^ 2 := by
      have h1 : (Nat.totient (a * c) : ℝ) ≤ ((a * c : ℕ) : ℝ) := by exact_mod_cast Nat.totient_le (a * c)
      have h2 : (1 : ℝ) ≤ ((a * c : ℕ) : ℝ) / (Nat.totient (a * c)) := (one_le_div hφm_pos).mpr h1
      nlinarith
    have hstep : 2 * (t1 : ℝ) ≤ 32 * t / (Real.log t) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hlog_sq
        (by positivity : (0 : ℝ) ≤ 2 * (t1 : ℝ)), ht1tR]
    calc 2 * (t1 : ℝ) ≤ 32 * t / (Real.log t) ^ 2 := hstep
      _ ≤ 32 * (((a * c : ℕ) : ℝ) / (Nat.totient (a * c))) ^ 2 * t / (Real.log t) ^ 2 := by
          gcongr ?_ / _
          nlinarith [hX1, (by positivity : (0 : ℝ) ≤ (t : ℝ))]
  -- final assembly
  calc ((#((Finset.Ico Y (Y + t)).filter (fun n => n.Prime ∧ (a * n + c).Prime))) : ℝ)
      ≤ (pairSieveS a c z Y t hz1).siftedSum + z := hcount
    _ ≤ ((t : ℝ) / S + ((z : ℕ) : ℝ) ^ 8) + z := by linarith [hupper]
    _ ≤ (t : ℝ) / S + 2 * (t1 : ℝ) := by linarith [hz8R, hzt1R]
    _ ≤ 16384 * (((a * c : ℕ) : ℝ) / (Nat.totient (a * c))) ^ 2 * t / (Real.log t) ^ 2
          + 32 * (((a * c : ℕ) : ℝ) / (Nat.totient (a * c))) ^ 2 * t / (Real.log t) ^ 2 := by
        linarith [hmain', h2t1]
    _ = 16416 * (((a * c : ℕ) : ℝ) / (Nat.totient (a * c))) ^ 2 * t / (Real.log t) ^ 2 := by
        ring


end

end PPF.Sieve
