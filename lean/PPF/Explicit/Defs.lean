import PPF.Tree

/-!
# Explicit bound: frozen constants

All numerals of the explicit RH-conditional upper bound
(mirrored by `scripts/explicit_bound.py`).

* `cE = 1/log 2` — the hazard constant;
* `epsE = 1/100`, `thetaE = 2^{-32}` — block accuracy and the short/long gap split;
* `C5 = 4·16416·e³/log² 2` — short-gap constant (pair sieve 16416, totient `e³`);
* `CT = 5·10^18` — explicit Selberg constant (discrete θ-form, `X ≥ 100`, `log² X ≤ h ≤ X`);
* `C4 = 64·CT·log³ 2/ε³` — bad-block constant;
* `etaE`, `eE`, `gE` — coefficients of the recurrence (`PPF.cond_rec_step` shape);
* `J = 2^44` — the recurrence holds for `j ≥ J`.
-/

namespace PPF.Explicit

noncomputable def cE : ℝ := 1 / Real.log 2
noncomputable def epsE : ℝ := 1 / 100
noncomputable def thetaE : ℝ := 1 / 2 ^ 32
noncomputable def C5 : ℝ := 4 * 16416 * Real.exp 3 / Real.log 2 ^ 2
noncomputable def CT : ℝ := 5 * 10 ^ 18
noncomputable def C4 : ℝ := 64 * CT * Real.log 2 ^ 3 / epsE ^ 3
noncomputable def etaE : ℝ := 2 * cE * epsE + 5 * C5 * thetaE
noncomputable def eE (j : ℕ) : ℝ := (2 * cE + 5 * C5) / (j : ℝ) ^ 2
noncomputable def gE (j : ℕ) : ℝ := (cE + 2) * C4 * (j : ℝ) ^ 3 * ((2 : ℝ) ^ (-thetaE)) ^ j
def J : ℕ := 2 ^ 44

end PPF.Explicit
