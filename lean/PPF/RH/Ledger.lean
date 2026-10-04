import PPF.RH.Windows

/-!
# Phase 5 ledger: `RiemannHypothesis → SelbergMeanSquare`

Route: explicit formula with the contour pushed to `Re s = −1/2`, then Selberg's
mean-square computation with a polynomial weight. Every item is a theorem in
namespace `PPF.RH`, stated in its own file so items can be proved in parallel.

| item | file | statement | depends on |
|---|---|---|---|
| finiteness, membership, `Re ρ = 1/2` | `ZeroCount` | `zetaZeros_finite`, `mem_zetaZeros`, `re_eq_half_of_mem` | vendored `ZeroCount`/`ExplicitFormula` |
| K2 | `ZeroCount` | `sum_mult_window_le`, `sum_mult_le` | vendored `sum_ord_etaFun_disk_le` |
| D1 | `Digamma` | `norm_digamma_le` | Mathlib `GammaSeq` |
| D2, D3 | `Reflection` | `norm_logDeriv_zeta_reflect_le`, `left_line_bound` | D1, `riemannZeta_one_sub` |
| D4 | `GoodHeights` | `riemannZeta_conj`, `deriv_riemannZeta_conj`, `exists_good_height_zeta` | D2, vendored `exists_good_height` |
| RT | `Residue` | `rectInt_logDeriv_zeta` | vendored `PerronKernel` |
| E3 | `ExplicitFormula` | `explicit_formula_RH` | RT, D3, D4, K2, vendored Perron lemmas |
| K1 | `Kernel` | `one_le_bump`, `norm_integral_bump_cpow_le` | — |
| K3 | `ZeroSums` | `sum_low_pairs_le`, `sum_high_pairs_le` | K2 |
| K4 | `MeanSquare` | `mean_square_zero_sum_le` | K1, K3 |
| B1–B3, assembly | `Windows` | `sum_eq_integral_theta`, `integral_psi_sub_theta_sq_le`, `integral_psi_window_sq_le`, `selbergMeanSquare_assembly` | E3, K4 |

`PPF.selbergMeanSquare_of_RH` (`PPF/Selberg.lean`) is `selbergMeanSquare_assembly`.
-/
