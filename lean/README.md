# Prime-prefix-free numbers: convergence of the reciprocal sum under RH

A Lean 4 / Mathlib proof that, assuming the Riemann Hypothesis, the reciprocals of
OEIS A287117 have a finite sum, and that the sum is less than `4.5·10^14`. A287117 consists of the integers with no odd prime
among their proper binary prefixes `⌊n/2^k⌋`, `k ≥ 1`.

```lean
def PrimePrefixFree (n : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ¬ ((n / 2 ^ k).Prime ∧ n / 2 ^ k ≠ 2)

open Classical in
theorem ppf_hasSum_of_RH (hRH : RiemannHypothesis) :
    ∃ s : ℝ, HasSum (fun n : ℕ => if PrimePrefixFree n then (1 : ℝ) / n else 0) s ∧
      s ≤ 4.5 * 10 ^ 14
```

`PPF/Main.lean` contains exactly this definition and theorem, so it can be read on its
own: every other name in the statement is Mathlib's, including `RiemannHypothesis`.
The development uses an identical copy, `PPF.PrimePrefixFree`, and the main proof
identifies the two by `Iff.rfl`. `#print axioms ppf_hasSum_of_RH` reports
`[propext, Classical.choice, Quot.sound]`. `HasSum` says the series converges to `s`; a
bound on `∑'` alone would not, since Mathlib defines the sum of a divergent series to
be `0`.

`PPF/TreeTest.lean` checks the definition against the first 61 terms of A287117. It
proves, by `decide +kernel`, that the numbers in `[1, 535]` with the property are
exactly those terms.

## Proof outline

Let `r m` be the fraction of level `[2^m, 2^{m+1})` that is prime-prefix-free. The
sum is at most `Σ r m`, and `r (m+1) = r m − #(odd primes at level m)/2^m`. The core
argument is a lower bound on the primes that survive to level `j`. It yields the
delayed recurrence

`r (j+1) ≤ r j (1 − c/j) + (η/j + e j) · r ⌊j/3⌋ + g j`, with `c = 1/log 2`.

The bootstrap turns this into `r j ≪ j^{−6/5}`. The margin comes from `1/log 2 > 1`.

Two analytic inputs enter the recurrence.

* **`SelbergMeanSquare`**: primes in almost all short intervals. For each `θ > 0`,
  the mean square over `n ∈ [X, 2X)` of `θ(n+h) − θ(n) − h` is at most `C h X log² X`
  for windows `X^θ ≤ h ≤ √X`. It is used to count the blocks
  `[M 2^b, (M+1) 2^b)` whose prime count deviates from `2^b/(j log 2)`.
* **`PairSieve`**: a Selberg upper-bound sieve for prime pairs `n, an + t` in an
  arbitrary interval. It controls the primes that have a prime ancestor a few
  levels up.

`pairSieve` proves `PairSieve` unconditionally. `selbergMeanSquare_of_RH` proves
`SelbergMeanSquare` from RH. That proof uses:

* an explicit formula for ψ with the contour moved to `Re s = −1/2`;
* reflection of `ζ′/ζ` through the functional equation, with a digamma bound;
* Selberg's mean-square computation with a polynomial weight.

## Layers

| theorem | hypotheses | file |
|---|---|---|
| `summable_of_inputs` | `SelbergMeanSquare`, `PairSieve` | `PPF/Conditional.lean` |
| `pairSieve` | none | `PPF/Sieve.lean`, `PPF/Sieve/Pair.lean` |
| `selbergMeanSquare_of_RH` | `RiemannHypothesis` | `PPF/Selberg.lean`, `PPF/RH/*` |
| `PPF.Explicit.tsum_le_of_RH` | `RiemannHypothesis` | `PPF/Explicit/*` |
| `ppf_hasSum_of_RH` | `RiemannHypothesis` | `PPF/Main.lean` (self-contained statement) |

## Files

| file | contents |
|---|---|
| `PPF/Interfaces.lean` | `PrimePrefixFree`, `SelbergMeanSquare`, `PairSieve` |
| `PPF/Tree.lean` | levels; the sets `S`, `P`, `r`; the recursion; the counting inequality; summability transfer |
| `PPF/Blocks.lean` | bad-block count from `SelbergMeanSquare` (shifting argument); prime counts in good blocks |
| `PPF/ShortGaps.lean` | short-gap bound from `PairSieve`; mean value of `(t/φ t)²` |
| `PPF/Bootstrap.lean` | the delayed recurrence implies summability |
| `PPF/Conditional.lean` | the recurrence, assembled |
| `PPF/Sieve/Pair.lean` | Selberg sieve for `n(an+c)` on `[Y, Y+H)` |
| `PPF/RH/ZeroCount.lean` | zeros in unit windows ≪ log, and `N(T) ≪ T log T` |
| `PPF/RH/Digamma.lean` | `‖ψ(w)‖ ≪ log |Im w|` on `1/2 ≤ Re w ≤ 2` |
| `PPF/RH/Reflection.lean` | `ζ′/ζ(1−w) + ζ′/ζ(w) ≪ log`; `ζ′/ζ` on `Re s = −1/2` |
| `PPF/RH/GoodHeights.lean` | a height `t ∈ [T, T+1]` where `ζ′/ζ ≪ log² T` for every `σ ∈ [−1/2, 2]` |
| `PPF/RH/Residue.lean` | residue theorem for `−ζ′/ζ · y^s/s` on `[−1/2, c] × [−t, t]` |
| `PPF/RH/ExplicitFormula.lean` | truncated explicit formula with error `y log²(Ty)/T + log²(Ty)` |
| `PPF/RH/Kernel.lean`, `PPF/RH/ZeroSums.lean` | weighted Mellin kernel `≪ X^{α+1}/(1+τ²)`; double sums over zeros |
| `PPF/RH/MeanSquare.lean` | mean square of the zero sum `≪ h X log² X` |
| `PPF/RH/Windows.lean` | from ψ to θ and from integrals to sums; assembly of `SelbergMeanSquare` |
| `PPF/Explicit/*` | the explicit bound: every constant of the RH chain made numeric (explicit formula `1.3·10^7`, Selberg mean square `5·10^18`, sieve `16416`), the recurrence for `j ≥ 2^44` with `θ = 2^{-32}`, and the bootstrap `r_j ≤ 3(2^55+1) j^{-5/4}` |
| `PPF/Vendor/*` | verbatim copies from [jdb19937/carmichael](https://github.com/jdb19937/carmichael) (`lean/Carmichael/`): `SelbergBound`, `TwinSieve`, `TotientSum`, `TotientSumSq`, `PerronKernel`, `LGrowth`, `ZeroCount`, `PartialFractions`, `ExplicitFormula` |

## Verify

```
make verify
```

This runs `lake build`, then `AxiomCheck.lean`. The `#guard_msgs` blocks there fail
unless the main theorem and the four layer theorems (`summable_of_inputs`, `pairSieve`,
`selbergMeanSquare_of_RH`, `PPF.Explicit.tsum_le_of_RH`) depend only on the three
standard axioms. Then it
runs `PPF/TreeTest.lean`. Last, `scripts/ReplayClosure.lean` collects every constant
the main theorem depends on (about 64,000, including Mathlib and Lean core) and
replays them through the kernel into an empty environment. This independent
re-check does not trust the build's compiled files or elaboration-time options.

Pinned versions: Lean `v4.33.1`, Mathlib `v4.33.1`, the same as
[jdb19937/carmichael](https://github.com/jdb19937/carmichael).
