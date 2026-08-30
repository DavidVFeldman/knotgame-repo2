# CENSUS — round 15 (T43, T44, T45)

Census first, as the commission requires: what was in the tree when round 15 was
picked up, and what round 15 adds.

## 1. Inherited and reused

| Inherited identifier | Module | Used by round 15 for |
| --- | --- | --- |
| `KnotGame.r`, `KnotGame.g`, `KnotGame.r_pos`, `KnotGame.r_lt_one` | `Basic` | the branch constants throughout |
| `KnotGame.survives`, `branch`, `act`, `survivesWord`, `posAfter` | `Basic` | the move side of T44 |
| `CountingOperator.branchLegal`, `branchSurvivesWord` | `CountingOperator` | the branch side of T44 |
| `ExpCount.rapp`, `rapp_cons` | `ExpCount` | the endpoint of a branch word (T44) |
| `KnotGame.KindDense` | `Density` | the hypothesis converted in T44 |
| `BackwardClosure.DenseFrom`, `denseFrom_half_imp_kindDense` | `BackwardClosure` | the inclusion T44 converses |
| `Contraction.P`, `LipBound`, `lipBound_P`, `lipBound_iterate`, `tendsto_const`, `lipschitzWith_of_lipBound` | `Contraction` | T43 and T45 |
| `EquiMean.BddMeas`, `EquiMean.S`, `equidistribution_in_mean` | `EquiMean` | the T45 corollary |

Confirmed by census before starting T45: **no invariant measure exists anywhere
in the tree**.  `FourierFloor.lean` records in its own scruples that `ν_r` is
not constructed, and `Contraction.lean` (round 14) says the same in its header.
`Trapezoid.lean` has a `bval` at `λ = √2` only, defined from an abstract digit
sequence `ε : ℕ → Fin 2` rather than from a point of `(0,1]`; it is a different
object from `InvariantMeasure.bval` and neither is used by the other.

Mathlib census for T45 (at this toolchain, mathlib `v4.28.0`):

* `MeasureTheory.Measure.infinitePi` **does** exist (`Mathlib/Probability/
  ProductMeasure.lean`, built on Ionescu–Tulcea), with `infinitePi_pi`,
  `eq_infinitePi`, `integral_restrict_infinitePi`.  What it does **not** provide
  at this version is a ready factorisation of the product over `ℕ` into the
  first coordinate and the shift, which is precisely the step the suggested
  route needs.
* The route actually taken needs only: `Int.fract`, `measurable_fract`,
  `Int.fract_sub_intCast`, `Int.fract_eq_self`, `summable_geometric_of_lt_one`,
  `Summable.tsum_eq_zero_add`, `measurable_of_tendsto_metrizable`,
  `MeasureTheory.integral_map`, `Integrable.of_bound`, and the interval-integral
  change-of-variables lemmas `intervalIntegral.integral_comp_mul_left`,
  `integral_comp_sub_right`, `integral_add_adjacent_intervals`,
  `integral_congr_ae`.  All are present.

No inherited definition was changed.  The edits to inherited files are: the
round-14 statement in `Contraction.lean` renamed and re-derived (T43, below),
one added import in `RequestProject/All.lean`, and one module name added to the
CI list in `.github/workflows/ci.yml`.

## 2. T43 — `RequestProject/Contraction.lean`

| Statement | Content |
| --- | --- |
| `continuous_of_lipBound` | a `LipBound` is a `LipschitzWith`, hence continuous |
| `abs_le_of_lipBound_on_Icc` | `|h y| ≤ |h(1/2)| + K` on `[0,1]` |
| `integrable_of_lipBound` | **(a)** a Lipschitz function is integrable against any probability measure carried by `[0,1]` |
| `integrable_iterate` | hence so is every `P^[m] h`: the old `hint` is derivable |
| `Lip`, `InvariantOn` | **(b)** the test class and the one-step invariance hypothesis |
| `integral_iterate_eq` | one-step invariance ⟹ `∫ P^[m] h dν = ∫ h dν` |
| `const_eq_integral_of_iterate_invariant` | round 14's statement, kept verbatim as the general form |
| `const_eq_integral_of_invariant` | the same conclusion from `hsupp` and `InvariantOn` alone |
| `integral_eq_of_invariant` | two invariant measures carried by `[0,1]` integrate every Lipschitz function alike |
| `tendsto_integral_of_invariant` | the packaged form: `P^[m] h → ∫ h dν` uniformly on `[0,1]` at rate `r^m` |

`EquiMean.equidistribution_in_mean` compiles unchanged: it never called
`const_eq_integral_of_invariant`, it takes the constant `c` and its estimate
`hc` as hypotheses, and both are untouched.

## 3. T44 — `RequestProject/BackwardClosure.lean`

| Statement | Content |
| --- | --- |
| `branchLegal_branch` | the step lemma: `survives lam m x → branchLegal lam (branch lam m x) x` |
| `branchWordOf` | the branch word taken by a knot at `x` along a move word |
| `rapp_branchWordOf` | it has the same endpoint (`act = f ∘ branch` definitionally) |
| `branchSurvivesWord_branchWordOf` | it is legal whenever the move word is survived |
| `kindDense_imp_denseFrom_half` | **T44** |
| `denseFrom_half_iff_kindDense` | the biconditional, with `1 < lam` |

## 4. T45 — `RequestProject/InvariantMeasure.lean` (new)

| Statement | Content |
| --- | --- |
| `digit`, `measurable_digit`, `digit_shift` | the binary digits and the shift `digit j (fract 2t) = digit (j+1) t` |
| `bval` | `(1-r) ∑' j, digit j t · r^j`, with `summable_digit`, `bval_mem_Icc`, `measurable_bval` |
| `bval_rec` | the self-similarity `bval t = (1-r)·digit₀ t + r·bval (fract 2t)` |
| `bval_of_lt_half`, `bval_of_half_le` | its two branch forms on `[0,1/2)` and `[1/2,1)` |
| `nu` | `map bval (volume.restrict (Ioc 0 1))` — the law of the digit series under a uniform point of `(0,1]` |
| `isProbabilityMeasure_nu`, `nu_compl_Icc` | a probability measure carried by `[0,1]` |
| `integral_nu` | `∫ ψ dν = ∫₀¹ ψ(bval t) dt` |
| `invariantOn_nu` | **T45**: `nu` satisfies `Contraction.InvariantOn` |
| `const_eq_integral_nu`, `tendsto_integral_nu` | the T43 hypotheses discharged |
| `equidistribution_in_mean_nu` | `EquiMean.equidistribution_in_mean` with its constant identified as `∫ k dν` |

The stopping rule of the commission was not reached: the module is 340 lines and
needs no product-measure layer.  What replaces the factorisation of a product
measure is the change of variables `s = 2t` on the two halves of `(0,1]`; see
`SCRUPLES-round15.md` §4 for the route and §6 for the exact limit of what the
construction certifies (in particular, `nu` is not identified with any measure
named elsewhere in the project or in the literature).
