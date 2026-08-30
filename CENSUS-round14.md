# CENSUS — round 14 (T39.5, T40, T41, T42)

Census first, as the commission requires: what was already in the tree when
round 14 was picked up, and what round 14 adds.

## 1. Inherited and reused verbatim

| Inherited identifier | Module | Used by round 14 for |
| --- | --- | --- |
| `KnotGame.r`, `KnotGame.g`, `KnotGame.f` | `Basic` | the branch maps and the window endpoints |
| `CountingOperator.T`, `T_one` | `CountingOperator` | the operator normalised by `P = (λ/2)T` (T40) |
| `CountingOperator.branchLegal`, `branchSurvivesWord`, `branchWords`, `branchWords_succ` | `CountingOperator` | the branch alphabet of T41(b) |
| `CountingOperator.integral_Ioo_comp_affine`, `integral_Ioo_comp_mul`, `integral_indicator_Iio`, `integral_indicator_Ioi` | `CountingOperator` | the change of variables and the two indicator splits in T41(a) |
| `ExpCount.rapp`, `rapp_cons`, `rapp_append`, `SW` | `ExpCount` | the action of a branch word (T41(b), T42) |
| `Branching.BLegal`, `bSurvives`, `Pisot.branchIter` | `BranchingCount`, `Pisot` | the two further copies bridged by T39.5 |
| `KnotGame.KindDense`, `N_unbounded_of_kindDense` | `Density` | the conclusion of T42(c) |

No inherited definition was changed and no inherited statement re-derived.  The
only edits to inherited files are four added imports in `RequestProject/All.lean`
and four module names added to the CI list in `.github/workflows/ci.yml`.

## 2. Round-14 modules and their contents

### T39.5 — `RequestProject/BranchBridge.lean`

The census finding of the commission is confirmed: the branch-word layer existed
three times, in modules with disjoint import paths.  The bridge is short, as the
commission hoped, and introduces no fourth copy:

| Statement | Content |
| --- | --- |
| `branchLegal_iff_BLegal` | the two legality predicates agree |
| `branchSurvivesWord_iff_bSurvives` | the two word-survival predicates agree |
| `rapp_eq_branchIter` | the two word actions agree |
| `branchIter_append`, `branchSurvivesWord_append` | the append laws on the operator side |
| `branchWords_eq_SW`, `bcount_eq_Kx` | the two counting layers agree, so `integral_bcount` is a statement about `ExpCount.Kx` |

### T40 — `RequestProject/Contraction.lean`

| Statement | Content |
| --- | --- |
| `P` | `(P h)(y) = ½[h(ry) + h(ry + 1 − r)]`, `r = 1/λ` |
| `P_one` | (a) `P 1 = 1` |
| `P_eq_smul_T` | `P = (λ/2)·T`, the normalisation by the eigenvalue of `T_one` |
| `lipschitz_contraction` | (b) `LipschitzWith K h → LipschitzWith (r·K) (P h)` |
| `lipschitz_contraction_iterate` | the same for `P^[m]`, with constant `r^m·K` |
| `tendsto_const` | (c) `P^[m] h` is within `2K r^m/(1−r)` of a constant on `[0,1]` |
| `tendstoUniformlyOn_const` | the same as `TendstoUniformlyOn` on `[0,1]` |
| `const_eq_integral_of_invariant` | the identification of the constant, from an explicit invariance hypothesis |

### T41 — `RequestProject/EquiMean.lean`

| Statement | Content |
| --- | --- |
| `S` | `(S h)(x) = h(λx)[x < r] + h(λx − (λ−1))[x > g]` |
| `adjoint` | (a) `∫₀¹ (S h) k = ∫₀¹ h (T k)` |
| `endpoint_propagator` | (b) `(S^[m] h)(x) = ∑_{ε ∈ branchWords λ x m} h(Φ_ε(x))` |
| `iterate_P_eq` | `P^[m] = (λ/2)^m · T^[m]` |
| `equidistribution_in_mean` | (c) `(λ/2)^m ∫₀¹ (S^m h) k → (∫₀¹ h)·c` |

### T42 — `RequestProject/BackwardClosure.lean`

| Statement | Content |
| --- | --- |
| `toMove`, `survivesWord_map_toMove`, `posAfter_map_toMove` | branch words realised as `M`-free move words |
| `denseFrom_half_imp_kindDense` | (c) `DenseFrom λ (1/2) → KindDense λ` |
| `N_unbounded_of_denseFrom_half` | density of the branch endpoints from `1/2` alone gives `N_λ = ∞` |
| `endpoints_subset_of_legal` | the prepending lemma for endpoint sets |
| `denseFrom_of_image`, `mem_D_of_image_mem_D`, `compl_D_forward_invariant` | backward closure of `D`, forward invariance of its complement |
| `N_unbounded_of_orbit_point_denseFrom` | one point of the forward orbit of `1/2` in `D` suffices |

## 3. What round 14 does not do

* The invariant measure `ν_r` of the IFS `{ry, ry + 1 − r}` is still nowhere
  constructed; the identification of the limit constant with `∫ h dν_r` is a
  hypothesis in both T40 and T41, exactly as the commission directs.
* The pointwise upgrade at `x = 1/2` (paper Question 50) is not attempted, and
  no weakened variant of it appears.
* Nothing listed in `UNBUILT.md` was touched.
