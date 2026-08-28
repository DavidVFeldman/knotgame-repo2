# CENSUS — round 4 (T11, T12, T13)

Census-first, as the commission requires: what the round-3 tree in the tarball
already contained, what round 4 reuses, and what is new.

## 1. What was inherited (ground truth: the round-3 tree)

The round-3 tree was rebuilt in place before any new work; it builds, and the
semantic axiom audit passes (524 theorems at the moment of inheritance).  No
round-1/2/3 definition was changed and no round-1/2/3 statement re-derived.
The only edit to an inherited file is four added imports in
`RequestProject/All.lean`.

| Item reused by round 4 | Identifier | File |
| --- | --- | --- |
| the branch maps `f 0 x = λx`, `f 1 x = λx−(λ−1)` | `KnotGame.f`, `f_zero`, `f_one` | `Basic.lean` |
| `r = λ⁻¹`, `g = 1 − r`, and `r_pos`, `r_lt_one`, `g_pos`, `g_lt_one` | `KnotGame.r`, `KnotGame.g` | `Basic.lean` |
| δ-transversality on `[1/2, 667/1000]` (T9) | `KnotGame.Transversality.transversality` | `Transversality.lean` |
| the class functions `gval`, `gder` | `KnotGame.Transversality.gval`, `gder` | `TransversalityBounds.lean` |
| the semantic axiom audit | `KnotGame.Audit` | `AxiomAudit.lean` |

**One finding, reported rather than repaired.**  The commission asks to "reuse
the existing branch maps and survival predicates; do not re-derive".  The branch
maps are there and are reused verbatim.  A *survival predicate for branch
words* is not: the round-3 tree has `survives`/`survivesWord` for words in the
three **moves** `L, M, R` (`Basic.lean`), and `branchIter` for iterating branch
maps along an itinerary (`Pisot.lean`), but nothing that says "this branch is
legal at this point".  Round 4 therefore introduces the two-line predicate
`Branching.BLegal` (branch `0` legal iff `x < r`, branch `1` legal iff `x > g`,
exactly the commission's convention) and builds `Surviving`, `SurvivesUpTo` and
`bSurvives` on top of it.  Nothing inherited was duplicated.

## 2. T11 — the two branching lemmas (`RequestProject/Branching.lean`)

| Claim of the commission | Identifier |
| --- | --- |
| the window `(g, r)`, both branches legal there | `Window`, `BLegal_of_mem_Window` |
| exactly one branch legal outside; `g + r = 1`, midpoint `1/2` | `cb_of_le_g`, `cb_of_r_le`, `g_add_r`, `mid_eq_half` |
| **T11a** from `x ≤ g`: `λx < r` | `no_jump_low` |
| **T11a** from `x ≥ r`: `λx − (λ−1) > g` | `no_jump_high` |
| "each crossing inequality is equivalent to `λ² ≥ λ+1`" | `lam_mul_g_lt_r_iff`, `no_jump_high_iff` |
| a forced step from below stays in `(0,g]` or lands in the window | `forced_low_dichotomy` |
| **T11b** `{1/(λ+1), λ/(λ+1)}` is a 2-cycle outside the window, forced | `sharp_two_cycle` |
| **T11c** `η = min(λ₀−1, (2−λ₁)/2)` | `eta` |
| **T11c** child in `(λ−1, λ/2]` below the midpoint | `good_child_low` |
| **T11c** child in `[(2−λ)/2, 2−λ)` above it, and `2−λ < r` | `good_child_high`, `two_sub_lt_r` |
| **T11c** the selected child has distance `≥ η` from `{0,1}` | `good_child` |
| **T11d** bounded return from `[η, g]` under branch `0` | `bounded_return_low` |
| **T11d** bounded return from `[r, 1−η]` under branch `1` | `bounded_return_high` |
| the anchor data `η = 1/5`, `g(λ₁) = 3/8`, `B = 3` | `CommonWindow.eta_anchor`, `g_lamHi`, `return_bound_anchor` |

Auxiliary, also new: `iterate_f_zero`, `iterate_f_one` (the two forced orbits in
closed form), `g_mono`, `sq_lt_of_le`, `lt_two_of_sq_lt`, `one_sub_mem_Window`
(the window is symmetric about `1/2`), `half_mem_Window`, `f_mem_Ioo`,
`cb`/`cb_legal` (the canonical "good child" selector, which is the forced branch
outside the window).

## 3. T12a — the continuum (`RequestProject/BranchingContinuum.lean`)

| Claim of the commission | Identifier |
| --- | --- |
| infinite itineraries and their orbits | `itinOrbit`, `Surviving` |
| the bit-driven construction ("read a bit at each window visit") | `bitBranch`, `bitState`, `theta` |
| the itineraries produced survive forever | `theta_surviving` |
| the map is injective | `theta_injective` |
| **T12a**: `Function.Injective` into the survival itineraries of `1/2` | `continuum_of_survival_itineraries` |

Supporting: `forced_low_iterates`, `forced_high_iterates` (the forced orbit
cannot avoid the window forever), `exists_window_ge`, `bitState_snd_unbounded`,
`exists_window_index` (every bit index is actually consumed at some window
visit), `bitState_eq_of_theta_eq`.

## 4. T12b — the linear count (`RequestProject/BranchingCount.lean`)

| Claim of the commission | Identifier |
| --- | --- |
| the spine (always take the good child) | `cstep`, `spine` |
| the spine returns to the window within `B+1` steps | `spine_return` |
| the visit times, with gaps `≤ B+1` | `nextVisit`, `visit`, `visit_props`, `visit_strictMono` |
| the word that deviates from the spine at one visit | `devOrbit`, `devItin`, `devWord`, `devOrbit_legal` |
| `K_m` = number of length-`m` branch words along which `1/2` survives | `SurvivesUpTo`, `K`, and `bSurvives` / `K_eq_card_bSurvives` |
| **T12b**: `K_m ≥ m/(B+1)` | `K_ge` |

## 5. T13 — the common window (`RequestProject/CommonWindow.lean`)

`CommonWindow.common_window` is the single citable identifier the commission
asks for.  For `λ ∈ [1000/667, 8/5]` it asserts, in one conjunction:

* (a) `1/λ ∈ [5/8, 667/1000] ⊆ [1/2, 667/1000]`, **and** the instantiated
  round-3 conclusion: every `{−1,0,1}` class function with constant term `1`
  that is `1/1000`-small at `1/λ` has termwise derivative `< −1/1000` there;
* (b) `1 < λ < 2` and `λ² < λ + 1`, so all of T11 applies;
* (c) `1000/667 ≤ 3/2 ≤ 8/5`, and `1/2 ∈ (g, r)` for every such `λ`;
* T12a: a continuum of survival itineraries of `1/2`;
* T12b with the anchor data `η = 1/5`, `B = 3`: `m/4 ≤ K λ m` for every `m`.

## 6. Not commissioned, not attempted

The geometric tail bound `P(S > t) ≤ C λ₀^(−t)` for the discarded child, the
renewal inequality, and the integrated exponential lower bound are marked open
in the note and are explicitly excluded by the commission.  They are absent from
the tree, and no weakened variant of them appears anywhere in round 4.
