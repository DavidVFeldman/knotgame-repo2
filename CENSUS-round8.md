# CENSUS — round 8 (T22–T26)

Census-first, as in the earlier rounds: what the inherited tree already
contained, what round 8 reuses, what round 8 adds, and — as the commission
explicitly asks — an audit of the items the commission flags as "may be partly
present".

## 0. Summary of outcomes

| Target | Status |
| --- | --- |
| T22a `prop:ternary` | **done** — `RequestProject/Ternary.lean` |
| T22b `prop:base32` | **done** — `RequestProject/Mahler.lean` |
| T22c `prop:mahler` | **done** — `RequestProject/Mahler.lean` |
| T22d `prop:translation` (optional) | **done** — `RequestProject/Translation.lean` |
| T23 `prop:kindyield` | **done** — `RequestProject/PeriodicYield.lean` |
| T24a cylinder count at 3/2 | **done** — `RequestProject/KindTree.lean` |
| T24b cylinder count at φ | **done** — `RequestProject/KindTree.lean` |
| T24c Hausdorff/box dimension (optional) | **not attempted**; see SCRUPLES-round8 §4 |
| T25 sharpness of the transversality window | **done** — `RequestProject/WindowSharp.lean` |
| T26 quantitative density criterion (optional) | **done** — `RequestProject/DensityQuant.lean` |

No `sorry`, no `admit`, no new `axiom`, no `native_decide`.  The semantic axiom
audit passes over the whole tree.

## 1. The commissioned audit of what was already present

The commission asks for these to be audited before any new work.  They were
rebuilt in place and read; all are genuine and all are used or deliberately
left alone.

| Claimed item | Identifier(s) | File | Finding |
| --- | --- | --- | --- |
| Littlewood-type obstruction | `KnotGame.littlewood` | `Littlewood.lean` | present and proved |
| no return of `1/2` to itself | `KnotGame.no_return_to_half` | `Littlewood.lean` | present and proved; it is a statement about *exact return of the point `1/2`*, and it does **not** exclude periodic kind words — see T23 below |
| kind-sequence unboundedness | `KnotGame.Kind`, `KnotGame.N_unbounded_of_kind` | `Littlewood.lean` | present and proved, in the **infinite-sequence** form |
| binary-square reformulation at `√2` | `KnotGame.posAfter_blocks` | `Sqrt2.lean` | present and proved |
| plastic-number configuration closure | `N_rho_le_seven`, `d_rho_four`, `d_rho_seven`, `card_reachable_configs` (= 25 525) | `PlasticConfig.lean` | present and proved; the closure round 1 had reported infeasible is in fact certified |
| compactness theorem (`thm:compactness`) | `KnotGame.InfinitelyManyKnots`, `infinitelyManyKnots_iff_annihilations`, `boundedAgeWitnesses_of_infinitelyManyKnots`, `infinitelyManyKnots_of_boundedAgeWitnesses`, `N_unbounded_of_infinitelyManyKnots` — all three conditions | `Compactness.lean` | present and proved; round 8's T23 lands on condition (i) |
| topological density criterion | `KnotGame.infinitelyManyKnots_of_kindDense`, `N_unbounded_of_kindDense` | `Density.lean` | present and proved; round 8's T26 strengthens the hypothesis, not the file |
| δ-transversality window `[1/2, 667/1000]` | the round-3 certificate | `Transversality*.lean` | present and proved; round 8's T25 is its negative control |
| the five-point golden orbit | `KnotGame.p`, `Golden.absSurv`, `Golden.absAct` | `Golden.lean` | present and proved; round 8's T24b is built on it |
| long survivor cells | `KnotGame.exists_long_cell`, `tidy_cells` | `SurvivorSet.lean` | present and proved; round 8's T26 uses it |

**Census findings that changed the plan.**

* **T23 was partly present.**  `Littlewood.N_unbounded_of_kind` already gives
  unboundedness from an *infinite* kind sequence.  What the paper's
  `prop:kindyield` asserts, and what was missing, is the **finite-word** form:
  a single finite kind word `v` of period `p` with last letter `M`, repeated.
  Round 8 adds exactly that (`KindWord`, `N_unbounded_of_kindWord`) and routes
  it through condition (i) of the certified `thm:compactness`.
* **`prop:itinerary` was not present.**  The base-3/2 itinerary sum used by
  T22b had no counterpart anywhere in the tree; `Mahler.itinerary_tsum` is new.
* **No ternary/Mahler file existed at all.**  `Ternary.lean`, `Mahler.lean`,
  `Translation.lean` are wholly new.
* **T24c** has no partial precursor: Mathlib's `dimH` is never mentioned in the
  tree, and round 8 does not introduce it.

## 2. What round 8 reuses

| Item reused | Identifier | File |
| --- | --- | --- |
| the game itself | `KnotGame.Move`, `act`, `survives`, `survivesWord`, `posAfter` | `Basic.lean` |
| `r = λ⁻¹`, `g = 1 − r` | `KnotGame.r`, `g`, `r_pos`, `g_add_r` | `Basic.lean` |
| the knot count and depth | `KnotGame.N`, `KnotGame.d` (`Basic.lean`), `births_le_N`, `card_run` (`Suffix.lean`), `card_run_ge_of_ages` (`Permanence.lean`) | `Basic.lean`, `Suffix.lean`, `Permanence.lean` |
| the compactness theorem, condition (i) | `KnotGame.InfinitelyManyKnots`, `infinitelyManyKnots_of_boundedAgeWitnesses`, `N_unbounded_of_infinitelyManyKnots` | `Compactness.lean` |
| ages of knots along a word | `KnotAt`, `HasKnotAge`, `knotAt_cons_M` (`Permanence.lean`), `hasKnotAge_append` (`Density.lean`) | `Permanence.lean`, `Density.lean` |
| long survivor cells | `exists_long_cell`, `tidy_cells` | `SurvivorSet.lean` |
| the topological density criterion | `KindDense`, `N_unbounded_of_kindDense` | `Density.lean` |
| the five-point golden orbit | `p`, `Golden.absSurv`, `Golden.absAct` | `Golden.lean` |
| the transversality function and derivative | `gval`, `gder` (`TransversalityBounds.lean`), the round-3 window | `Transversality*.lean` |
| the semantic axiom audit | `KnotGame.Audit` | `AxiomAudit.lean` |

**No inherited definition was changed and no inherited statement was
re-derived.**  The only edit to an inherited file is the seven new imports in
`RequestProject/All.lean`.

## 3. What is new in round 8

| File | Content |
| --- | --- |
| `RequestProject/Ternary.lean` | **T22a**.  `D x = ⌊3x⌋` (the ternary cell index), the digit code `code : Move → ℤ`, the fatality criterion `survives_iff_digit_ne`, the ternary form of the move `act_eq_ternary` (`x ↦ (3x − [D x > c])/2`), the one-step package `step_ternary`, and `exists_unique_fatal` (exactly one of the three digits is fatal at every point — never none, never two).  Also the dyadic invariant `Dyadic`, `dyadic_half`, `dyadic_act`, `dyadic_posAfter`, `three_mul_ne_one`, `three_mul_ne_two`, which is what adjoins `1/2` when `c = 1`, and the arithmetic facts `one_lt_lam32`, `r32`, `g32`. |
| `RequestProject/Mahler.lean` | **T22b/c**.  `orbit_partial` and `summable_itinerary` set up the itinerary series; `itinerary_tsum` is `prop:itinerary` (`Σ_{j≥1} ε_j (2/3)^j = 1`); `base32_tsum` is its base-3/2 reading; `digit_eq_eps_add` / `digit_eq_eps_add_strict` are `D(x_n) = ε_{n+1} + [2x_{n+1} > 1]`; `floor_mem`, `mahler_recursion` and `mahler_of_survives` are the Mahler recursion in the `(p, y)` coordinates of `prop:mahler`. |
| `RequestProject/PeriodicYield.lean` | **T23**.  `rep` (word repetition) with `rep_add`, `length_rep`, `rep_split`; `KindWord` (a finite word all of whose repetitions `1/2` survives, with last letter `M`); `hasKnotAge_rep`; and the conclusions `infinitelyManyKnots_of_kindWord`, `N_unbounded_of_kindWord`. |
| `RequestProject/KindTree.lean` | **T24a/b**.  `words` (all words of a given length) with `mem_words`; `kindWords` (survivors) with `mem_kindWords`, `kindWords_succ`, `card_kindWords_succ`; `card_kindWords_dyadic`; **T24a** `card_kindWords_three_halves : (kindWords (3/2) n).card = 2 ^ n`; the five per-state recursions `card_p0_succ`…`card_p4_succ` at `λ = φ`; **T24b** `card_kindWords_phi_add_three : N_{n+3} = 4 N_n`. |
| `RequestProject/WindowSharp.lean` | **T25**.  `coeffOf`/`sharpList`/`sharpPoly` (a degree-22 `{−1,0,1}` coefficient vector) and `witness_at_3339`: at `x = 3339/5000 ∈ (667/1000, 67/100]`, `0 < g(x) ≤ 1/1000` and `−1/1000 < g′(x) < 0`.  `strongList`/`strongPoly` (degree 26) and `witness_at_3343`: at `x = 3343/5000`, `g(x) ≤ 1/100000` and `g′(x) > 0`.  The exports `transversality_fails_beyond_window` and `window_not_extendable`, plus `deriv_witness_at_3339`.  All checks are kernel reductions over exact rationals. |
| `RequestProject/Translation.lean` | **T22d**.  `wstep`/`witer` (the `w`-coordinate dynamics `w ↦ (3/2)w − [⌊(3/2)w⌋ > c]`) with `witer_succ`, `witer_shift`; `two_mul_act` (the change of coordinates `w = 2x`); `translate_core`; `birthSet`/`mem_birthSet`/`mem_birthSet_cons`/`card_birthSet`; `MahlerAlive`, `MahlerCriterion`, `moveOf`, `ctrl`, `mahlerAlive_iff`; and the equivalence `unbounded_iff_mahler`. |
| `RequestProject/DensityQuant.lean` | **T26**.  `KindDenseQuant` (the hypothesis **(D_λ)**), `kindDense_of_quant`, the quantitative extension step `exists_extension_len`, the nested family `qword` with its suffix/length lemmas, `hasKnotAge_qword`, `le_N_qword_length`, the growth constant `growth lam C = max 2 (1 + C(log λ + 1))`, `qword_length_step`, `qword_length_le`, and the conclusions `d_le_pow` (`d_λ(k) ≤ B^k − 1`) and `N_unbounded_of_kindDenseQuant`. |

New search program (never trusted by any Lean statement; the kernel re-checks
everything it produces): `scripts/window_sharp_search.py`, which produced the
T25 coefficient vectors.

## 4. Correspondence with the paper

| Paper label | Lean identifier | File |
| --- | --- | --- |
| `prop:ternary` | `survives_iff_digit_ne`, `act_eq_ternary`, `step_ternary`, `exists_unique_fatal`, `dyadic_posAfter` | `Ternary.lean` |
| `prop:itinerary` | `itinerary_tsum` | `Mahler.lean` |
| `prop:base32` | `base32_tsum`, `digit_eq_eps_add`, `digit_eq_eps_add_strict` | `Mahler.lean` |
| `prop:mahler` | `mahler_recursion`, `mahler_of_survives` | `Mahler.lean` |
| `prop:translation` | `unbounded_iff_mahler` | `Translation.lean` |
| `prop:kindyield` | `N_unbounded_of_kindWord` | `PeriodicYield.lean` |
| `prop:kinddim` (cylinder counts only) | `card_kindWords_three_halves`, `card_kindWords_phi_add_three` | `KindTree.lean` |
| `prop:kinddim` (dimension) | — not attempted | — |
| sharpness of the round-3 window | `witness_at_3339`, `witness_at_3343`, `window_not_extendable` | `WindowSharp.lean` |
| `thm:density`, quantitative form | `d_le_pow` | `DensityQuant.lean` |

## 5. Not commissioned, not attempted

Exhaustiveness for `prop:twostep`; the exact values `d_{3/2}(7) = 52` and
`d_{3/2}(8) ≥ 57`; the silver-ratio `d(k)` formula.  None of these was touched.
