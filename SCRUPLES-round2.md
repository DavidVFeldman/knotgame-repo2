# Round 2 — SCRUPLES summary

What is **proved** in round 2, what is **reused** from round 1, and what is
**reported**.  Docstrings in the sources state exactly this and nothing more.

## Proved in round 2

`RequestProject/Gaps.lean`

| Identifier | Exactly what is proved | Hypotheses |
|---|---|---|
| `Straddles` | *definition*: `x < r/2 ∧ 1 - r/2 < y` | — |
| `act_lt_act` | `act m x < act m y` | `1 < λ`; `x`, `y` survive `m`; `x < y` |
| `gap_law` | `act m y - act m x = λ(y-x)`, **or** `m = M` and `Straddles x y` and `act m y - act m x = λ(y-x) - (λ-1)` | `1 < λ`; `x`, `y` survive `m`; `x < y` |
| `straddles_unique` | `False` | `1 < λ`; `Straddles x y`; `Straddles z u`; `y ≤ z` |
| `straddles_at_most_one` | `¬ Straddles z u` | `1 < λ`; `Straddles x y`; `y ≤ z` |
| `half_not_survives_M` | `¬ survives M (1/2)` | `1 < λ` |
| `birth_head_ne_M` | `m ≠ M` | `1 < λ`; `survivesWord (1/2) (m :: w)` |
| `two_mul_births_le_length_succ` | `2 * births w ≤ n + 1` | `1 < λ`; `w.length = n` |
| `births_le_ceil_half` | `births w ≤ (w.length + 1) / 2` | `1 < λ` |
| `step_subset_Ioo`, `runFrom_subset_Ioo`, `run_subset_Ioo` | knots stay in `(0,1)` | `1 < λ` |
| `run_subset` | a set containing `1/2` and closed under `act` on its survivors contains every knot of every reachable configuration | closure only; no bound on `λ` needed |
| `runFrom_append` | `runFrom S (u ++ v) = runFrom (runFrom S u) v` | — |
| `card_le_length_succ` | `T.card ≤ b.length + 1` | `1 < λ`; `T ⊆ (0,1)`; every element of `T` survives `b`; `1 ≤ λ^{|b|}(y-x)` for all `x < y` in `T` |
| `scheduling_bound` | `(run w).card ≤ W + (W+1)/2 + 1` | `1 < λ`; `1 ≤ λ^W δ`; at every prefix `u` of `w`, distinct elements of `run u` are `≥ δ` apart |
| `N_le_of_separated` | `N n ≤ W + (W+1)/2 + 1` for every `n` | `1 < λ`; `1 ≤ λ^W δ`; distinct elements of `run u` are `≥ δ` apart, for **every** word `u` |
| `near_collision` | there are a prefix `u` of `w` and distinct `x, y ∈ run u` with `|x - y| < (λ^m)⁻¹` | `1 < λ`; `3m + 4 < 2·(run w).card` |

`RequestProject/GoldenEffective.lean`

| Identifier | Exactly what is proved |
|---|---|
| `delta0` | *definition*: `φ - 3/2` |
| `phi_pow_five` | `φ^5 = 5φ + 3` |
| `phi_pow_five_mul_delta0` | `φ^5 · (φ - 3/2) = φ²/2` — the exact identity, no numerics |
| `window_bound` | `1 ≤ φ^5 · delta0` |
| `p_sep` | distinct points of the five-point orbit are `≥ delta0` apart |
| `run_sep` | distinct coexisting knots at `λ = φ` are `≥ delta0` apart |
| `N_phi_le_nine` | `N φ n ≤ 9` for every `n` |
| `card_run_phi_le_nine` | `(run φ w).card ≤ 9` for every word `w` |

`RequestProject/PlasticOrbit.lean`

| Identifier | Exactly what is proved |
|---|---|
| `rho_lb`, `rho_ub` | `1324717957/10⁹ ≤ ρ ≤ 1324717958/10⁹` |
| `traw`, `tval`, `tf0`, `tf1` | *definitions*: the coordinates `(a,b,c) ↦ (a + bρ + cρ²)/2` and the two branch maps on them |
| `tval_tf0`, `tval_tf1` | the coordinate maps compute `x ↦ ρx` and `x ↦ ρx - (ρ-1)` |
| `Mn`, `En`, `abs_traw_sub_Mn` | the certified integer enclosure `|10¹⁸·traw t - Mn t| ≤ En t` |
| `orbitList` | *definition*: 153 integer triples |
| `orbitList_length` | the list has 153 entries |
| `chk_range` | every listed point has `0 < value < 1` |
| `chk_closed` | for every listed point, each of its two branch images is again listed, or provably outside `(0,1)` |
| `chk_chain` | the list is increasing, with consecutive gaps `≥ 239/100000` |
| `orbitList_pairwise` | any two distinct listed points are `≥ 239/100000` apart |
| `run_subset_OrbSet` | every knot of every reachable configuration at `λ = ρ` is a listed point |
| `run_sep` | distinct coexisting knots at `λ = ρ` are `≥ 239/100000` apart |
| `rho_pow_22` | `ρ²² = 86 + 151ρ + 114ρ²` |
| `window_bound_rho` | `1 ≤ ρ²² · (239/100000)` |
| `N_rho_le_34` | `N ρ n ≤ 34` for every `n` |
| `card_run_rho_le_34` | `(run ρ w).card ≤ 34` for every word `w` |

## Reused from round 1, unchanged

`Move`, `r`, `g`, `deleted`, `survives`, `f`, `branch`, `act`, `survivors`,
`step`, `runFrom`, `run`, `N`, `d`, `survivesWord`, `posAfter`, `births`
(`Basic.lean`); `straddle`, `act_injOn`, `act_M_ne_half`, `lam_mul_r`,
`lam_mul_g` (`Distinct.lean`); `mem_step`, `card_runFrom`, `card_run`
(`Suffix.lean`); `act_mem_Ioo` (`Pisot.lean`); `phi`, `phi_sq`, `one_lt_phi`,
`phi_gt`, `phi_lt`, `p`, `run_eq` (`Golden.lean`); `rho`, `rho_cubic`,
`rho_gt`, `one_lt_rho` (`Plastic.lean`).

No round-1 definition was altered and no round-1 theorem was restated.

## Reported, not repaired

* **The commission's premise for T4 is inaccurate about round 1.**  Round 1
  certified neither `d ≥ 2k-1` nor `d(k+1) ≥ d(k)+2`; `d` is defined but nothing
  about its values is proved (round-1 census flag (F)).  Rather than invent a
  reuse, T4 was proved from scratch, in the shape the scheduling argument
  consumes.  See finding (R2-a) of `CENSUS-round2.md`.
* **T7 was offered as an acceptable failure and is not one.**  Round 1's
  infeasibility finding was about the 25 525 reachable configurations and is
  untouched; the 153-point orbit needed here is a different and much smaller
  object, and it is certified.  See finding (R2-b) of `CENSUS-round2.md` and the
  round-2 addendum in `PLASTIC-REPORT.md`.

## Hypotheses deliberately not carried

* `δ > 0` in T5.  The paper states it; it follows from `1 ≤ λ^W δ`, which is
  also assumed, so carrying it would state more than is used.
* `W = ⌈log_λ(1/δ)⌉` in T5.  Replaced by the equivalent, logarithm-free
  `1 ≤ λ^W δ`, which is what both corollaries supply.

## Hypotheses that had to be made explicit

None.  Every hypothesis of T1–T7 as commissioned is either used or, in the two
cases listed above, provably redundant and therefore dropped.
