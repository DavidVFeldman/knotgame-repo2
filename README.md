This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# Knot counts in an interval deletion game — formal verification

A Lean 4 / Mathlib formalisation of the paper *Knot counts in an interval
deletion game*, carried out to the commission shipped with it.

Start here:

* [`CENSUS.md`](CENSUS.md) — Work Order 0: every numbered statement of the paper
  mapped to its Lean identifier, marked *in scope* / *out of scope
  (computational)* / *deferred*, with the flags on hypotheses the paper leaves
  implicit.
* [`PROP9-PLASTIC.md`](PROP9-PLASTIC.md) — Proposition 3.4 (the plastic
  number), certified: the 153 orbit points, the 25 525 reachable
  configurations, `sup N = 7` and the least lengths, with the design of the
  kernel certificate.
* [`PLASTIC-REPORT.md`](PLASTIC-REPORT.md) — the round-1 negative report on
  Proposition 3.4, with the cost measurements that ruled out the first route,
  and the round-6 addendum recording what replaced it.
* [`CENSUS-round2.md`](CENSUS-round2.md) — round 2: the audit of the round-1
  tree against the round-2 targets, and the map of targets T1–T7 to Lean
  identifiers.
* [`SCRUPLES-round2.md`](SCRUPLES-round2.md) — round 2: exactly what is proved,
  what is reused, and what is reported.
* [`AXIOM-AUDIT-round2.md`](AXIOM-AUDIT-round2.md) — the audit output, automatic
  and per-target.
* [`CENSUS-round3.md`](CENSUS-round3.md) — round 3: what was inherited, and the
  map of targets T8 (tribonacci, supergolden), T9 (δ-transversality) and T10
  (pair counting) to Lean identifiers.
* [`SCRUPLES-round3.md`](SCRUPLES-round3.md) — round 3: every place where the
  Lean statement is not a literal transcription of the commission.
* [`AXIOM-AUDIT-round3.md`](AXIOM-AUDIT-round3.md) — round 3: the audit output,
  automatic and per-target.
* [`CENSUS-round4.md`](CENSUS-round4.md) — round 4: what was inherited from the
  round-3 tree, and the map of targets T11 (the branching lemmas below the
  golden ratio), T12 (continuum and linear count) and T13 (the common window)
  to Lean identifiers.
* [`SCRUPLES-round4.md`](SCRUPLES-round4.md) — round 4: the open/closed
  conventions at `g` and `r`, the treatment of the midpoint in T11c, and every
  other deviation from a literal transcription.
* [`AXIOM-AUDIT-round4.md`](AXIOM-AUDIT-round4.md) — round 4: the audit output,
  automatic and per-target.
* [`CENSUS-round5.md`](CENSUS-round5.md) — round 5: what was inherited from the
  round-4 tree, and the map of targets T14 (the survivor set), T15 (permanence),
  T16 (one annihilation per step), T17 (compactness), T18 (density), T19 (the
  deficit law and free births), T20 (candidate cells) and T21 (the two-step
  containment) to Lean identifiers.
* [`SCRUPLES-round5.md`](SCRUPLES-round5.md) — round 5: the rendering of the
  left-infinite runs in T17, the `λ < 3/2` restriction in T19(b), the scoping of
  T21, and every other deviation from a literal transcription.
* [`AXIOM-AUDIT-round5.md`](AXIOM-AUDIT-round5.md) — round 5: the audit output,
  automatic and per-target.
* [`CENSUS-round7.md`](CENSUS-round7.md) — round 7: what was inherited, and the
  three items the notes flag as open — the return-time tail bound, the renewal
  inequality and the exponential lower bound for `K_m` — mapped to Lean
  identifiers.
* [`SCRUPLES-round7.md`](SCRUPLES-round7.md) — round 7: the deterministic
  (Lebesgue) form of the tail bound, the deterministic renewal step that
  replaces the empirical renewal inequality, the rates actually obtained, and
  the exact extent of the parameter window.
* [`AXIOM-AUDIT-round7.md`](AXIOM-AUDIT-round7.md) — round 7: the audit output,
  automatic and per-target.
* [`CENSUS-round11.md`](CENSUS-round11.md) — round 11: the statements the
  round-1 census had recorded as *deferred* (`lem:overlap`, `cor:decide`,
  `prop:circle`), together with `prop:immortal32`, `prop:square` /
  `prop:squaresurv`, the record-length bounds `prop:lowerbound` /
  `cor:recursive`, the measure and dimension *upper* bound for the kind set,
  and a sharper certified rate at `λ = 3/2`.
* [`SCRUPLES-round11.md`](SCRUPLES-round11.md) — round 11: the hypotheses added
  to `prop:square` and to the record-length bounds, the reading of "decidable"
  in `cor:decide`, and every other deviation.
* [`AXIOM-AUDIT-round11.md`](AXIOM-AUDIT-round11.md) — round 11: the audit
  output, automatic and per-target.
* [`CENSUS-round12.md`](CENSUS-round12.md), [`SCRUPLES-round12.md`](SCRUPLES-round12.md),
  [`AXIOM-AUDIT-round12.md`](AXIOM-AUDIT-round12.md) — round 12: the Hausdorff
  *lower* bound for the kind set, hence `dimH K_{3/2} = log 2 / log 3`
  (`RequestProject/KindDimLower.lean`).  Round 12 was interrupted before
  writing its paperwork; these three documents were reconstructed in round 13
  from the source, and say so in their headers.
* [`CENSUS-round13.md`](CENSUS-round13.md), [`SCRUPLES-round13.md`](SCRUPLES-round13.md),
  [`AXIOM-AUDIT-round13.md`](AXIOM-AUDIT-round13.md) — round 13: the box
  dimension of the kind set (T36), the missing paperwork of rounds 11 and 12
  (T37), the counting operator (T38) and the trapezoid at `λ = √2` (T39).
  `SCRUPLES-round13.md` §1 displays the definitions of covering number and box
  dimension and argues that they are the standard ones.
* [`ABANDONED.md`](ABANDONED.md) — **everything this development does not
  deliver**, in one place: the growth rate beyond `49^(1/16)`, the record
  depths beyond `k = 4`, the exhaustiveness half of `prop:twostep`, the
  commissioned width of the above-`φ` window, the independence step of
  `prop:trapezoid`, and the paper's computational remarks and open questions.
  (Its §1, the dimension of the kind set, is now **closed**: rounds 12 and 13
  proved the Hausdorff lower bound and both box dimensions.)
* [`GITHUB_HANDOFF_CHECKLIST`](GITHUB_HANDOFF_CHECKLIST) — status of every work
  order and every round-2 target, the standing constraints, and how to
  reproduce.

## The development

| File | Contents |
|---|---|
| `RequestProject/Basic.lean` | the game: `Move`, `r`, `g`, `deleted`, `survives`, `branch`, `act`, `step`, `run`, `N`, `d`, `posAfter`, `births` |
| `RequestProject/Distinct.lean` | distinctness of images (`act_injOn`, `act_M_ne_half`, `card_step`) |
| `RequestProject/Suffix.lean` | suffix decomposition (`card_run`) and monotonicity (`N_mono`) |
| `RequestProject/Threshold.lean` | `N λ n = 1` for all `n ≥ 1` iff `2 ≤ λ` (`N_eq_one_iff`) |
| `RequestProject/Golden.lean` | the golden ratio automaton and `sup N = 2` (`Golden.sup_N_phi`) |
| `RequestProject/Pisot.lean` | Pisot parameters have a finite orbit (`orb_finite`, `conj_bound`) |
| `RequestProject/Plastic.lean` | the plastic number is Pisot; its orbit is finite |
| `RequestProject/Sqrt2.lean` | the case `λ = √2`: blocks `RR`, `LL` and the `b` coordinate |
| `RequestProject/Littlewood.lean` | the Littlewood identity, no return to `1/2`, kind sequences make `N` unbounded |
| `RequestProject/Gaps.lean` | round 2, T1–T5: order (`act_lt_act`), the gap law (`gap_law`), one service per move (`straddles_unique`), birth spacing (`births_le_ceil_half`), and the scheduling bound (`scheduling_bound`, `N_le_of_separated`) |
| `RequestProject/GoldenEffective.lean` | round 2, T6: `N φ n ≤ 9` from the five-point orbit and `φ⁵(φ-3/2) = φ²/2` |
| `RequestProject/PlasticOrbit.lean` | round 2, T7: the 153-point orbit of `1/2` at the plastic number, certified over `ℤ[ρ]`, and `N ρ n ≤ 34` |
| `RequestProject/Tribonacci.lean` | round 3, T8: the 7-point orbit at the tribonacci parameter, its 20 reachable configurations, `sup N = 3`, `d = 1, 3, 7` |
| `RequestProject/Supergolden.lean` | round 3, T8: the 43-point orbit at the supergolden parameter, its 412 configurations with depths, `sup N = 4`, `d = 1, 3, 5, 11` |
| `RequestProject/TransversalityBounds.lean` | round 3, T9: tail and centered-form estimates for the `{−1,0,1}` class |
| `RequestProject/TransversalityChecker.lean` | round 3, T9: the branch-and-bound checker `cellOK`, in exact integer arithmetic |
| `RequestProject/TransversalityCell.lean` | round 3, T9: soundness of the checker on one cell (`cell_sound`) |
| `RequestProject/TransversalityCertificate.lean` | round 3, T9: the 27 kernel-checked cells tiling `[1/2, 667/1000]` |
| `RequestProject/Transversality.lean` | round 3, T9: δ-transversality on the window (`transversality`, `transversality_deriv`) |
| `RequestProject/PairCounting.lean` | round 3, T10: the endpoint family `Phi`, the embedding lemma, and the pair-counting bounds on `[1000/667, 2]` (`volume_close_le`, `sum_volume_close_le`, `sum_volume_close_le_unord`, `lintegral_pairCount_le`) |
| `RequestProject/Branching.lean` | round 4, T11: the window `(g,r)` and branch legality, no jumping (`no_jump_low`, `no_jump_high`) with its sharp equivalences, the 2-cycle at `λ ≥ φ` (`sharp_two_cycle`), the good child (`good_child`) and bounded return (`bounded_return_low`, `bounded_return_high`) |
| `RequestProject/BranchingContinuum.lean` | round 4, T12a: the bit-driven itineraries and a continuum of survival itineraries of `1/2` (`continuum_of_survival_itineraries`) |
| `RequestProject/BranchingCount.lean` | round 4, T12b: the spine, its window visits, and the linear count `m/(B+1) ≤ K λ m` (`K_ge`) |
| `RequestProject/CommonWindow.lean` | round 4, T13: one identifier for the window `[1000/667, 8/5]` on which transversality, the branching lemmas and the count all hold (`common_window`) |
| `RequestProject/SurvivorSet.lean` | round 5, T14: the cells of a word, their count, total length `r^{\|v\|}` and the long cell (`inCells_cells`, `length_cells_le`, `volume_survivorSet`, `exists_long_cell`) |
| `RequestProject/Backward.lean` | round 5, T16: the inverse branches and one annihilation per backward step (`posAfter_inj`, `annihilation_unique`) |
| `RequestProject/Permanence.lean` | round 5, T15: knots with ages and the permanence law (`KnotAt`, `mem_run_iff`, `knotAt_cons`) |
| `RequestProject/Compactness.lean` | round 5, T17: left-infinite runs and the equivalence of the three conditions (`infinitelyManyKnots_iff_annihilations`, `infinitelyManyKnots_of_boundedAgeWitnesses`, `N_unbounded_of_infinitelyManyKnots`) |
| `RequestProject/Density.lean` | round 5, T18: the conditional density criterion (`KindDense`, `infinitelyManyKnots_of_kindDense`) |
| `RequestProject/Deficit.lean` | round 5, T19: the deficit law (`deficit_law`, `step_extremes`) and free births (`actsAs_M_R_iff`, `actsAs_M_L_iff`, `actsAs_M_R_converse_fails`) |
| `RequestProject/Candidates.lean` | round 5, T20: itineraries and the partition of the survivor set into candidate cells (`FollowsItin`, `followsItin_partition`) |
| `RequestProject/CandidateInstance.lean` | round 5, T20: the instance at `λ = 3/2` — six live candidates of `2^11`, total length `(2/3)^19` (`candidate_count`, `candidate_total_length`) |
| `RequestProject/RunRational.lean` | round 5, T21: the exact integer model of the game at `λ = 3/2` and the bridge (`runZ`, `run_eq_image_runZ`, `run_subset_run_iff`) |
| `RequestProject/TwoStep.lean` | round 5, T21: the record words for `k = 2,…,7`, their configurations, the depth bounds and the containments `2 ⊂ 3 ⊂ 5 ⊂ 7`, `4 ⊂ 6` |
| `RequestProject/PlasticIndex.lean` | the game at `ρ` as an automaton on the 153 orbit indices: packed transition tables and the bridge (`stepIdx`, `runIdx`, `run_eq_cfgSet`, `card_run_eq_length`) |
| `RequestProject/PlasticTbl.lean` | the search tree holding the configuration certificate, and the facts used about it |
| `RequestProject/PlasticCert.lean` | generated data: all 25 525 reachable index configurations with depth tags and recorded parents |
| `RequestProject/PlasticConfig.lean` | Proposition 3.4: `sup N ρ = 7` (`sup_N_rho`), the least lengths `d ρ k` for `k ≤ 7`, and the count 25 525 (`card_reachable_configs`) |
| `RequestProject/PlasticOrbitCount.lean` | Proposition 3.4: the orbit of `1/2` at `ρ` has exactly 153 points (`card_Orb_rho`, `Orb_rho_eq_OrbSet`) |
| `RequestProject/RecordDepths.lean` | the exact record depths `d_{3/2}(2) = 3`, `d_{3/2}(3) = 5`, `d_{3/2}(4) = 9`, by kernel exhaustion of all words of length `≤ 8` |
| `RequestProject/ExpCount.lean` | round 7: the covering machinery — images of branch words (`rapp`), absorption (`bSurvives_of_image_mem`), the localized counts `Kx`, `kappa`, the doubling property `Doubling`, the deterministic renewal step (`two_mul_kappa_le`) and `two_pow_le_K_of_doubling` |
| `RequestProject/ExpCert.lean` | round 7: interval arithmetic in the point and in the parameter (`iok`, `rapp_mem_of_iok`), certificates and `doubling_of_cert` |
| `RequestProject/ExpLower.lean` | round 7: the instance at `λ = 3/2` — a 15-cell certificate with word length 5, giving `2 ^ (m/5) ≤ K (3/2) m` (`two_pow_le_K`) |
| `RequestProject/ExpWindowData.lean` | round 7: generated data — 24 parameter cells covering `[1000/667, 8/5]`, 1333 interval cells, word length `T ≤ 8` |
| `RequestProject/ExpWindow.lean` | round 7: the kernel checks of that data and the uniform bound `2 ^ (m/8) ≤ K λ m` on the common window (`doubling_window`, `two_pow_le_K_window`) |
| `RequestProject/ExpMulti.lean` | round 7: the same covering argument at multiplicity `k` (`MDoubling`, `mul_kappa_le`, `pow_le_K_of_mdoubling`) |
| `RequestProject/ExpMultiCert.lean` | round 7: certificates at multiplicity `k` (`mcellOK`, `mdoubling_of_cert`) |
| `RequestProject/ExpSharpData.lean` | round 7: generated data — 503 cells tiling `[1/4,3/4]`, each with 15 distinct words of length 12, at `λ = 3/2` |
| `RequestProject/ExpSharp.lean` | round 7: the sharper bound at `λ = 3/2`, `15 ^ (m/12) ≤ K (3/2) m` (`fifteen_pow_le_K`) |
| `RequestProject/ReturnTail.lean` | round 7: the return time of the discarded child and its tail bound (`retTime`, `return_time_tail`, `return_time_tail_three_halves`, `return_time_tail_prob_three_halves`) |
| `RequestProject/Ternary.lean` | round 8, T22a: the ternary reformulation at `λ = 3/2` — the cell index `D x = ⌊3x⌋`, the digit code, `survives_iff_digit_ne`, `act_eq_ternary`, `step_ternary`, `exists_unique_fatal`, and the dyadic invariant (`Dyadic`, `dyadic_posAfter`) |
| `RequestProject/Mahler.lean` | round 8, T22b/c: the itinerary sum `itinerary_tsum` (`prop:itinerary`), its base-3/2 reading `base32_tsum`, the digit identity `digit_eq_eps_add`(`_strict`), and Mahler's recursion (`mahler_recursion`, `mahler_of_survives`) |
| `RequestProject/Translation.lean` | round 8, T22d: the knot-free equivalent at `λ = 3/2` (`MahlerCriterion`, `translate_core`, `card_birthSet`, `unbounded_iff_mahler`) |
| `RequestProject/PeriodicYield.lean` | round 8, T23: a periodic kind word ending in `M` yields infinitely many simultaneous knots (`KindWord`, `infinitelyManyKnots_of_kindWord`, `N_unbounded_of_kindWord`) |
| `RequestProject/KindTree.lean` | round 8, T24a/b: cylinder counts of the survival tree of `1/2` — `2 ^ n` at `λ = 3/2` (`card_kindWords_three_halves`) and `N_{n+3} = 4 N_n` at `λ = φ` (`card_kindWords_phi_add_three`). The dimension (T24c) is not attempted |
| `RequestProject/WindowSharp.lean` | round 8, T25: sharpness of the transversality window — explicit `{−1,0,1}` members and rational points just beyond `667/1000` at which transversality fails (`witness_at_3339`, `witness_at_3343`, `window_not_extendable`) |
| `RequestProject/DensityQuant.lean` | round 8, T26: the quantitative density criterion (`KindDenseQuant`) and the exponential depth bound `d_λ(k) ≤ B ^ k − 1` (`d_le_pow`, `N_unbounded_of_kindDenseQuant`) |
| `RequestProject/NoRecurrence.lean` | round 10, T30 (`prop:norecur`): at `λ = 3/2` no knot occupies the same position twice (`no_recurrence`, `no_recurrence_knotAt`, `knot_positions_injective`) and no nonempty block of moves acts as the identity on a knot (`no_identity_block`, `no_identity_block_config`); built on round 8's dyadic invariant |
| `RequestProject/ExpSharperData.lean` | round 10, T31: generated data — 747 cells tiling `[1/6,5/6]`, each with 26 distinct words of length 14, at `λ = 3/2` |
| `RequestProject/ExpSharper.lean` | round 10, T31: the sharper bound at `λ = 3/2`, `26 ^ (m/14) ≤ K (3/2) m` (`twentysix_pow_le_K`), improving round 7's `15 ^ (m/12)` (`sharper_rate`, `sharper_rate_real`) |
| `RequestProject/ExpVar.lean` | round 10, T32 machinery: doubling with a *variable* return time (`Divergent`, `VDoubling`, `two_pow_le_K_of_vdoubling`) and its certificate checkers (`vcellOK`, `vlamCellOK`, `vdoubling_of_cert`, `vdoubling_of_window`) |
| `RequestProject/ExpAboveData0.lean` … `ExpAboveData11.lean`, `ExpAboveData.lean` | round 10, T32: generated data — 180 parameter cells carrying 17 141 point cells, split across twelve files for elaboration |
| `RequestProject/ExpAboveChecks.lean` | round 10, T32: the kernel checks of that data, in 36 groups |
| `RequestProject/ExpAbove.lean` | round 10, T32: exponential kind counts **above** the golden ratio — `2 ^ (m/18) ≤ K λ m` for `λ ∈ [3457/2000, 4331/2500]` (`two_pow_le_K_above`), in particular at `√3` (`two_pow_le_K_sqrt_three`); the commissioned window `[17/10, 7/4]` is *not* certified, see `CENSUS-round10.md` §4 |
| `RequestProject/Overlap.lean` | round 11, `lem:overlap`: the `{0,±1}` polynomial class `PMOne`, `1/√2` and `2/3` are not roots of a non-zero member (`not_pm_root_inv_sqrt_two`, `not_pm_root_two_thirds`), `1/φ` and `1/ρ` are (`inv_phi_root`, `inv_rho_root`), and the consequence `branchIter_injective` at `3/2` and `√2` |
| `RequestProject/PisotDecide.lean` | round 11, `cor:decide`: at a Pisot parameter the reachable configurations are finite (`reachable_finite`), `N_λ` is eventually constant (`N_eventually_constant`) and its supremum is attained at a finite level (`sup_N_isGreatest`) |
| `RequestProject/CircleForm.lean` | round 11, `prop:circle`: the circle model (`rot`, `Dop`) and the three normal forms `circle_L`, `circle_R`, `circle_M`, with the count of marked points (`card_marked`) |
| `RequestProject/Immortal.lean` | round 11, `prop:immortal32`: infinitely many immortal births force `N = ∞` (`ImmortalBirth`, `N_unbounded_of_immortal`), for every `λ > 1` |
| `RequestProject/Square.lean` | round 11, `prop:square` / `prop:squaresurv`: the binary square at `λ = √2` (`alpha`, `beta`, `square_normal_form`) and the survival table on the five regions (`squaresurv`, `spares_region₁…₅`) |
| `RequestProject/KindDim.lean` | round 11, `prop:kinddim` (upper half): the kind set at `λ = 3/2` is Lebesgue null (`volume_K`) and has `dimH K ≤ log 2 / log 3` (`dimH_K_le`) |
| `RequestProject/RecordLower.lean` | round 11, `prop:lowerbound` / `cor:recursive`: `2k ≤ d λ k + 1` and `d λ k + 2 ≤ d λ (k+1)` under the attainability hypothesis, via the chopping lemma `births_le_births_take_add_one` |
| `RequestProject/ExpSharpestData*.lean`, `ExpSharpestChecks*.lean` | round 11: generated data — 2 008 cells tiling `[1/6,5/6]`, each with 49 distinct words of length 16 — and their kernel checks in 41 groups |
| `RequestProject/ExpSharpest.lean` | round 11: the sharpest certified bound at `λ = 3/2`, `49 ^ (m/16) ≤ K (3/2) m` (`fortynine_pow_le_K`), rate `49^(1/16) ≈ 1.27537` (`sharpest_rate`, `sharpest_rate_real`) |
| `RequestProject/KindDimLower.lean` | round 12, `prop:kinddim` (lower half): the coding map `G` of the binary survival tree, the measure `kindMeasure` it carries (`kindMeasure_K`), the Frostman estimate (`kindMeasure_le`, `kindMeasure_le_of_ediam`), and hence `log 2 / log 3 ≤ dimH K` (`le_dimH_K`) and `dimH K = log 2 / log 3` (`dimH_K_eq`) |
| `RequestProject/KindBox.lean` | round 13, T36: covering numbers (`coverSizes`, `coverNum`), the box dimensions (`upperBoxDim`, `lowerBoxDim`) over *all* scales `r → 0⁺`, the triadic bounds, the squeeze `tendsto_boxQuot`, and `boxDim_K`: both box dimensions of the kind set at `λ = 3/2` are `log 2 / log 3` |
| `RequestProject/CountingOperator.lean` | round 13, T38 (`prop:lebeigen`): the transfer operator `T` and its eigenvalue (`T_one`, `T 1 = (2/λ)·1`); the branch count with `∫₀¹ B_λ(m,x) dx = (2/λ)^m` (`integral_bcount`, `bcount_eq_card`); the move-word count with `∫₀¹ K_λ(m,x) dx = (3/λ)^m` (`integral_kcount`) — the constant is `3/λ`, not `2/λ`, for the three-letter alphabet, and at `λ = 3/2` it reproduces the known `2^m` |
| `RequestProject/Trapezoid.lean` | round 13, T39 (`prop:trapezoid`): the even/odd splitting of the backward series at `λ = √2` (`bval_split`) with ranges `[0, 2−√2]` and `[0, √2−1]`; the convolution of two uniform laws (`unifSum_eq_withDensity`); and the trapezoidal density with plateau `(2+√2)/2` (`trapDens`, `trapezoid_law`, `trapezoid_of_split`) |
| `RequestProject/AxiomAudit.lean` | semantic audit of the axioms of every public theorem |

## Building

```
lake exe cache get
lake build
```

`lake build` also runs the axiom audit, which fails the build if any public
theorem of the `KnotGame` namespace depends on an axiom outside `propext`,
`Classical.choice`, `Quot.sound` — in particular on `sorryAx`. The development
contains no `sorry`, `admit`, `axiom` or `native_decide`.

`experiments/` holds cost measurements only; it is outside the library glob and
is never built.  `scripts/` holds the search programs that *found* the objects
the kernel then verifies (the record words of `TwoStep.lean` among them); no
Lean statement depends on them.  Two of them are generators:
`scripts/plastic_cert.py` writes `RequestProject/PlasticCert.lean` and
`scripts/plastic_orbcert.py` writes the `orbCert` table of
`RequestProject/PlasticOrbitCount.lean`; both read the transition tables out of
`RequestProject/PlasticIndex.lean`, and what they write is checked by the
kernel.  `scripts/window_sharp_search.py` found the coefficient vectors of
`RequestProject/WindowSharp.lean`; they are inert data and every inequality
about them is re-checked by the kernel over exact rationals.  Round 10 adds two
more generators: `scripts/gen_expsharper.py` writes
`RequestProject/ExpSharperData.lean`, and `scripts/gen_expabove.py` (with the
search library `scripts/expvar_search.py`) writes
`RequestProject/ExpAboveData0.lean` … `ExpAboveData11.lean`,
`RequestProject/ExpAboveData.lean` and `RequestProject/ExpAboveChecks.lean`.
Both are untrusted; the kernel re-checks every cell they emit.

## Round documents

Each round leaves three documents: a census of what was inherited and what is
new (`CENSUS-round*.md`), a record of every deviation from the paper
(`SCRUPLES-round*.md`), and the axiom report (`AXIOM-AUDIT-round*.md`).  The
latest round is round 13 (`CENSUS-round13.md`, `SCRUPLES-round13.md`,
`AXIOM-AUDIT-round13.md`); `GITHUB_HANDOFF_CHECKLIST` carries the per-round
checklists, and `ABANDONED.md` collects, once and for all, what the
development does not deliver and why.
