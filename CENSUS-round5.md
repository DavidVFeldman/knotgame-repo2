# CENSUS — round 5 (T14–T21)

Census-first, as the commission requires: what the round-4 tree in the tarball
already contained, what round 5 reuses, and what is new.

## 1. What was inherited (ground truth: the round-4 tree)

The round-4 tree was rebuilt in place before any new work.  It builds and the
semantic axiom audit passes.  **No round-1/2/3/4 definition was changed and no
round-1/2/3/4 statement was re-derived.**  The only edit to an inherited file is
ten added imports in `RequestProject/All.lean` (`SurvivorSet`, `Backward`,
`Permanence`, `Compactness`, `Density`, `Deficit`, `Candidates`,
`CandidateInstance`, `RunRational`, `TwoStep`).

| Item reused by round 5 | Identifier | File |
| --- | --- | --- |
| the three moves and their deleted sets | `KnotGame.Move`, `KnotGame.deleted` | `Basic.lean` |
| survival of one move / of a word | `KnotGame.survives`, `survives_L/M/R`, `KnotGame.survivesWord` | `Basic.lean` |
| the branch maps and the action | `KnotGame.f`, `KnotGame.branch`, `KnotGame.act`, `act_M_of_lt`, `act_M_of_gt`, `act_L`, `act_R` | `Basic.lean` |
| `r = λ⁻¹`, `g = 1 − r`, `r_pos`, `r_lt_one`, `g_pos`, `lam_mul_r` | `KnotGame.r`, `KnotGame.g` | `Basic.lean` |
| one-step and word transport of configurations | `KnotGame.survivors`, `step`, `runFrom`, `run` | `Basic.lean` |
| the counting functions of the paper | `KnotGame.N`, `KnotGame.d`, `KnotGame.births` | `Basic.lean` |
| the position of a survivor after a word | `KnotGame.posAfter` | `Basic.lean` |
| membership in `run` / `step`, and `card_run` | `mem_step`, `filter_step`, `card_runFrom`, `card_run`, `births_le_N` | `Suffix.lean` |
| the gap law (T2) | `KnotGame.gap_law` | `Gaps.lean` |
| the images of the branch maps inside `(0,1)` | `KnotGame.act_mem_Ioo` | `Pisot.lean` |
| the semantic axiom audit | `KnotGame.Audit` | `AxiomAudit.lean` |

**Census findings, reported rather than repaired.**

1. *T15 asks to audit round 1's suffix decomposition first.*  `Suffix.lean` has
   the counting side of the decomposition (`mem_step`, `card_runFrom`,
   `card_run`, `births_le_N`), i.e. "a survivor of `w` is a suffix-born point
   transported forward", but it carries **no notion of the age of a knot** and
   no statement that ages are preserved by prefixing.  Round 5 therefore adds
   `KnotAt` / `HasKnotAge` (position *and* age) and derives `mem_run_iff` from
   the inherited `mem_step` rather than re-proving it.
2. *T14 needs a description of `S(v)` as a finite union of intervals.*  Nothing
   inherited describes the survivor set geometrically: rounds 1–4 track finite
   configurations (`Finset ℝ`) and single itineraries, never the set of
   surviving *entry* points.  `cells` and `survivorSet` are new.
3. *T21 record words.*  The seven record words of `prop:twostep` are **not
   listed** in the commission, in `knotgame.tex`, or anywhere in the tarball
   (Figure `fig:records32` is an included PDF).  See §8 and `SCRUPLES-round5.md`.

## 2. T14 — survivor-set structure (`RequestProject/SurvivorSet.lean`)

| Claim of the commission | Identifier |
| --- | --- |
| the cell list of a word, built from the right by the inverse branches | `cells`, `cells_cons_L/R/M` |
| the cells are disjoint, ordered, and open — the invariant carried by the induction | `Tidy`, `tidy_cells` |
| `x` survives `v` iff `x` lies in one of the cells | `inCells_cells` |
| at most `1 + #M(v)` cells | `length_cells_le` (with `countM`, `countM_cons`, `countM_le_length`) |
| total length exactly `r^{\|v\|}` | `cellsLen_cells` |
| the same, as Lebesgue measure of `S(v)` | `survivorSet`, `survivorSet_eq_biUnion`, `volume_survivorSet` |
| some cell has length `≥ r^{\|v\|}/(\|v\|+1)` | `exists_long_cell` |

Auxiliary and new: `inCells`, `splitHalf` (the `M`-step on cell lists, which
splits the cell straddling `1/2`), `splitHalf_length_le`, `splitHalf_sum`,
`splitHalf_side`, `inCells_splitHalf`, `scaleCell`, `tidy_map_scale`,
`inCells_map_scale`, `inCells_M_map`, `cellsLen`, `cells_ne_nil`,
`volume_biUnion_cells`.

## 3. T15 — permanence (`RequestProject/Permanence.lean`)

| Claim of the commission | Identifier |
| --- | --- |
| knot of `w` at position `x` and age `a` | `KnotAt`, `HasKnotAge`, `KnotAt.age_lt` |
| the knots of `cv` are the knots of `v`, positions and ages unchanged, plus … | `knotAt_cons`, `knotAt_cons_of_knotAt` |
| … one new knot of age `\|v\|`, present iff `c = M` and `1/2` survives `v` | `knotAt_cons_M` |
| the configuration after `w` is exactly the set of knot positions | `mem_run_iff` (from the inherited `mem_step`), `mem_runFrom_iff` |
| distinct ages give distinct knots | `knotAt_age_inj` |
| `k` distinct ages ⟹ `k` simultaneous knots | `card_run_ge_of_ages` |

## 4. T16 — one annihilation per step (`RequestProject/Backward.lean`)

| Claim of the commission | Identifier |
| --- | --- |
| the inverse branches `y ↦ ry` and `y ↦ ry + (1−r)` | `invBranch`, `invBranch_M`, `invBranch_M_of_lt`, `invBranch_M_of_ge` |
| their images lie in `(0,1)` | `invBranch_R_mem`, `invBranch_L_mem` |
| each inverse branch is injective (disjoint images `[0,r)` / `[1−r,1]`, and `[0,r/2)` / `(1−r/2,1]` at `M`) | `invBranch_injective` |
| the inverse branch really inverts the action on survivors | `invBranch_act` |
| every composite is injective | `posAfter_inj` |
| **T16**: at most one point reaches `1/2` at a backward step | `annihilation_unique` |

## 5. T17 — the compactness criterion (`RequestProject/Compactness.lean`)

The chosen rendering is the one the commission offers: a left-infinite run is
`b : ℕ → Move`, read through ever-longer suffixes `sfx b a`.

| Claim of the commission | Identifier |
| --- | --- |
| suffixes of a left-infinite run | `sfx`, `sfx_zero`, `sfx_succ`, `length_sfx`, `sfx_congr`, `sfx_split` |
| a knot of age `a` of a left-infinite run | `InfKnotAge`, `infKnotPos`, `knotAt_of_infKnotAge` |
| **(i)** some run carries infinitely many simultaneous knots | `InfinitelyManyKnots` |
| **(ii)** some backward play annihilates infinitely many points | `annihilated`, `InfinitelyManyAnnihilations` |
| **(iii)** words with `k` knots of pointwise bounded ages | `BoundedAgeWitnesses` |
| **(i) ⟺ (ii)** — the two readings of one definition | `infinitelyManyKnots_iff_annihilations` (via `annihilated_eq_image`, `infKnotPos_injOn`) |
| **(i) ⟹ (iii)** | `boundedAgeWitnesses_of_infinitelyManyKnots` |
| **(iii) ⟹ (i)** — bounded integer sequences admit constant subsequences; diagonal agreement on ever-longer suffixes | `infinitelyManyKnots_of_boundedAgeWitnesses` (with `back`, `sfx_back_of_agree`, `infKnotAge_back`) |
| any of them implies `N_λ(n)` unbounded | `N_unbounded_of_infinitelyManyKnots` |

## 6. T18 — the topological density criterion (`RequestProject/Density.lean`)

**Conditional**, exactly as commissioned: the hypothesis is certified for no
specific `λ`, and every statement carries it as an explicit argument.

| Claim of the commission | Identifier |
| --- | --- |
| HYPOTHESIS: every nonempty open subinterval of `(0,1)` contains `Φ_u(1/2)` for a kind `u` | `KindDense` |
| knots survive prefixing (the half of T15 that makes the construction nest) | `knotAt_append`, `hasKnotAge_append` |
| T14 gives the open target, the hypothesis gives the kind word, T15 gives the gain | `exists_extension` |
| the nested sequence of words | `dword`, `dword_succ`, `dword_suffix`, `dword_length_lt`, `dword_length_strictMono`, `hasKnotAge_dword_succ`, `hasKnotAge_dword` |
| CONCLUSION: condition (i) of T17 | `infinitelyManyKnots_of_kindDense` |
| in particular `N_λ(n)` unbounded | `N_unbounded_of_kindDense` |

## 7. T19 — two short consequences (`RequestProject/Deficit.lean`)

| Claim of the commission | Identifier |
| --- | --- |
| **(a)** `T = 1 − spread`; `T ↦ λT` when the extreme pair straddles, `T ↦ λT − (λ−1)` otherwise | `deficit`, `deficit_law` (from the inherited `gap_law`) |
| the extremes of the new configuration are the images of the extremes | `step_extremes`, `act_le_act` |
| **(b)** "`M` acts on `C` exactly as `m'`" | `ActsAs` |
| **(b)** every knot `< r/2` ⟹ `M` acts as `R` | `actsAs_M_R_of_forall_lt` |
| **(b)** every knot `> 1 − r/2` ⟹ `M` acts as `L` | `actsAs_M_L_of_forall_gt` |
| **(b)** the converses, for `λ < 3/2` | `forall_lt_of_actsAs_M_R`, `forall_gt_of_actsAs_M_L`, `actsAs_M_R_iff`, `actsAs_M_L_iff` |
| **(b)** the converse is *false* for `λ ≥ 3/2` — reported, not repaired | `actsAs_M_R_converse_fails` |
| a free `M` is a free birth | `step_M_eq_of_actsAs` |

The `λ ≥ 3/2` finding is the one substantive divergence of round 5 from the
paper; it is documented in `SCRUPLES-round5.md` §4.

## 8. T20 — the candidate-cell identity (`Candidates.lean`, `CandidateInstance.lean`)

General theory (any `λ > 1`, any word):

| Claim of the commission | Identifier |
| --- | --- |
| an itinerary declares a branch at each `M` | `FollowsItin`, `followsItin_length`, `followsItin_L/R/M_cons` |
| following an itinerary implies surviving, inside `(0,1)` | `survivesWord_of_followsItin`, `mem_Ioo_of_followsItin` |
| every survivor follows one itinerary, and only one | `exists_followsItin`, `followsItin_unique` |
| **cells partition `S(w)`** | `followsItin_partition` |
| the exact integer endpoints of a cell, over the denominator `2·3^{\|w\|}` | `cellZ`, `cellZ_bounds`, `followsItin_iff_cellZ` (with `r_three_halves`, `g_three_halves`) |

The instance `w = MLMLMMMMMLMRLRMLMLM` at `λ = 3/2`:

| Claim of the commission | Identifier |
| --- | --- |
| cells are the open intervals with those integer endpoints | `followsItin_eq_Ioo`, `volume_cell` |
| a cell is nonempty iff its endpoints are ordered | `cell_nonempty_iff` |
| the `2^11 = 2048` candidates | `allItin`, `mem_allItin`, `card_allItin_eleven`, `countM_wordT20` |
| **exactly six of the 2048 are nonempty** | `liveItin`, `mem_liveItin`, `candidate_count` |
| **the six lengths sum to `(2/3)^19 = 524288/1162261467`** | `candidate_total_int`, `candidate_total_length` |
| the six cells are exactly `S(w) ∩ (0,1)` | `candidates_partition_survivorSet` |

All finite claims are closed by kernel `decide` on integers; no `native_decide`.

## 9. T21 (optional) — the two-step containment (`RunRational.lean`, `TwoStep.lean`)

**Easy half only, and even that with the scope stated below.**  The bridge from
the real game at `λ = 3/2` to an exact integer model:

| Claim | Identifier |
| --- | --- |
| the embedding `A ↦ A/2·3^j` and its injectivity/rescaling | `emb`, `emb_injective`, `emb_scale` |
| integer survival, action, one step, whole word | `survivesZ`, `actZ`, `stepZ`, `runZFrom`, `runZ` |
| the integer model computes the real game | `survives_emb`, `act_emb`, `step_emb`, `runFrom_emb`, `run_eq_image_runZ`, `card_run_eq_card_runZ` |
| rescaling a configuration by `2^k`, and containment as an integer subset test | `scaleZ`, `image_scaleZ`, `run_subset_run_iff` |

The instances:

| Claim | Identifier |
| --- | --- |
| the record words for `k = 2,…,6`, and a `52`-move word for `k = 7` | `record2`…`record7` |
| the configurations they produce (kernel `decide`, exact integers) | `runZ_record2`…`runZ_record7`, `card_run_record2`…`card_run_record7` |
| the depth bounds `d_{3/2}(k) ≤ 3, 5, 9, 19, 23, 52` for `k = 2,…,7` | `d_le_three`, `d_le_five`, `d_le_nine`, `d_le_nineteen`, `d_le_twentythree`, `d_le_fiftytwo` (with `card_run_le_N`) |
| the containments `2 ⊂ 3`, `3 ⊂ 5`, `5 ⊂ 7`, `4 ⊂ 6` | `record_subset_two_three`, `record_subset_three_five`, `record_subset_five_seven`, `record_subset_four_six` |

The `k = 7` word is beyond exhaustive search at depth `52`; it was found by a
beam search (`scripts/game32_beam.py`) and is not certified to be a record, only
to have length `52`, to produce seven knots, and to contain the `k = 5`
configuration.  This closes the chains `2 ⊂ 3 ⊂ 5 ⊂ 7` and `4 ⊂ 6` of the figure.

## 9b. Exact record depths for `k ≤ 4` (`RecordDepths.lean`, not commissioned)

| Claim | Identifier |
| --- | --- |
| all `3^n` words of length `n`, and membership | `allWords`, `mem_allWords` |
| an exhaustion bounds `N` | `N_le_of_allWords`, with `N_le_of_le`, `le_d_of_N_le` |
| the three exhaustions (kernel `decide +kernel`) | `N_two_le_one`, `N_four_le_two`, `N_eight_le_three` |
| the exact depths `d_{3/2}(2) = 3`, `d_{3/2}(3) = 5`, `d_{3/2}(4) = 9` | `d_two_eq_three`, `d_three_eq_five`, `d_four_eq_nine` |

Not delivered, and explicitly not claimed: the *minimality* of the depths for
`k ≥ 5` (the enumeration would need `3^18 ≈ 4·10^8` words), that the listed
configurations are *all* the record configurations at each depth, and the hard
half (exhaustiveness).  `prop:twostep` is **not** labelled certified.

## 10. Not commissioned, not attempted

The return-time tail bound, the renewal inequality, and any exponential lower
bound on `K_m` remain absent from the tree.  No weakened variant of them appears
anywhere in round 5.
