# CENSUS — round 11 (the deferred statements of the paper, and a sharper rate)

Census-first, as in every earlier round: what the inherited round-10 tree
already contained, what round 11 reuses, what round 11 adds, and — for the
items that were *not* carried to completion — a plain statement of where they
stop.  The abandonment statement is a separate document,
[`ABANDONED.md`](ABANDONED.md); this census is the positive record.

## 0. Summary of outcomes

| Paper item | Statement | Status | File |
| --- | --- | --- | --- |
| `lem:overlap` (Lemma 11) — round-1 census flagged *deferred (no work order)* | `1/√2` and `2/3` are not roots of a non-zero `{0,±1}` polynomial; `1/φ`, `1/ρ` are roots of `x²+x−1`, `x³+x²−1` | **done** | `RequestProject/Overlap.lean` |
| `cor:decide` (Corollary 7) — round-1 census flagged *deferred*, flag (G) | at a Pisot parameter the reachable configurations are finite, `N_λ` is eventually constant, `sup N_λ` is attained at a finite level | **done** (see SCRUPLES §2 for the reading of "decidable") | `RequestProject/PisotDecide.lean` |
| `prop:circle` (Proposition 4) — round-1 census flagged *deferred (no work order)* | the circle normal form `L = D∘ρ_{−g/2}`, `R = D∘ρ_{g/2}`, `M = ρ_{−1/2}∘D∘ρ_{−1/2}`, and the count of marked points | **done** | `RequestProject/CircleForm.lean` |
| `prop:immortal32` | a control sequence with infinitely many immortal births forces `N = ∞` | **done**, and for every `λ > 1`, not only `3/2` | `RequestProject/Immortal.lean` |
| `prop:square`, `prop:squaresurv` | the binary square at `λ = √2`: `x_n = (√2−1)(α_n+√2β_n)`, `(α,β) ↦ ({2β}, α)`, `ε = ⌊2β⌋`, and the survival table on the five regions | **done** | `RequestProject/Square.lean` |
| `prop:kinddim` | the kind set `K_{3/2}` is Lebesgue null and has Hausdorff dimension `≤ log 2 / log 3` | **partly done — the upper bound only**; the matching lower bound and the box dimension are **abandoned**, see `ABANDONED.md` §1 | `RequestProject/KindDim.lean` |
| `prop:lowerbound`, `cor:recursive` — the record-length bounds `d_λ(k) ≥ 2k−1` and `d_λ(k+1) ≥ d_λ(k)+2`; round 1's census recorded `d` as *defined but with nothing proved about it* (flag (F)) | as stated, under the attainability hypothesis that `d` be a genuine record length | **done** | `RequestProject/RecordLower.lean` |
| a sharper exponential rate at `λ = 3/2` (continuation of round 10's T31) | `49 ^ ⌊m/16⌋ ≤ K_{3/2}(m)`, rate `49^(1/16) ≈ 1.27537` against round 10's `26^(1/14) ≈ 1.26203` | **done**; the aspirational rate `1.29` is **abandoned**, see `ABANDONED.md` §2 | `RequestProject/ExpSharpest.lean` (+ `ExpSharpestData0…8`, `ExpSharpestChecks0…8`) |

No `sorry`, no `admit`, no new `axiom`, no `@[implemented_by]`, no
`native_decide` anywhere in the tree.

## 1. What was already present, and is reused rather than re-derived

| Inherited item | File | Used by |
| --- | --- | --- |
| `Pisot.IsPisot`, `orb_finite`, `Orb` | `Pisot.lean` | `cor:decide` |
| `run_subset` (the round-2 invariance principle), `N_le_of_le`, `N` | `Gaps.lean`, `Basic.lean` | `cor:decide` |
| the golden and plastic minimal polynomials | `Golden.lean`, `Plastic.lean` | `lem:overlap`'s positive half |
| `branch`, `f`, `posAfter`, `survivesWord` | `Basic.lean` | `lem:overlap`'s corollaries, `prop:square` |
| `card_run`, `births_le_N`, `prefixWord` | `Suffix.lean`, `Littlewood.lean` | `prop:immortal32` |
| `Sqrt2` block coordinates and `Real.sqrt 2` facts | `Sqrt2.lean` | `prop:square` |
| `Mahler.itinerary_tsum`, `orbit` (round 8) | `Mahler.lean` | `prop:square`'s first identity |
| `KindTree.card_kindWords_three_halves` (round 8: `2^n` cylinders) | `KindTree.lean` | `prop:kinddim` |
| `ExpMulti.MDoubling`, `pow_le_K_of_mdoubling`, `ExpMultiCert.mcellOK`, `mdoubling_of_cert`, `chained` | `ExpMulti.lean`, `ExpMultiCert.lean`, `ExpCert.lean` | the sharper rate |
| `Gaps.act_lt_act`, `run`, `births` | `Gaps.lean`, `Basic.lean` | `prop:circle`'s count |
| `two_mul_births_le_length_succ`, `births_le_N`, `card_run` (round 2's birth spacing) | `Gaps.lean`, `Suffix.lean` | `prop:lowerbound`, `cor:recursive` |

Nothing in the round-10 tree contained any of the seven items of §0: `rg` over
the inherited sources returns no statement about `{0,±1}` polynomials beyond
the transversality class, no statement about reachable *configurations* at a
Pisot parameter (only about the orbit), no circle model, no immortality
predicate, no binary-square coordinates at `√2`, no measure or dimension
statement about the kind set, and no certificate at `λ = 3/2` beyond round 10's
`26 ^ ⌊m/14⌋`.

## 2. What round 11 adds

| File | Lines | Contents |
| --- | --- | --- |
| `RequestProject/Overlap.lean` | 419 | `PMOne`, `PMOne.isPrimitive`, `not_root_of_primitive`, `minpoly_inv_sqrt_two`, `minpoly_two_thirds`, `not_pm_root_inv_sqrt_two`, `not_pm_root_two_thirds`, `inv_phi_root`, `inv_rho_root`; and the consequence the paper draws — `branchIter_injective`, `branchIter_injective_three_halves`, `branchIter_injective_sqrt_two` |
| `RequestProject/PisotDecide.lean` | 105 | `run_subset_Orb`, `reachable`, `reachable_finite`, `N_le_card_orb`, `N_eventually_constant`, `sup_N_isGreatest` |
| `RequestProject/CircleForm.lean` | 146 | `rot`, `Dop`, `Dop_eq`, `circle_L`, `circle_R`, `circle_M`, `card_marked` |
| `RequestProject/Immortal.lean` | 101 | `shiftSeq`, `ImmortalBirth`, `card_immortal_le_births`, `N_unbounded_of_immortal`, `N_unbounded_of_immortal_three_halves` |
| `RequestProject/Square.lean` | 479 | `bsum` and its digit lemmas, `alpha`, `beta`, `sval`, `beta_succ`, `alpha_succ`, `eps_eq_floor`, `pos_eq`, `square_normal_form`; `Spares`, the five region tables `spares_region₁…₅`, `spares_zero_iff`, `spares_one_iff`, `squaresurv_general`, `squaresurv`, `no_spare_of_exceptional` |
| `RequestProject/KindDim.lean` | 263 | `dig`, `cval`, `cyl`, `E`, `K`, `E_succ_subset`, `volume_E_le`, `volume_K`, `dexp`, `dimH_K_le` |
| `RequestProject/RecordLower.lean` | 150 | `survivesWord_take`, `births_le_one_of_length_le_two`, the chopping lemma `births_le_births_take_add_one`, `two_mul_le_of_le_N`, `d_ge_two_mul_sub_one`, `d_succ_ge_add_two` |
| `RequestProject/ExpSharpestData.lean`, `ExpSharpestData0…8.lean` | ≈ 6 400 | generated data: 2 008 cells tiling `J = [1/6, 5/6]`, each carrying 49 distinct branch words of length 16 |
| `RequestProject/ExpSharpestChecks0…8.lean` | ≈ 240 | the kernel checks, 41 groups of at most 50 cells, `decide +kernel` |
| `RequestProject/ExpSharpest.lean` | 111 | `cells_chained`, `cells_ok`, `mdoubling_three_halves_16`, `fortynine_pow_le_K`, `sharpest_rate`, `sharpest_rate_vs_round7`, `sharpest_rate_real` |

The only inherited file edited is `RequestProject/All.lean`, and only to add
imports.  No inherited definition or statement was changed.

Search programs added (untrusted, nothing depends on them):
`scripts/gen_expsharpest.py`, which writes the `ExpSharpestData*` files and the
`ExpSharpestChecks*` files, on top of the inherited `scripts/expcert_dfs.py`.

## 3. The certificate sizes, for reference

| Round | Parameter | Core interval | `T` | multiplicity | cells | rate |
| --- | --- | --- | --- | --- | --- | --- |
| 7 (`ExpLower`) | `3/2` | `[1/4, 3/4]` | 5 | 2 | 15 | `2^(1/5) ≈ 1.1487` |
| 7 (`ExpSharp`) | `3/2` | `[1/4, 3/4]` | 12 | 15 | 503 | `15^(1/12) ≈ 1.25316` |
| 10 (`ExpSharper`) | `3/2` | `[1/6, 5/6]` | 14 | 26 | 747 | `26^(1/14) ≈ 1.26203` |
| 11 (`ExpSharpest`) | `3/2` | `[1/6, 5/6]` | 16 | 49 | 2 008 | `49^(1/16) ≈ 1.27537` |

Measured growth at `λ = 3/2` (in `experiments/`, untrusted) is about
`4/3 = 1.3333` per step; nothing certifies it, and no sharpness is claimed for
any row of the table.

## 4. Where the round stops

Three things are *not* delivered and are not claimed anywhere in the tree.  The
full statement, with the reasons and the sizes attempted, is in
[`ABANDONED.md`](ABANDONED.md):

1. the lower bound `dimH K_{3/2} ≥ log 2 / log 3`, and the box dimension — only
   the null statement and the upper bound are certified;
2. the aspirational certified rate `1.29` at `λ = 3/2` — the ceiling actually
   reached is `49^(1/16) ≈ 1.27537`;
3. everything listed in `ABANDONED.md` §3–§6, which was already outstanding
   when round 11 began: the exhaustive record depths beyond `k = 4`, the
   exhaustiveness half of `prop:twostep`, the commissioned width of the
   above-`φ` parameter window, and the paper's explicitly computational
   remarks, tables and open questions.
