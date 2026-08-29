# CENSUS — round 12 (the Hausdorff lower bound for the kind set)

Round 12 was a single-item session, and it was **interrupted**: it produced
`RequestProject/KindDimLower.lean`, which entered the import closure and has
built under continuous integration ever since, but no census, scruples or
axiom audit was written for it.  This document, written in round 13, is that
missing census.  It is a reconstruction from the source file itself and from
the surrounding rounds; where round 13 could not determine what round 12
intended, this document says so rather than guessing.

## 0. Summary of outcome

| Paper item | Statement | Status | File |
| --- | --- | --- | --- |
| `prop:kinddim` (lower half) | `log 2 / log 3 ≤ dimH K_{3/2}` | **done** (`le_dimH_K`) | `RequestProject/KindDimLower.lean` |
| `prop:kinddim` (exact value) | `dimH K_{3/2} = log 2 / log 3` | **done** (`dimH_K_eq`), combining round 11's `dimH_K_le` with the above | `RequestProject/KindDimLower.lean` |
| `prop:kinddim` (box dimension) | both box dimensions equal `log 2 / log 3` | **not delivered by round 12**; delivered by round 13, `RequestProject/KindBox.lean` | — |

No `sorry`, no `admit`, no new `axiom`, no `native_decide` in the file.

## 1. What was already present, and is reused rather than re-derived

| Inherited item | File | Used for |
| --- | --- | --- |
| `KindDim.dig`, `cval`, `cyl`, `E`, `K`, `dexp`, `E_succ_subset`, `volume_K`, `dimH_K_le` | `KindDim.lean` (round 11) | the ambient objects; `dimH_K_eq` is `dimH_K_le` plus `le_dimH_K` |
| `KindTree.kindWords`, `card_kindWords_three_halves` | `KindTree.lean` (round 8) | the `2^n` cylinder count that fixes the exponent |
| `Ternary.exists_unique_fatal` | `Ternary.lean` (round 8) | exactly one of `L`, `M`, `R` is fatal at a reachable position, hence every node of the survival tree has exactly two children |
| `survives`, `survivesWord`, `posAfter`, `act`, `Move` | `Basic.lean` | the survival tree itself |
| `MeasureTheory.Measure.le_hausdorffMeasure` | Mathlib | the mass distribution principle |

Nothing in the round-11 tree contained a measure on the kind set, a coding map
from `[0,1)` onto it, or any lower bound on `dimH K`; round 11's
`ABANDONED.md` §1 recorded the lower bound as abandoned, which is precisely
what round 12 then went and proved.  (That staleness is corrected in round 13;
see `ABANDONED.md` §1 as it now stands.)

## 2. What round 12 adds

`RequestProject/KindDimLower.lean`, 658 lines, namespace `KnotGame.KindLower`:

| Group | Declarations |
| --- | --- |
| the two children of a node | `nextMove`, `nextMove_ne`, `nextMove_injective`, `survives_nextMove` |
| positions along a word | `pos`, `posAfter_mem_Ioo`, `pos_mem_Ioo`, `unique_fatal_pos` |
| binary digits of a real | `flr`, `bitAt`, `flr_succ_cases`, `flr_succ_eq`, `flr_congr_of_succ`, `flr_congr_add`, `flr_congr_of_le`, `bitAt_congr` |
| the coding map | `wordOf`, `wordOf_succ`, `wordOf_length`, `wordOf_survives`, `wordOf_mem_kindWords`, `wordOf_le_append`, `cval_mem_cyl`, `cyl_append`, `G`, `cval_le_one`, `bddAbove_cval`, `cval_wordOf_mem_cyl`, `monotone_cval_wordOf`, `G_mem_cyl`, **`G_mem_K`** |
| measurability | `wrd`, `flr_of_div`, `wordOf_congr`, `wordOf_eq_wrd`, `measurable_flr`, `measurable_cval_wordOf`, `tendsto_cval_wordOf`, `measurable_G` |
| the measure | **`kindMeasure`** (`= Measure.map G (volume.restrict (Ico 0 1))`), `measurableSet_E`, `measurableSet_K`, **`kindMeasure_K : kindMeasure K = 1`** |
| cylinder arithmetic | `cnum`, `dig_injective`, `cnum_nonneg`, `cnum_lt`, `cval_eq_cnum`, `cnum_injective`, `flr_eq_of_wordOf_eq`, `wrd_injective` |
| the Frostman estimate | **`kindMeasure_le`**, `abs_sub_le_of_ediam`, `exists_pow_bracket`, **`kindMeasure_le_of_ediam`** |
| the conclusion | **`le_dimH_K : ENNReal.ofReal dexp ≤ dimH K`**, **`dimH_K_eq : dimH K = ENNReal.ofReal dexp`** |

The only inherited file edited was `RequestProject/All.lean`, and only to add
the import.

## 3. The argument, in one paragraph

At every reachable position exactly one of the three moves is fatal, so the
survival tree at `λ = 3/2` is a binary tree; `nextMove y b` names its two
children.  The binary digits of `t ∈ [0,1)` therefore descend the tree, giving
a word `wordOf t n` of length `n` at every level and, in the limit, a point
`G t = ⨆ n, cval (wordOf t n)` of the kind set (`G_mem_K`).  Push Lebesgue
measure on `[0,1)` forward along `G` to get `kindMeasure`, a probability
measure carried by `K` (`kindMeasure_K`).  A set of diameter at most `3^{-n}`
meets at most four level-`n` cylinders, and each level-`n` cylinder pulls back
to a single dyadic interval of length `2^{-n}`, so
`kindMeasure s ≤ 4 · 2^{-n}` whenever `ediam s ≤ 3^{-n}`
(`kindMeasure_le_of_ediam`).  Mathlib's mass distribution principle then gives
`log 2 / log 3 ≤ dimH K`, and with round 11's upper bound, equality.

## 4. Where round 12 stops

* The box dimension is **not** treated.  (An early draft of the file's
  docstring promised `coverK_lower`, `coverK_upper` and
  `box_dimension_triadic`; the session ended before they were written, and the
  names never existed.  Round 13 corrected the docstring and supplied the box
  dimension in `RequestProject/KindBox.lean`.)
* The constant `4` in the Frostman estimate is not optimised, and nothing is
  claimed about the measure `kindMeasure` beyond the two facts used
  (`kindMeasure K = 1` and the diameter estimate) — in particular it is not
  identified with the natural `log 2 / log 3`-dimensional Hausdorff measure on
  `K`, and no such identification is claimed.
* Nothing outside `λ = 3/2` is treated.
