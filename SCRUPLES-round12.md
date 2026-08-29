# SCRUPLES — round 12

Round 12 (`RequestProject/KindDimLower.lean`) was interrupted before it wrote
its paperwork.  These scruples were reconstructed in round 13 by reading the
source; where they state an intention they state only what the source
demonstrably does.  Conventions inherited from earlier rounds (survival by
strict inequalities, `g + r = 1`, `K λ m` for the number of surviving branch
words of length `m`, the kind set `K` and the cylinder apparatus of
`KindDim.lean`) are unchanged and are not repeated.

## 1. What is proved, precisely

* `le_dimH_K : ENNReal.ofReal dexp ≤ dimH K` and
  `dimH_K_eq : dimH K = ENNReal.ofReal dexp`, where `dexp = Real.log 2 / Real.log 3`
  and `K` is `KindDim.K`, the kind set at `λ = 3/2` **as `KindDim.lean`
  defines it**: the intersection `⋂ n, E n` of the level-`n` unions of
  surviving ternary cylinders.  No claim is made here that `K` coincides with
  any other description of the kind set; that identification, to the extent it
  is made anywhere, belongs to `KindDim.lean` and `KindTree.lean`.
* Everything is at `λ = 3/2` only.  The binary structure of the tree is what
  the argument runs on, and it is special to `3/2`.

## 2. The coding map is a choice of coding, not the canonical one

* The survival tree has exactly two children at each node (round 8's
  `Ternary.exists_unique_fatal`: exactly one of `L`, `M`, `R` is fatal at a
  reachable position).  `nextMove y b` picks them out; `b = false` is the one
  with the smaller base-three digit.  **The ordering is a convenience, not a
  claim**: only `nextMove y false ≠ nextMove y true` is ever used.
* `G t = ⨆ n, cval (wordOf t n)` is defined for *every* real `t`, not only for
  `t ∈ [0,1)`; outside `[0,1)` its value is meaningless and is never used.
  Totality is what keeps `G` measurable without a subtype.
* The binary digits of `t` are read off the integer parts `⌊2^n t⌋` (`flr`,
  `bitAt`).  No choice principle is involved in the digits.  `G` is *not*
  claimed to be injective, and it is not: dyadic rationals have two expansions
  in the usual way.  Nothing in the argument needs injectivity — only that the
  preimage of a level-`n` cylinder is a single dyadic interval
  (`wrd_injective`).

## 3. The measure

* `kindMeasure := Measure.map G (volume.restrict (Ico (0:ℝ) 1))`.  It is a
  probability measure carried by `K` (`kindMeasure_K : kindMeasure K = 1`).
  It is **not** claimed to be the `log 2 / log 3`-dimensional Hausdorff measure
  restricted to `K`, nor to be the unique self-similar measure on `K`; it is
  simply *a* measure with enough mass and a good enough Frostman estimate.
* The Frostman constant is `4`: a set of diameter at most `3^{-n}` meets at
  most four level-`n` triadic cylinders.  Four is not optimal (two would do
  with more care about cylinder endpoints); only finiteness matters, and the
  file says so.
* The mass distribution principle is used in Mathlib's form,
  `MeasureTheory.Measure.le_hausdorffMeasure`, applied to the scaled measure
  `(1/8) • kindMeasure` at scale `1/3`.  The scaling absorbs the constant `4`;
  no sharpness is claimed for `1/8` either.

## 4. Deviations from the paper

* **The paper gives no proof of the lower bound** — `prop:kinddim` asserts the
  value `log 2 / log 3` and appeals to the standard self-similarity heuristic.
  The Lean proof is therefore not a transcription of anything; it is an
  argument supplied here.  It is flagged as such because a reader comparing
  paper and sources will find no correspondence line by line.
* **`dexp` is `Real.log 2 / Real.log 3`, coerced by `ENNReal.ofReal`**, because
  `dimH` takes values in `ℝ≥0∞`.  The paper writes `log 2 / log 3` with the
  base of the logarithm unspecified; the ratio is base-independent.
* **The box dimension is not treated in this file.**  An early draft of the
  file's docstring announced `coverK_lower`, `coverK_upper` and
  `box_dimension_triadic`; those declarations were never written, and round 13
  removed the promise from the docstring (the only edit round 13 made to this
  file) and proved the box-dimension statements in
  `RequestProject/KindBox.lean` instead.  This is recorded here rather than
  quietly fixed, because a stale forward reference in a docstring is exactly
  the kind of thing that turns into a false claim downstream.

## 5. Paperwork

No census, scruples or axiom audit was produced by round 12 itself.  The
census is `CENSUS-round12.md` and the axiom report is
`AXIOM-AUDIT-round12.md`, both written in round 13 from the source as it
stands.  They are marked as reconstructions in their own headers.
