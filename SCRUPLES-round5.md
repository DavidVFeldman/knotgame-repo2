# SCRUPLES — round 5 (T14–T21)

Every place where the Lean statement is not a literal transcription of the
commission, and every convention that had to be fixed.  Conventions inherited
from earlier rounds (the window open at both ends, survival by strict
inequalities, `g + r = 1`) are unchanged and are not repeated here.

## 1. T14 — the survivor set

* **The cells are a list, not a set.**  `cells lam v : List (ℝ × ℝ)` is an
  explicit list of pairs, built by recursion from the right.  "At most
  `1 + #M(v)` intervals" is `length_cells_le`, a bound on the length of that
  list.  That the list really describes disjoint open intervals in increasing
  order is the invariant `Tidy` (`tidy_cells`), which the induction carries.
* **Open, and why.**  Cells are open because survival is a conjunction of
  strict inequalities; `inCells L x` is `∃ p ∈ L, p.1 < x ∧ x < p.2`.  The
  endpoints of a cell are therefore *not* in `S(v)`, and the count is unaffected
  by them.
* **The `M` step splits at `1/2`.**  `splitHalf` cuts the (at most one) cell
  straddling `1/2` into two.  This is where the single extra interval per `M`
  comes from, and it removes the point `1/2` itself from the union — which is
  correct, since `1/2` is the newborn knot's position and is deleted by `M`.
* **Total length.**  `cellsLen_cells` gives the total length exactly `r^{|v|}`
  as a sum over the list; `volume_survivorSet` restates it as
  `volume (survivorSet lam v) = ENNReal.ofReal (r^{|v|})`, using
  `survivorSet lam v = {x | 0 < x ∧ x < 1 ∧ survivesWord lam x v}`.
* **The long cell.**  `exists_long_cell` returns a *pair* `p ∈ cells lam v` with
  `p.2 - p.1 ≥ r^{|v|}/(|v|+1)` together with the fact that every point strictly
  between `p.1` and `p.2` lies in `(0,1)` and survives `v`.  The commission's
  "contains an open interval of length ≥ …" is exactly this; no separate
  interval object is introduced.

## 2. T15 — permanence

* **Ages are rendered by suffix length.**  `KnotAt lam w a x` says `w` factors
  as `p ++ M :: s` with `|s| = a`, `1/2` surviving `s` and `posAfter (1/2) s = x`.
  So "age" is the number of moves since the birth, and a knot of age `a` in a
  word of length `n` was born at position `n - a - 1` (`KnotAt.age_lt`).
* **The bridge to the configuration** is `mem_run_iff`: `x ∈ run lam w` iff
  `∃ a, KnotAt lam w a x`.  It is derived from round 1's `mem_step`, not
  re-proved.
* The commission's "plus one new knot of age `|v|` present iff `c = M` and
  `1/2` survives `v`" is the right disjunct of `knotAt_cons`, whose position
  component is pinned to `posAfter (1/2) v`; distinctness of the new knot from
  the old ones is not asserted there (it follows from `knotAt_age_inj`).

## 3. T16 — one annihilation per backward step

The commission's statement about inverse branches is proved in the *forward*
reading: `posAfter_inj` says `x ↦ posAfter lam x v` is injective on the points
surviving `v`, and `annihilation_unique` specialises it to the target `1/2`.
The inverse branches themselves appear as `invBranch`, with the disjointness of
their images recorded (`invBranch_M_of_lt`, `invBranch_M_of_ge`,
`invBranch_R_mem`, `invBranch_L_mem`) — the commission's images `[0, r)`,
`[1-r, 1]`, `[0, r/2)`, `(1 - r/2, 1]`.

## 4. T17 — the compactness criterion (the rendering the commission asked to be
recorded)

* A **left-infinite run** is a function `b : ℕ → Move`, read as ever-longer
  suffixes: `b i` is the letter `i+1` places from the end, and the last `a`
  letters form `sfx b a`.  This is the rendering the commission explicitly
  allows.
* **(i) and (ii) are the two readings of one definition.**
  `InfinitelyManyKnots lam` says the set of `a` with `b a = M` and `1/2`
  surviving `sfx b a` is infinite (forward reading: a knot of age `a` is
  present); `InfinitelyManyAnnihilations lam` says infinitely many *points* are
  annihilated, i.e. the map `a ↦ posAfter (1/2) (sfx b a)` has infinite range on
  that set (backward reading).  `infinitelyManyKnots_iff_annihilations` proves
  them equivalent; the content of the equivalence is exactly T16 (injectivity),
  and it is the only place where `1 < λ` is needed.
* **(iii)** is `BoundedAgeWitnesses lam`: a bound `A : ℕ → ℕ` and, for each `k`,
  a word carrying knots of `k` distinct ages, the `j`-th of which is at most
  `A j`.  "Pointwise bounded in `k`" is that `A` does not depend on `k`.
* **The compactness step** `(iii) → (i)` is carried out with a non-principal
  ultrafilter (`Filter.hyperfilter` on `ℕ`) rather than by extracting a diagonal
  subsequence: `Move` is finite and the ages are bounded, so letters and ages
  have ultrafilter limits and the witnesses agree with the limit run on
  ever-longer suffixes.  This is a different bookkeeping for the same argument;
  the commission permits either.
* **`N_λ = ∞`** is rendered as unboundedness, `∀ K, ∃ n, K ≤ N lam n`
  (`N_unbounded_of_infinitelyManyKnots`), rather than as a statement about a
  supremum in `ℕ∞`.

## 5. T18 — the density criterion

* **Conditional, and flagged as such.**  `KindDense lam` is an explicit
  hypothesis of both conclusions and is certified for no specific `λ`.  At any
  Pisot parameter it is false (the kind orbit of `1/2` is finite there), so the
  theorem is not vacuous but is also not instantiated anywhere.
* **The shape of the hypothesis.**  "Every nonempty open subinterval of `(0,1)`
  contains a kind endpoint" is written with `0 ≤ c < d ≤ 1` and the conclusion
  `c < Φ_u(1/2) < d`, i.e. over closed-ended parameters `c, d` with an open
  target.  This is equivalent to the commission's phrasing and is what the T14
  long cell delivers.

## 6. T19 — the two consequences

* **(a)** `deficit_law` is stated for a *pair* `x < y` of points surviving the
  move, since that is what the gap law gives.  The commission's proviso ("no
  death, no range-extending birth") is isolated in `step_extremes`, which shows
  that under it the images of the old extremes are the extremes of the new
  configuration; the two together are the corollary.  The birth clause of the
  proviso is `m = M → act m x ≤ 1/2 ≤ act m y`.
* **(b) reported, not repaired.**  The two sufficient conditions of `lem:free`
  hold for every `λ > 1` (`actsAs_M_R_of_forall_lt`, `actsAs_M_L_of_forall_gt`).
  The **converses are false as literally stated for `λ ≥ 3/2`**:
  `actsAs_M_R_converse_fails` exhibits the one-knot configuration `{r}`, which
  `M` and `R` delete alike, although `r ≥ r/2`.  The obstruction is the position
  of `1 - r/2` relative to `r`, which the paper's proof flags: when
  `r ≤ 1 - r/2` a knot in `[r, 1 - r/2]` dies under both moves, and the paper's
  argument at that point appeals to a knot in `(1 - r/2, 1]` that need not
  belong to `C`.  The biconditionals `actsAs_M_R_iff`, `actsAs_M_L_iff` are
  therefore stated under `1 < λ < 3/2`.

## 7. T20 — the candidate cells

* **Itineraries are Booleans, one per `M`**: `false` = lower branch
  (`x < r/2`), `true` = upper branch (`1 - r/2 < x`).  `FollowsItin` also
  requires the *final* point to lie in `(0,1)`, which is what makes the cells
  partition `S(w)` rather than cover it.
* **The instance is the commission's word** `w = MLMLMMMMMLMRLRMLMLM`
  (`wordT20`), which is the same word as `record5` in `TwoStep.lean`.
* **Exact arithmetic.**  At `λ = 3/2` the cell of an itinerary is the open
  interval with endpoints `(cellZ w t).1 / (2·3^{|w|})` and
  `(cellZ w t).2 / (2·3^{|w|})` (`followsItin_eq_Ioo`); a candidate is genuine
  exactly when those integers are in order (`cell_nonempty_iff`).  The two
  finite claims — six live candidates out of `2^11`, and total length
  `(2/3)^19` — are kernel `decide` on integers.  The total length is stated as
  the sum of `(cellZ w t).2 - (cellZ w t).1` over the live itineraries divided
  by `2·3^19`, matching `volume_cell`.

## 8. T21 — the two-step containment: scoping

This is the item where the delivered statement differs most from the
commission's wording, so it is spelled out in full.

1. **The paper's record words are not in the source materials.**  Neither the
   commission, nor `knotgame.tex`, nor anything else in the tarball lists the
   seven words of Figure `fig:records32`; the figure is an included graphic.
   Every word used here was therefore found independently, by search over the
   exact integer model of `RunRational.lean`
   (`scripts/game32_bfs.py`, `scripts/game32_records.py`,
   `scripts/game32_beam.py`).  The Lean tree does not depend on the searches:
   each word is re-run inside the kernel and every claim about it is checked
   there.
2. **`k = 2, …, 6`**: exhaustive breadth-first search over reachable
   configurations, deduplicated at each depth; each word is the first, in the
   order `L < M < R`, attaining its knot count at the least depth at which that
   count occurs.  The lengths `3, 5, 9, 19, 23` agree with the values of
   `d_{3/2}(k)` quoted in the paper.
3. **`k = 7`**: exhaustive search is out of reach at depth `52` (the layer sizes
   grow by a factor of about `1.35` per move: `3838` configurations at depth 18,
   more than `10^8` at depth 52, and dominance pruning — discarding a
   configuration contained in another at the same depth, which is sound because
   the one-step map is monotone for inclusion — removes only about half of
   them).  `record7` was found by a *beam* search and is not certified to be a
   record: what is certified is that it has length `52`, produces seven knots
   (`card_run_record7`), hence `d_{3/2}(7) ≤ 52`, and that its configuration
   contains the `k = 5` one (`record_subset_five_seven`).
4. **Containment is between point sets.**  `run (3/2) record5 ⊆ run (3/2) record7`
   compares the two configurations as subsets of `(0,1)`; `record7` is not an
   extension of `record5` on the right, and the five shared points are shared as
   positions, not as knots with a common history.  The same holds of the other
   three containments.  With `record_subset_five_seven` the chains of the figure
   are `2 ⊂ 3 ⊂ 5 ⊂ 7` and `4 ⊂ 6`, as the commission lists them.
5. **Minimality.**  `TwoStep.lean` certifies only upper bounds `d_{3/2}(k) ≤ |w|`.
   `RecordDepths.lean` adds the matching lower bounds for `k ≤ 4` — by
   exhausting all `3^n` words of length `n ≤ 8` in the kernel — giving
   `d_{3/2}(2) = 3`, `d_{3/2}(3) = 5`, `d_{3/2}(4) = 9`.  For `k ≥ 5` the
   enumeration is too large (`3^18 ≈ 4·10^8` words for `d_{3/2}(5) = 19`) and
   only the upper bound is certified.
6. **The hard half is not attempted**, and `prop:twostep` — which quantifies
   over *all* record configurations — is **not** labelled certified anywhere in
   the tree.

## 9. What is not there

The return-time tail bound, the renewal inequality and any exponential lower
bound on `K_m` remain absent, as in round 4; no weakened variant of them
appears.
