# CENSUS — round 17 (T47, T48, T49)

Census-first, as required. What follows is what was looked for in the inherited
tree and in Mathlib, what was found and reused, and what had to be written.

## 1. T47 — "every point of `(0,1)` has a legal move"

Looked for, in the inherited tree:

* `KnotGame.act_mem_Ioo` (`RequestProject/Pisot.lean`, line 34) —
  **found and reused verbatim.** It is exactly the statement the commission
  suspected already existed: `1 < lam → x ∈ Ioo 0 1 → survives lam m x →
  act lam m x ∈ Ioo 0 1`, for an arbitrary move `m`. Nothing in this round
  re-proves it.
* A statement of the form "some move is legal at `x`". Searched for
  `exists.*survives`, `survives.*exists`, `legal`, and inspected
  `SurvivorSet.lean`, `Branching.lean`, `Backward.lean`,
  `BranchingCount.lean`, `Density.lean`. **Not found in that shape.** What the
  tree has instead are counting statements about *branch words* surviving from
  a point (`branchWords`, `BranchingCount`), and those are about words legal
  from a point rather than about a single letter being available at an
  arbitrary point of `(0,1)`. Rather than route through a counting lemma, the
  one-letter fact is proved directly here: `g_lt_r` (the deleted proportion is
  below the retained one exactly when `lam < 2`) plus a two-case split on
  `x < r lam`. Three lines.
* `KnotGame.g`, `KnotGame.r`, `r_pos`, `r_lt_one`, `lam_mul_r`
  (`Basic.lean`, `Threshold.lean`) — reused.
* `survives`, `act`, `Move` (`Basic.lean`) — reused; the statement of T47 is
  phrased in exactly those terms, as the commission wrote it.

Written here: `g_lt_r`, `nextMove`, `survives_nextMove`, `orbit`,
`orbit_mem_Ioo`, `no_contracting_weight`.

From Mathlib: `exists_pow_lt_of_lt_one` (for `0 < eps` and `th < 1` there is
`n` with `th ^ n < eps`) — checked to exist at this toolchain and used to close
the decay. Nothing heavier than `Nat.rec` (through the equation compiler) is
used to build the orbit, as the commission asked.

## 2. T48 — sharpness of the contraction constant

* `KnotGame.Contraction.P` (`Contraction.lean`, line 71) — the normalised
  operator, reused; not restated.
* `KnotGame.Contraction.lipschitz_contraction` (line 145) — the theorem whose
  constant is being certified sharp. Read, not edited, not re-proved.
* Looked for an existing sharpness or lower-bound statement anywhere in the
  tree (`rg 'sharp' RequestProject`, plus `WindowSharp.lean`, `ExpSharp*.lean`,
  which concern the certified exponential rate and not this operator).
  **Not found**; the appendix records it as unformalised, which matches.

Written here: `P_id`, `dist_P_id`, `not_lipschitzWith_P_id`. Together seven
lines of proof; `P_id` is `funext` + `ring` after unfolding `P`.

From Mathlib: `LipschitzWith.dist_le_mul`, `Real.dist_eq`, `abs_mul`.

## 3. T49 — the density criterion at a Pisot parameter

The commission asked for the exact relationship between `Orb lam` and the
endpoint set of `DenseFrom` to be checked before anything was written. It was:

* `KnotGame.Orb` (`Pisot.lean`, line 29) is
  `{x | ∃ w : List Move, survivesWord lam (1/2) w ∧ posAfter lam (1/2) w = x}`.
* `KnotGame.KindDense` (`Density.lean`, line 37) is
  `∀ c d, 0 ≤ c → c < d → d ≤ 1 → ∃ u : List Move, survivesWord lam (1/2) u ∧
  c < posAfter lam (1/2) u ∧ posAfter lam (1/2) u < d`.

These are stated through *the same* two functions, `survivesWord` and
`posAfter`, from *the same* base point `1/2`, with no side condition on either
side. So `KindDense lam` says precisely that every subinterval of `(0,1)`
contains a point of `Orb lam`; the bridge is `Iff.rfl` and is recorded as
`mem_orb_iff`. **No new definition was introduced and neither inherited
definition was touched.**

* `KnotGame.BackwardClosure.DenseFrom` (`BackwardClosure.lean`, line 107) is
  the *branch-word* form, through `branchSurvivesWord` and `rapp`. It is a
  genuinely different expression, and the tree already bridges it:
  `BackwardClosure.denseFrom_half_imp_kindDense` (line 121). That direction
  carries **no hypothesis on `lam`**, so it, and not the round-15 equivalence
  `denseFrom_half_iff_kindDense` (line 199, which needs `1 < lam` for its other
  direction), is what is used. See SCRUPLES §3.
* `KnotGame.orb_finite` (`Pisot.lean`, line 185) — reused as the Pisot input.
  Not restated, not edited.
* Looked for "a finite set is not dense in an interval" in Mathlib in a form
  that applies here. The available statements are about the topological
  `Dense`/`DenseRange`/`interior` predicates (`Set.Finite.isClosed`,
  `dense_iff_closure_eq`, and the density of a set with empty interior), and
  `KindDense` is a bespoke interval-hitting predicate, not `Dense`. Rather than
  build the translation to the topological predicate — which would have needed
  a lemma of its own about `Orb` and the subspace topology of `(0,1)` — the
  elementary pigeonhole is done directly: `n = |Orb| + 1` disjoint intervals
  `(k/n, (k+1)/n)`, one orbit point in each, injective by disjointness, and
  `Finset.card_le_card` on the image. That is the whole of
  `not_kindDense_of_orb_finite`.

Written here: `mem_orb_iff`, `not_kindDense_of_orb_finite`,
`not_denseFrom_half_of_finite`, `not_kindDense_of_isPisot`,
`not_denseFrom_half_of_isPisot`.

From Mathlib: `Finset.card_le_card`, `Finset.card_image_of_injective`,
`Set.Finite.mem_toFinset`, `Fin.ext`, `div_le_one`.

## 4. What was NOT done

Nothing from `UNBUILT.md`. Nothing about `N lam` at non-Pisot parameters,
nothing about Question 50, nothing about `nu`. No inherited module was edited,
so operating rule 9 was not triggered.
