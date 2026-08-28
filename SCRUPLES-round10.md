# SCRUPLES — round 10

Every place where a round-10 Lean statement is not a literal transcription of
the paper, and every convention that had to be fixed.  Conventions inherited
from earlier rounds (the window open at both ends, survival by strict
inequalities, `g + r = 1`, `N_λ` unbounded written `∀ K, ∃ n, K ≤ N λ n`,
`K λ m` for the number of surviving branch words of length `m`) are unchanged
and not repeated.  Each item also appears in the docstring of the file it
belongs to.

## 1. T30 — no recurrence (`prop:norecur`)

* **The round-8 dyadic invariant is reused; the paper's arithmetic is not
  re-derived.**  The commission asks for exactly this.  The paper argues that a
  recurrence after `B` moves makes the position the fixed point
  `N(S)/(3^B − 2^B)` of an affine composite, then uses the telescoping identity
  `Σ_{j=1}^B 3^{B−j} 2^{j−1} = 3^B − 2^B` and the oddness of `3^B − 2^B` to
  reduce to the fixed points `0` and `1`, which no knot occupies.  The Lean
  proof reaches the same conclusion from `Ternary.Dyadic` alone: a point
  reachable in `n` moves is an odd multiple of `2^-(n+1)`
  (`Ternary.dyadic_posAfter`, round 8), the level `n` is *determined* by the
  point (`dyadic_level_unique`), and a block of `k > 0` further moves raises the
  level by exactly `k` (`dyadic_posAfter_of_dyadic`, `posAfter_length_eq`).  So
  a recurrence would identify two different levels.  **No `3^B − 2^B`
  computation appears in the Lean file**; the fixed points `0` and `1` of the
  paper never arise, because a dyadic point of level `n` is neither.  This is a
  different proof of the same statement, and is flagged as such.
* **Hypothesis form.**  `no_recurrence` is stated for any `x` carrying the
  invariant, `Dyadic n x`, rather than for "a knot".  That is the more general
  statement; `dyadic_of_knotAt` supplies the hypothesis for an actual knot, and
  `no_recurrence_knotAt`, `no_identity_block`, `no_identity_block_config` are
  the game-level readings.  `no_identity_block` is stated for a point of
  `run (3/2) w`, i.e. a knot of a reachable configuration, which is the form the
  paper cites against the candidate mechanism for `prop:twostep`.
* **"Same position twice" is formalised as "a nonempty block of moves does not
  return the position to itself"** (`no_recurrence`), together with the
  pairwise/injective forms `positions_pairwise_ne` and
  `knot_positions_injective` (the map `i ↦ position after `i` iterations of a
  block` is injective).  Nothing is claimed about *distinct* knots occupying the
  same position at different times.
* Only `λ = 3/2` is treated.  The invariant is specific to `3/2`.

## 2. T31 — the sharper certificate at `λ = 3/2`

* **What is improved, and by how much.**  Round 7 certified
  `15 ^ ⌊m/12⌋ ≤ K_{3/2}(m)` (rate `15^(1/12) = 1.25316…`).  Round 10 certifies
  `26 ^ ⌊m/14⌋ ≤ K_{3/2}(m)` (`twentysix_pow_le_K`, rate
  `26^(1/14) = 1.26203…`).  The comparison is itself certified, in integer form
  (`sharper_rate : 15^14 < 26^12`) and in real form
  (`sharper_rate_real : (15:ℝ)^(1/12) < (26:ℝ)^(1/14)`).
* **The core interval changed** from round 7's `J = [1/4, 3/4]` to
  `J = [1/6, 5/6]`.  Both are legitimate cores; the wider one happens to admit
  the same multiplicity at fewer cells (747 against 1016).  No claim is made
  that either is optimal.
* **`⌊m/14⌋`, not `m/14`.**  As in round 7, the exponent is natural-number
  division; the bound is a floor bound and says nothing between multiples of 14.
* **No sharpness.**  `26` at `T = 14` is the largest multiplicity *this search*
  found at a kernel-feasible size; the true growth rate of `K_{3/2}` is measured
  at about `4/3` in `experiments/` and is not certified anywhere.  The
  commissioned target of rate `1.29` was **not** reached; the ceiling actually
  hit is tabulated in `CENSUS-round10.md` §3.
* **The search is untrusted.**  `scripts/gen_expsharper.py` merely writes the
  data; the kernel re-checks every cell over exact rationals
  (`decide +kernel`), in 15 groups because one ungrouped reduction does not go
  through.

## 3. T32 — above the golden ratio

* **The commissioned window is not the certified window.**  This is the round's
  main deviation and it is stated at the top of `RequestProject/ExpAbove.lean`
  as well as here.  Commissioned: `[17/10, 7/4]`.  Certified:
  `[3457/2000, 4331/2500] = [1.7285, 1.7324]`.  The certified window is above
  the golden ratio (`golden_lt_window`) and contains `√3`
  (`sqrt_three_mem_window`), so the commission's *stated purpose* — a certified
  exponential kind count at a parameter above `φ`, `√3` in particular — is met;
  its stated *width* is not.  The parameters tried and the exact failure
  locations are in `CENSUS-round10.md` §4.
* **A weakened doubling hypothesis.**  `ExpCount.Doubling` asks for two distinct
  branch words of a *common* length `T`.  Above `φ` no such certificate was
  found at any feasible `T`.  `ExpVar.VDoubling lam a b T` instead asks for two
  words of lengths *at most* `T` that **diverge** (`Divergent u v`: neither is a
  prefix of the other), both of whose images return to `[a,b]`.  Divergence is
  what the counting argument actually needs
  (`append_ne_of_divergent`, `two_mul_kappa_le_var`), and it is strictly weaker
  than equal-length distinctness.  The conclusion is correspondingly the *same*:
  `2 ^ ⌊m/T⌋ ≤ K λ m` (`two_pow_le_K_of_vdoubling`).
* **`T` is the worst return time, not a typical one.**  `Tbound = 18` is the
  maximum over all 17 141 point cells; most cells return in far fewer steps, so
  the certified rate `2^(1/18) ≈ 1.0393` is a gross underestimate of the true
  growth.  No sharpness whatsoever is claimed.
* **The core interval `J = [43/100, 57/100]` is not an arbitrary choice.**  It
  must lie inside the branching window `(1 − 1/λ, 1/λ)` for every parameter of
  the window: for the wider `J = [2/5, 3/5]` there are points of `J` whose orbit
  never branches at all (above `φ` the survivor set of the hole is nonempty),
  and the search demonstrably stalls.
* **Interval arithmetic in the parameter as well as the point**, as in round 7,
  so that one certificate serves a whole parameter cell; the window is split
  into 180 parameter cells adaptively.  Soundness of the two-level check is
  `vdoubling_of_cert` (one parameter cell) and `vdoubling_of_window` (a chained
  list of them).
* **`√3` enters only through `sqrt_three_mem_window`,** proved by squaring the
  two rational endpoints.  Nothing arithmetic about `√3` is used, and no
  irrationality or Pisot property is invoked.
* **`K_unbounded_above` is a corollary of the floor bound**, not an independent
  result.
* **The searches are untrusted.**  `scripts/expvar_search.py` and
  `scripts/gen_expabove.py` write inert data; the kernel re-checks all 180
  parameter cells over exact rationals in 36 groups (`decide +kernel`), and
  re-checks that they tile the window (`pcells_chained`).

## 4. File discipline (the parallel-run clause)

All new Lean material is in new files: `NoRecurrence.lean`, `ExpSharper.lean`,
`ExpSharperData.lean`, `ExpVar.lean`, `ExpAbove.lean`, `ExpAboveChecks.lean`,
`ExpAboveData.lean` and `ExpAboveData0.lean`…`ExpAboveData11.lean`.  The only
inherited Lean file edited is `RequestProject/All.lean`, and only by adding
three `import` lines.  `Translation.lean`, `PeriodicYield.lean` and
`TwoStep.lean` were not opened for editing, and no `Fourier*`/`Floor*` file was
created.

**Why twelve data files.**  Not taste: the T32 data as a single 18 213-line file
could not be elaborated (over 17 minutes and 8.6 GB before being abandoned).
Split into twelve, elaboration is ≈ 300 s in total.  The split is mechanical —
`scripts/gen_expabove.py` emits three check-groups (15 parameter cells) per
file, and `ExpAboveData.lean` only concatenates the 36 group definitions.

## 5. What round 10 does *not* claim

* Nothing about the exact growth rate of `K_λ` at any parameter, at `3/2` or
  above `φ`.
* Nothing about parameters outside `[3457/2000, 4331/2500]` above `φ`; in
  particular the failures near `1.7282`, `1.7325`, `1.7328` are failures *of the
  search*, and are not certified to be genuine obstructions.
* Nothing about `prop:twostep` itself; T30's `no_identity_block` only rules out
  the one candidate mechanism the paper mentions.
