# COMMISSION: knotgame round 2 — order, gaps, and the scheduling bound

## Ground rules (unchanged from round 1)

- **Tarball is ground truth.** The enclosed Lean project is the certified round-1
  development. Build on it; do not re-derive what it already proves. Census
  first: audit what exists, report the census, then extend.
- **Report rather than repair.** If a target statement appears false,
  unprovable as stated, or infeasible for the kernel, report that finding with
  a minimal reproduction. Do not weaken a statement to make it go through
  and do not substitute a neighbouring statement. A documented failure is a
  deliverable (see PLASTIC-REPORT.md from round 1 for the model).
- **No `sorry`, no `admit`, no new axioms, no `native_decide`.** Acceptance is
  a semantic axiom audit: `#print axioms` on every top-level target must show
  at most `propext`, `Classical.choice`, `Quot.sound`.
- **SCRUPLES.** Docstrings state exactly what is proved, including hypotheses
  (per-run scoping, open-interval survival conventions, closed deleted
  intervals), and nothing more.

## Setting (as in round 1)

Fixed `λ ∈ (1,2)`, maps `f₀ x = λ*x`, `f₁ x = λ*x - (λ-1)`; moves L, M, R with
closed deleted intervals; knots born at `1/2`; survivor and configuration
definitions as in the round-1 development. Reuse those definitions verbatim.

## Targets, in dependency order

**T1 (order).** Each move, restricted to its survivors, is strictly
order-preserving: if `x < y` both survive move `c`, then `image c x < image c y`.
For L, R this is monotonicity of an affine map with positive slope; for M,
survivors below the deleted interval map into `(0, 1/2)` and survivors above it
into `(1/2, 1)`.

**T2 (gap law).** If `x < y` both survive move `c` then
`image c y - image c x = λ*(y-x)` unless `c = M` and `x` lies below the deleted
interval while `y` lies above it, in which case
`image c y - image c x = λ*(y-x) - (λ-1)`. Pure case analysis on affine maps.

**T3 (one service per move).** For an ordered finite set of survivors, at most
one consecutive pair straddles an M (has members on opposite sides of the
deleted interval). Proof shape: the below-group is an initial segment of the
order (by T1's side classification), so at most one consecutive pair crosses
the boundary.

**T4 (birth spacing) — census first.** Round 1 certified `d ≥ 2k-1` and
`d(k+1) ≥ d(k)+2` (or close variants). Audit; reuse if present in usable form;
otherwise prove: consecutive surviving births are at least 2 apart, because a
knot born at `t` dies if move `t+1` is M (`1/2` lies strictly inside M's
deleted interval for every `λ ∈ (1,2)`).

**T5 (scheduling theorem).** If a run reaches `k` simultaneous knots at time
`n`, and every two coexisting knots are at distance `≥ δ > 0` throughout the
run, and `W` satisfies `λ^W * δ ≥ 1`, then `k ≤ W + ⌈W/2⌉ + 1`.
Proof shape (paper Section "Order, gaps, and a scheduling bound", enclosed):
knots of age ≥ W are alive through the last W moves; each consecutive pair of
them must straddle some move of the window (T2 + distances < 1 + `λ^W δ ≥ 1`),
each move serves at most one such pair (T3), so (old knots) − 1 ≤ W; knots of
age < W number at most ⌈W/2⌉ (T4). Formalise the window bookkeeping in
whatever way is most natural for the round-1 run/configuration encoding; the
combinatorial core is a pigeonhole from a finite injection.

**T6 (golden ratio, effective bound).** Using the round-1 certified five-point
orbit of `1/2` at `λ = φ`: all knot positions lie in the orbit; distinct
coexisting knots (round-1 distinctness lemma) are therefore at distance
`≥ δ₀ = φ - 3/2`; and `φ^5 * (φ - 3/2) = φ²/2 ≥ 1` — an exact identity via
`φ² = φ + 1`, so `W = 5` works with no numerics. Conclude `N_φ ≤ 9`.
Consistency remark for the docstring: round 1 proved the sharp value 2; this
is a strictly weaker bound by an independent argument, and that is the point.

**T7 (optional, plastic).** The analogue at the plastic number needs the
153-point orbit closure and its minimum gap in ℚ(ρ). Round 1 found the
25,525-configuration closure infeasible for the kernel; the 153-point orbit
may or may not be. Attempt only after T1–T6 are secured; an infeasibility
report in the round-1 style is a fully acceptable outcome.

## Numerical anchors (for statement-writing, not for proofs)

- φ orbit: `{(2-φ)/2, (φ-1)/2, 1/2, (3-φ)/2, φ/2}`; adjacent gaps
  `φ-3/2, (2φ-3)... ` — minimum `φ - 3/2 = (√5-2)/2 ≈ 0.1180`.
- Key identity for T6: `φ^5 = 5φ+3`, `φ^6 = 8φ+5`, hence
  `φ^5(φ - 3/2) = (φ+1)/2 = φ²/2 ≈ 1.309 ≥ 1`.
- Bound arithmetic: `W=5`, `⌈W/2⌉=3`, so `N_φ ≤ 9`.

## Deliverables

Census report; Lean sources extending the round-1 project; axiom audit output
for every target; SCRUPLES summary distinguishing proved / reused / reported;
GITHUB_HANDOFF_CHECKLIST as in round 1.
