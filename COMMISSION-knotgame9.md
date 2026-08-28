# COMMISSION: knotgame round 12 — rebuild the union, close the paperwork, box dimension (T33–T35)

Ground rules unchanged. The tarball is the MERGED tree described in
MERGE-NOTES.md: two parallel lineages united by file union. Census-first.

## T33 — rebuild, audit, and document (do this before anything else)
(a) `lake build` the merged tree; repair nothing silently — if the union
breaks, report what and why before touching it. (b) Run the tree-wide
semantic axiom audit over the FULL import closure, and verify the invariant
*file set = import closure of All.lean* (the orphan lesson of the last
round). (c) Write the missing paperwork: the round-11 per-target axiom audit
referenced by README but never written; census/scruples/audit for the
interrupted final session (KindDimLower: `le_dimH_K`, `dimH_K_eq`,
`kindMeasure` and its Frostman estimate — presently certified in file but
undocumented, and ABANDONED.md §1 is stale, still recording the lower bound
as abandoned); and a round-12 section covering the merge itself.

## T34 — box dimension of the kind set at λ = 3/2
Complete the announced extension: define upper and lower box dimension
(Mathlib has none — SCRUPLES must display the definition and argue its
agreement with the standard lim log N(ε)/log(1/ε), including the squeeze
from triadic scales to all scales), then prove both equal log 2 / log 3,
the lower bound via `kindMeasure`'s covering estimate (any cover at scale
3^(−n) needs ≥ 2^n/4 members), the upper via the 2^n cylinders.

## T35 (optional) — golden-floor enclosures at the cubic parameters
Round 9's audit records no numerical enclosures at the plastic, supergolden
and tribonacci floors. Attempt the plastic one by the same tail-plus-Taylor
method; infeasibility report acceptable.

## Still explicitly NOT commissioned
Two-step exhaustiveness; d_{3/2}(7) = 52, d_{3/2}(8) ≥ 57; widening the
above-φ window (the narrow certified window stands; failures there were
search failures, not obstructions, and may be revisited when the checker is
cheaper).

## Deliverables
Census; per-target audits including retroactive round-11; MERGE-NOTES
verification; SCRUPLES (box-dimension definition faithfulness above all);
GITHUB_HANDOFF_CHECKLIST section, self-contained (still no repository).
