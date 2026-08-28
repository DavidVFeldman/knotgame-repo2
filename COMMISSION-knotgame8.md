# COMMISSION: knotgame round 10 — no-recurrence, and pushing the certificates (T30–T32)

Ground rules unchanged (census-first; report-rather-than-repair; no
sorry/admit/new axiom/native_decide; semantic axiom audit; SCRUPLES
docstrings). Paper source enclosed; cite paper labels.

## PARALLEL-RUN CLAUSE — read first

This round runs IN PARALLEL with round 9 (COMMISSION-knotgame7.md), both
branching from the ROUND-8 tree shipped here as ground truth. Round 9's
targets (immortal births, record min-gaps, the Fourier floor at φ) are
disjoint from this round's. To keep the eventual merge a pure file union:
- put ALL new material in NEW files under fresh names; never edit an
  inherited file except to add imports to `RequestProject/All.lean`;
- do not touch `Translation.lean`, `PeriodicYield.lean`, `TwoStep.lean`, or
  add any file whose name begins `Fourier`/`Floor` (reserved for round 9);
- census-first as usual, but treat round 9's targets as out of scope even if
  you notice them missing.

## T30 — no position recurs at λ = 3/2 (paper `prop:norecur`)

At λ = 3/2 no knot ever occupies the same position twice. Paper proof
(§12, one paragraph): positions are dyadic (round 8's `Dyadic` invariant in
`Ternary.lean` — reuse it); a recurrence after B moves makes the position a
fixed point of the affine composite x ↦ λ^B x − c with
c = (λ−1) Σ_{j∈S} λ^{B−j}; clearing denominators the fixed point is
N(S)/(3^B − 2^B) with N(S) = Σ_{j∈S} 3^{B−j} 2^{j−1}; the telescoping
identity Σ_{j=1}^B 3^{B−j} 2^{j−1} = 3^B − 2^B and the oddness of 3^B − 2^B
leave only the fixed points 0 and 1, which no knot occupies. Include the
corollary that no block of moves acts as the identity on any knot
(`no_identity_block`), which the paper cites against a candidate mechanism
for `prop:twostep`.

## T31 — a sharper exponential certificate at λ = 3/2

Round 7 certified K_{3/2}(m) ≥ 15^{⌊m/12⌋} (rate ≈ 1.2532; measured ≈ 4/3).
Produce a certified improvement using the existing `MDoubling` machinery: any
k, T with k^{1/T} > 15^{1/12} accepted; aim for rate ≥ 1.29 if the kernel
tolerates it. New data/soundness files only (e.g. `ExpSharper*.lean`). Report
the practical ceiling you hit — group the kernel checks as round 7 did — and
if no improvement is kernel-feasible, say so with the sizes attempted.

## T32 — exponential kind counts ABOVE the golden ratio

The covering argument nowhere needs λ < φ. Produce a doubling (or
multiplicity) certificate on a rational window above φ containing √3 —
suggested [17/10, 7/4] — giving 2^{⌊m/T⌋} ≤ K λ m there (any certified T).
This is new territory: the branching lemmas fail above φ (the certified
two-cycle avoids the window), so returns near that cycle may be slow and the
certificate may need longer words or a smaller core. If no certificate is
found at reasonable size, deliver an infeasibility report with the parameters
tried — that itself is informative about the two-cycle's shadow. Do NOT
weaken to a sub-window excluding √3 without saying so prominently.

## Still explicitly NOT commissioned

Exhaustiveness for `prop:twostep`; d_{3/2}(7) = 52 and d_{3/2}(8) ≥ 57; the
Hausdorff/box dimensions of `prop:kinddim`; and everything reserved to
round 9 above.

## Deliverables

Census; sources; per-target axiom audit; SCRUPLES (especially: T30's reuse of
the round-8 dyadic invariant rather than a re-derivation; T31/T32 certificate
sizes and kernel costs; the parallel-run file discipline observed);
GITHUB_HANDOFF_CHECKLIST round-10 section, self-contained as before since no
repository exists yet.
