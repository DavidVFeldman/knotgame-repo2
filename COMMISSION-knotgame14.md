# COMMISSION: knotgame round 14 — the spectral material (T40–T42)

## OPERATING RULES — read first

The tree in this tarball is GREEN under continuous integration. Verifying the
whole tree is NOT your job.

1. FIRST COMMAND: `lake exe cache get`. A progress report of the form
   "8125 of 8145" means you are compiling Mathlib from source and have not
   started on this project.
2. NEVER a bare `lake build`. Build only the modules you author, one at a
   time: `lake build RequestProject.<YourModule>`.
3. NEVER a tree-wide axiom audit. `#print axioms` on YOUR OWN theorems only.
4. If one of your modules takes more than ~10 minutes to elaborate, stop and
   report it; do not retry in a loop.
5. `RequestProject` is built by directory glob — anything you leave in that
   directory is compiled. Do not leave scratch files there.
6. Do not attempt anything listed in `UNBUILT.md`.
7. Deliver source plus documents. Do not build the union, do not push.

Census-first; report rather than repair; no sorry/admit/new axiom/
native_decide; SCRUPLES for every convention or deviation. The textual gate
strips `--` comments, so prose may mention a forbidden token; code may not.

Read `STATE-OF-PLAY.md` before starting.

## T39.5 — bridge the branch-word layers FIRST (census finding, round 14)

A census of the delivered tree found the branch-word layer defined three
times, in modules with disjoint import paths: `bSurvives`/`SW`/`rapp` in the
`Branching`→`ExpCount` chain, `branchSurvivesWord`/`branchWords` in round 13's
`CountingOperator`, and `branchIter` in `Pisot`; `BLegal` and `branchLegal`
are the same definition verbatim. T41 needs the `integral_bcount` side for its
`(λ/2)^m`, and T42 needs `rapp_append` from the other side.

Before T40–T42, write ONE bridging module proving the definitions agree
(`branchLegal_iff_BLegal`, `rapp_eq_branchIter`, and whatever else the two
sides need), and build the rest on it. Do not add a fourth copy. If the
bridge turns out to be more than a short module, report that and stop rather
than working around it.

## T40 — the contraction and the spectral gap (paper `prop:gap`)

Define the normalised counting operator on (0,1),
  (P h)(y) = (1/2)[ h(r y) + h(r y + 1 - r) ],   r = 1/λ, λ ∈ (1,2).
Prove:
(a) `P_one` : P 1 = 1.
(b) `lipschitz_contraction` : PREFER the `LipschitzWith` formulation over the
    derivative bound — if h is `LipschitzWith K` then `P h` is
    `LipschitzWith (r*K)` — as recommended by the round-14 census. The
    derivative identity (Ph)'(y) = (r/2)[h'(ry) + h'(ry+1−r)] is the proof
    idea, not necessarily the statement.
(c) `tendsto_const` : for Lipschitz h, P^m h converges uniformly to a
    constant, with rate r^m. RECOMMENDED ROUTE (census): nested-interval
    oscillation — the image of P^m lies in an interval of length ≤ r^m·K
    shrinking to a point — rather than a Cauchy estimate.
Identifying that constant as ∫h dν_r requires the invariant measure of the
IFS {ry, ry+1−r}. The census confirms ν_r is NOWHERE CONSTRUCTED in this
project (`FourierFloor` says so in its own scruples: the certified statements
there concern the cosine products directly). Therefore: prove (a)–(c), and
state the identification as an explicit hypothesis, exactly as round 13 did
for the trapezoid. Constructing ν_r is deferred to a later round; do not
attempt it here.

## T41 — equidistribution in mean (paper `thm:equimean`)

With S the adjoint composition operator,
  (S h)(x) = h(λx)·[x < r] + h(λx − (λ−1))·[x > g],   g = 1 − r,
prove:
(a) `adjoint` : ∫₀¹ (S h) g dx = ∫₀¹ h (T g) dx, where T = (2/λ)⁻¹P scaled as
    in the paper — i.e. T h(y) = (1/λ)[h(ry) + h(ry+1−r)].
(b) `endpoint_propagator` : ∫ h dμˣ_m = (S^m h)(x), where μˣ_m is the endpoint
    measure of the branch words of length m legal from x. Use the BRANCH
    alphabet via the T39.5 bridge — not the three-move alphabet. (The round-13
    correction to T38 is the precedent: S is the two-branch operator, and the
    move alphabet carries the constant 3/λ, not 2/λ.)
(c) `equidistribution_in_mean` : (λ/2)^m ∫ (S^m h) g dx → (∫h dx)(∫g dν_r),
    for continuous h, g — conditional on T40's identification if that was
    left hypothetical.

## T42 — the backward-closure lemma, and the bridge to unboundedness

The census found this is one cheap step from being load-bearing, and that step
is now commissioned as part of it. In this project `survives L` and
`survives R` are definitionally `branchLegal 1` and `branchLegal 0`, so
`0 ↦ R, 1 ↦ L` realises branch words as M-free move words. Prove:
(c) `denseFrom_half_imp_kindDense` : `DenseFrom lam (1/2) → KindDense lam`,
    and hence, composing with the certified `Density.N_unbounded_of_kindDense`,
    that density of the branch endpoints from 1/2 alone gives N_λ = ∞.
This makes the two-letter analysis of paper §10.2 the whole of the spreading
problem rather than a simplification of it, and the paper now says so.

Also prove, as originally commissioned:

Let D be the set of x whose endpoint sets are dense in (0,1). Prove: if
y = Φ_ε(x) for a branch word ε legal from x, then the endpoints from y at
level m are among those from x at level m + |ε|; hence y ∈ D ⟹ x ∈ D, and
the complement of D is forward invariant. This is short and needs no analysis
— it is the prepending lemma in another guise — but it is the structural
handle the open problem currently rests on, so it is worth having certified.

## Explicitly NOT commissioned

The pointwise upgrade at x = 1/2 (paper Question 50) — it is unproved on
paper, and the Lasota–Yorke route is closed for the reason given there. Do not
attempt it and do not substitute a weakened variant. Also: everything in
UNBUILT.md; two-step exhaustiveness; d_{3/2}(7) = 52 and d_{3/2}(8) ≥ 57.

## Note on where this runs

Round 14 is to be run by a prover with a working Lean toolchain and Mathlib
cache. A session without one should NOT write these modules and report them
done — see working rule 7 and the two files in UNBUILT.md that were reported
complete without ever being elaborated. A session without a toolchain should
deliver census and design decisions only, and say so.

## Deliverables

Census; sources; `#print axioms` for your own theorems; SCRUPLES (in
particular: which formulation of the Lipschitz bound you chose, and whether
the identification of the limit constant is proved or hypothesised); a
round-14 section for GITHUB_HANDOFF_CHECKLIST.
