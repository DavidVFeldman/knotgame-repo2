# COMMISSION: knotgame round 5 — the backward game, compactness, and the topological density criterion (T14–T21)

Ground rules unchanged (census-first; report-rather-than-repair; the ROUND-4
tree in this tarball is ground truth; no sorry/admit/new axiom/native_decide;
semantic axiom audit; SCRUPLES docstrings). All targets below are proved in
the enclosed paper source (knotgame.tex, Sections 9–11); cite the paper labels
in docstrings.

## T14 — survivor-set structure (paper Lemma `lem:survivorset`)
S(v), the set of x ∈ (0,1) surviving the word v, is a union of at most
1 + #{M's in v} OPEN intervals of total Lebesgue length exactly r^|v|; hence
it contains an open interval of length ≥ r^|v|/(|v|+1). Induct from the right
via the inverse branches; openness because survival is strict inequalities.

## T15 — permanence (paper Lemma `lem:permanent`) — census first
The knots of cv are exactly the knots of v, with identical positions and ages,
plus one new knot of age |v| present iff c = M and 1/2 survives v. Round 1's
suffix decomposition should supply most of this; audit before proving.

## T16 — one annihilation per step (paper Lemma `lem:oneperstep`)
The inverse branches y↦ry and y↦ry+(1−r) are injective with disjoint images
([0,r) and [1−r,1] at L/R; [0,r/2) and (1−r/2,1] at M), so every composite is
injective and at most one point reaches 1/2 at any backward step.

## T17 — the compactness criterion (paper Theorem `thm:compactness`)
Equivalent: (i) some left-infinite run carries infinitely many simultaneous
knots; (ii) some backward play annihilates infinitely many points; (iii) there
are words w_k with k knots whose age vectors are pointwise bounded in k. Any
implies N_λ = ∞. Rendering latitude: (i)/(ii) may be formalised as an infinite
sequence of moves b : ℕ → Move (read as ever-longer suffixes) with an infinite
set of ages a such that 1/2 survives the first a letters read forward and
letter a+1 is M; record the chosen rendering in SCRUPLES and prove (i)⟺(ii) as
the two readings of one definition if that is what they become. The proof of
(iii)⟹(i) is combinatorial: bounded integer sequences admit constant
subsequences; extract agreement on ever-longer suffixes diagonally. No
topology library is required, though one may be used.

## T18 — the topological density criterion (paper Theorem `thm:density0`)
HYPOTHESIS: every nonempty open subinterval of (0,1) contains Φ_u(1/2) for
some kind word u. CONCLUSION: condition (i) of T17 holds; in particular
N_λ = ∞ and N_λ(n) is unbounded. Proof: T14 gives the open target, the
hypothesis gives the kind word, T15 gives the gain with ages fixed, T17 gives
the run. This is a conditional theorem; the hypothesis is certified for no
specific λ, and the docstring must say so.

## T19 — two short consequences
(a) Deficit law (paper Corollary `cor:deficit`): across a move with no death
and no range-extending birth, T = 1 − spread obeys T↦λT (extreme pair
straddles) and T↦λT−(λ−1) (otherwise). Direct from the certified gap_law.
(b) Free births (paper Lemma `lem:free`): an M acts on the configuration
exactly as R iff every knot is < r/2, and exactly as L iff every knot is
> 1−r/2. Case analysis; watch the λ ≥ 3/2 vs λ < 3/2 position of 1−r/2
relative to r, which the paper's proof handles.

## T20 — the candidate-cell identity (paper Remark `rem:candidates`), finite
For the word w = MLMLMMMMMLMRLRMLMLM at λ = 3/2: itinerary cells (entry
intervals realising a fixed branch declaration at each of the 11 M's) are
pairwise disjoint open intervals whose union is S(w); exactly 6 of the 2048
are nonempty; their lengths sum to exactly (2/3)^19 = 524288/1162261467.
General lemma (cells partition S(w)) plus kernel decide on exact rationals for
the instance.

## T21 (optional, split) — the two-step containment (paper Prop `prop:twostep`)
EASY HALF (commissioned): the seven listed record words produce the listed
configurations (run the game, decide on dyadic rationals), and the listed
containments hold (subset checks): k=2⊂3⊂5⊂7 and 4⊂6 for the drawn
representatives. HARD HALF (attempt only if cheap; infeasibility report
welcome): exhaustiveness — that these are ALL configurations attaining k at
depth d(k) — which for k=7 required 2.49 million retained states and is
likely kernel-infeasible. Do NOT label prop:twostep certified unless the hard
half succeeds; the easy half certifies only the drawn instances.

## Still explicitly NOT commissioned
The return-time tail bound, the renewal inequality, and any exponential lower
bound on K_m: not yet proved on paper. No weakened variants.

## Deliverables
Census; sources; per-target axiom audit; SCRUPLES notes (especially the T17
rendering and the T21 scoping); GITHUB_HANDOFF_CHECKLIST round-5 section.
