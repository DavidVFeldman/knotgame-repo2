# COMMISSION: knotgame round 4 — branching below the golden ratio (T11–T13)

Ground rules unchanged (census-first; report-rather-than-repair; the ROUND-3
tree in this tarball is ground truth; no sorry/admit/new axiom/native_decide;
semantic axiom audit; SCRUPLES docstrings). Reuse the existing branch maps and
survival predicates; do not re-derive.

Setting: λ ∈ (1,2), g = 1−1/λ, r = 1/λ. Branch 0 is x ↦ λx, legal iff x < r;
branch 1 is x ↦ λx−(λ−1), legal iff x > g. The *window* is (g, r): both
branches legal there, exactly one elsewhere ("forced").

## T11 — the two branching lemmas (proved in the enclosed note, §6)

**T11a (no jumping).** For λ² < λ+1 (i.e. λ < φ): if x ≤ g then λx < r, and
if x ≥ r then λx−(λ−1) > g. So a forced step from outside the window either
stays on its own side or lands inside; it never crosses. Pure algebra:
each crossing inequality is equivalent to λ² ≥ λ+1.

**T11b (sharpness).** For λ² ≥ λ+1: the pair {1/(λ+1), λ/(λ+1)} is a
2-cycle of the forced dynamics with both points outside the window
(1/(λ+1) ≤ g and λ/(λ+1) ≥ r). Universally quantified algebra over
λ ∈ [φ, 2); no search.

**T11c (good child).** Fix rationals λ₀ < λ₁ with 1 < λ₀, λ₁² < λ₁+1, and
η = min(λ₀−1, (2−λ₁)/2). For λ ∈ [λ₀,λ₁] and x ∈ (g,r): if x ≤ (g+r)/2 then
λx ∈ (λ−1, λ/2]; else λx−(λ−1) ∈ [(2−λ)/2, 2−λ) and 2−λ < r. In both cases
the selected child has distance ≥ η from {0,1}.

**T11d (bounded return).** Same window. If x ∈ [η, g] then some forced
iterate λᵏx with k ≤ B lies in (g,r), all earlier iterates staying in (0,g];
symmetrically from [r, 1−η] under branch 1. Here B is any natural with
λ₀^(B−1)·η > g(λ₁); the anchor window [1000/667, 8/5] gives η = 1/5,
g(λ₁) = 3/8, B = 3. (Proof: the distance to the relevant endpoint multiplies
by λ each forced step, and T11a forbids crossing.)

## T12 — consequences

**T12a (continuum).** For λ ∈ [λ₀,λ₁] as above, an explicit injection from
(ℕ → Bool) into infinite kind sequences from any window point: at each
window visit follow the chosen bit's child, then the forced steps of T11d.
Deliverable: `Function.Injective` into the set of survival itineraries of 1/2
(note 1/2 ∈ (g,r) for every λ < 2).

**T12b (linear count).** K_m := the number of length-m branch words along
which 1/2 survives satisfies K_m ≥ m/(B+1) (natural division is fine).

## T13 — the common window (packaging)

One theorem stating that on λ ∈ [1000/667, 8/5]: (a) the transversality
statement of round 3 applies (1/λ ∈ [5/8, 667/1000] ⊆ [1/2, 667/1000]);
(b) λ² < λ+1, so T11 applies; (c) 3/2 lies in the window. Just inequalities
on rationals plus instantiation — the point is a single citable identifier
asserting that every certified tool coexists on a window containing 3/2.

## Explicitly NOT commissioned

The geometric tail bound P(S > t) ≤ Cλ₀^(−t) for the discarded child, the
renewal inequality, and the integrated exponential lower bound. These are not
yet proved on paper (the note marks them open); by our own standard they are
not ready to be formalised. Do not attempt them, and do not substitute
weakened variants.

## Deliverables

Census; Lean sources; per-target axiom audit; SCRUPLES notes (in particular:
exact open/closed conventions at g, r, and the treatment of the boundary
x = (g+r)/2 in T11c); GITHUB_HANDOFF_CHECKLIST round-4 section.
