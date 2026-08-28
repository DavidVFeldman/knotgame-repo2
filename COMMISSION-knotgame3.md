# COMMISSION: knotgame round 3 — tribonacci/supergolden (T8) and the transversality inequality (T9)

Ground rules unchanged (census-first; report-rather-than-repair; tarball —
the ROUND-2 tree — is ground truth; no sorry/admit/new axiom/native_decide;
semantic axiom audit; SCRUPLES docstrings).

## T8 (carried over from the round-2 addendum, not attempted in round 2)

Exact session computations in Z[λ] give: **tribonacci** (x³=x²+x+1,
λ≈1.83929): orbit of 1/2 has 7 points, 20 reachable configurations, maximum
exactly 3, d(k)=1,3,7. **Supergolden** (x³=x²+1, λ≈1.46557): orbit 43 points,
412 configurations, maximum exactly 4, d(k)=1,3,5,11. Certify in the round-1
φ style (orbit closure, transition tables, configuration reachability, exact
max), tribonacci first; integer coordinate triples over Z[λ] with λ bracketed
by rationals, as in round 2's PlasticOrbit. Enclosed: `pisot2.py` (the session
computation). Supergolden infeasibility report acceptable; tribonacci at 20
configurations should not need one.

## T9 (new): δ-transversality for the {−1,0,1} class through x = 2/3

**Statement to certify.** Let 𝓑₀₁ = { g(x) = 1 + Σ_{i≥1} c_i x^i : c_i ∈
{−1,0,1} } (all finite and infinite coefficient sequences). Then for all
g ∈ 𝓑₀₁ and all x ∈ [1/2, 667/1000]:

    |g(x)| ≤ 1/1000   ⟹   g′(x) < −1/1000.

**Why it matters** (context, not part of the target): this extends the
pair-counting estimates of the transversality note to a parameter window
containing λ = 3/2, which the classical box-class window (ceiling
x* = 0.649138) provably cannot reach. The degree-one case at x = 2/3 is the
round-1 {0,±1} lemma; this is its uniform two-dimensional strengthening.

**Reduction to a finite check** (prove as a lemma). For x ≤ 667/1000 and
truncation depth D = 48, the tail beyond D satisfies
|Σ_{i>D} c_i x^i| ≤ x^{D+1}/(1−x) and |Σ_{i>D} i c_i x^{i−1}| ≤
((D+1)x^D(1−x)+x^{D+1})/(1−x)². So it suffices to show: no prefix
(c_1,…,c_D) and x in the window admit |g_D(x)| ≤ 1/1000 + T1 and
g_D′(x) ≥ −1/1000 − T2, with T1, T2 the (rational upper bounds for the) tail
bounds at the right-hand endpoint of the x-cell.

**Certificate architecture.** Branch-and-bound over (x-cells) × (coefficient
prefixes) with centered-form enclosures: track the prefix polynomial and its
derivative exactly at the rational cell midpoint; bound their variation over
the cell by (w/2)·Σ_{j<i} j x_b^{j−1} and (w/2)·Σ_{j<i} j(j−1) x_b^{j−2}
(sign-independent, precomputable as rationals). Prune a node when either
(a) |g at midpoint| exceeds 1/1000 + variation + tail, or (b) the derivative
midpoint plus variation plus tail is below −1/1000. A session prototype
(`bnb2.py`, enclosed) closes the whole window with **25 cells and 18,622
nodes, zero leaks** — the cell decomposition is enclosed as
`certificate-cells.json` and is deterministic from the generator. All
arithmetic is rational once cell endpoints are rational and the floating
pads are replaced by exact bounds; the expected Lean form is a verified
checker function over the (regenerated or enclosed) tree, discharged by
kernel `decide`, in the spirit of round 2's PlasticOrbit but with rational
rather than integer arithmetic.

**Validation context** (session, float prototype): the search *refuses* to
certify on [0.669, 0.6695] at the same δ (a genuine double zero of the class
lies near 0.669), and *leaks* 321,056 states on [0.666, 0.667] at δ = 1/500 —
so the method detects failure where failure exists, and the margin at
δ = 1/1000 is real, not an artifact of pruning. These negative controls need
not be formalized; they are why we believe the statement.

**Scruples.** If the rational-arithmetic version of any pad or tail bound
fails to close a cell, subdivide (the generator shows how); if the kernel
cannot digest the certificate at this size, report per protocol with timing
data — do not reach for compiled evaluation.

## Optional T10

The pair-counting proposition of the transversality note, on the window
certified by T9, with Mathlib's Lebesgue measure. Only after T8–T9.
