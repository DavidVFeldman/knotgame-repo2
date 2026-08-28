# COMMISSION: knotgame round 8 — the 3/2 reformulations, periodic yield, kind dimension, window sharpness (T22–T26)

Ground rules unchanged (census-first; report-rather-than-repair; the tree in
this tarball is ground truth; no sorry/admit/new axiom/native_decide; semantic
axiom audit; SCRUPLES docstrings). Paper source enclosed; cite paper labels.

**Census note before starting.** The tree already covers far more than the
paper's appendix credited: `Littlewood.lean` (`littlewood`,
`no_return_to_half`), `Sqrt2.lean` (the binary-square reformulation through
`posAfter_blocks`), and `PlasticConfig.lean` (`N_rho_le_seven`, `d_rho_four`,
`d_rho_seven`, `card_reachable_configs` at 25,525 — the closure round 1
reported infeasible). Audit these first; several targets below may be partly
present.

## T22 — the λ = 3/2 ternary and Mahler reformulations (paper §11)

The one headline reformulation with no file of its own.

**T22a (`prop:ternary`).** At λ = 3/2 the three deleted intervals are exactly
the ternary cells [0,1/3], [1/3,2/3], [2/3,1]. Writing D(x) for the ternary
cell index of x, a move is the choice of a forbidden digit c ∈ {0,1,2}: every
knot with D(x) = c dies; every survivor moves to (3x − [D(x) > c])/2; and when
c = 1 the point 1/2 is adjoined.

**T22b (`prop:base32`).** The itinerary identity Σ_{j≥1} ε_j (2/3)^j = 1 —
a knot's itinerary is a {0,1}-representation of 1 in base 3/2 — together with
D(x_n) = ε_{n+1} + [2x_{n+1} > 1].

**T22c (`prop:mahler`).** With w = 2x ∈ (0,2), p = ⌊w⌋ ∈ {0,1}, y = w − p:
D = ⌊(3/2)w⌋, w' = (3/2)w − ε, y' = {(3/2)y + p/2}, D = p + [y ≥ (2−p)/3],
p' = D − ε. This is the recursion of Mahler's problem; certifying it is
certifying that the identification is exact.

**T22d (`prop:translation`), optional.** The equivalence: N_{3/2} unbounded iff
for every k there are N, a control c ∈ {0,1,2}^N and indices t_1 < … < t_k with
c_{t_i} = 1 such that the k trajectories w_{t_i} = 1,
w_{s+1} = (3/2)w_s − [⌊(3/2)w_s⌋ > c_{s+1}] all stay in (0,2) to time N.
Attempt after T22a–c.

## T23 — periodic kind words yield unboundedness (paper `prop:kindyield`)

If v is a kind word of period p (1/2 survives v^n for every n) with v_p = M,
then N_λ = ∞. Short: the M at the end of each period gives a birth, and
kindness makes every such birth survive to the end of every later period, so
condition (i) of the certified `thm:compactness` holds. This is the live route
to unboundedness that the certified `no_return_to_half` does NOT exclude — the
paper's remark after `cor:noperiodic` says so explicitly, and the docstring
must preserve that distinction.

## T24 — kind-set cylinder counts (paper `prop:kinddim`), split

**T24a (easy, commissioned).** At λ = 3/2, coding L,M,R as ternary digits, the
survival tree of 1/2 has exactly 2^n nodes at depth n: because the three
deleted intervals tile, exactly one digit is fatal at each node — never none,
never two. Induction on n; no Hausdorff dimension needed.

**T24b (easy, commissioned).** At λ = φ, the analogous count satisfies
N_{n+3} = 4 N_n, from the certified five-state orbit: two states have two
children, three have one.

**T24c (harder, optional).** Hausdorff (and box) dimension exactly
log 2 / log 3 at 3/2 and 2 log 2 / (3 log 3) at φ, via Mathlib's `dimH`.
Infeasibility report acceptable; do not claim the dimension from the cylinder
count alone.

## T25 — sharpness of the transversality window

Round 3 certified δ-transversality for the {−1,0,1} class on [1/2, 667/1000]
with δ = 1/1000. Certify that it FAILS not far beyond: exhibit an explicit
finite coefficient vector c ∈ {−1,0,1}^n and a rational x ∈ (667/1000, 67/100]
with |g(x)| ≤ 1/1000 and g'(x) ≥ −1/1000, verified by kernel reduction over
exact rationals, with the infinite tail bounded so the finite witness suffices.
Search programs are untrusted; the kernel re-checks. This makes the certified
window essentially optimal for this class and is the negative control the
paper currently reports only as a beam computation.

## T26 (optional) — the quantitative density criterion (paper `thm:density`)

Round 5 certified the topological form (`infinitelyManyKnots_of_kindDense`).
Strengthen to: under (D_λ) — every interval of length ε contains a kind-word
endpoint at word length ≤ C log(1/ε) — the same conclusion holds with the
explicit bound d_λ(k) ≤ exponential in k, via
|v_{k+1}| ≤ (1 + C log λ)|v_k| + O(log|v_k|).

## Still explicitly NOT commissioned

Exhaustiveness for `prop:twostep`; the exact values d_{3/2}(7) = 52 and
d_{3/2}(8) ≥ 57; the silver-ratio d(k) formula. All are large searches, and
the first was already reported infeasible.

## Deliverables
Census (including the audit of what is already present); sources; per-target
axiom audit; SCRUPLES (especially the T23 distinction from `no_return_to_half`,
and T24's split); GITHUB_HANDOFF_CHECKLIST section.
