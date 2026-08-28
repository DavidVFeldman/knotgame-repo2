# Work Order 6 — negative report on Proposition 3.4 (the plastic number)

Paper reference: Proposition 9 of the compiled PDF, `\label{prop:plastic}`
(the commission's "Proposition 3.4").

> For `λ = ρ` the orbit `Orb(ρ)` has 153 points, there are 25 525 reachable
> configurations, and `sup_n N_ρ(n) = 7`. The least lengths attaining `k` knots
> for `k ≤ 6` are 1, 3, 5, 7, 12, 17.

**This proposition is not certified.** Per the commission ("Attempt it; if the
check does not close, report the cost measurements and stop"), this is the
report. No weaker statement is offered in its place.

## What *is* certified

`RequestProject/Plastic.lean`, sorry-free and inside the axiom audit:

| Identifier | Statement |
|---|---|
| `KnotGame.Plastic.cubic`, `cubic_monic` | `X³ - X - 1` over `ℤ`, monic |
| `KnotGame.Plastic.rho`, `rho_cubic`, `rho_mem` | the plastic number as the real root of `x³ = x + 1` in `(1,2)`, obtained from the intermediate value theorem |
| `KnotGame.Plastic.rho_gt`, `rho_lt` | `1.32 < ρ < 1.33` |
| `KnotGame.Plastic.cubic_factor` | the factorisation of the cubic over `ℂ` used to bound the two complex roots |
| `KnotGame.Plastic.isPisot_rho` | **the plastic number is a Pisot number** |
| `KnotGame.Plastic.orb_rho_finite` | **`Orb ρ` is finite**, by Theorem 6 (`KnotGame.orb_finite`) |

So the *hypothesis* of Proposition 9 — that the orbit is a finite set on which a
finite automaton lives — is certified. What is not certified is any of the three
numerical assertions (153, 25 525, `sup N = 7`), nor the table of least lengths
(which is in any case out of scope as a `d(k)` table).

## Why it does not close

The intended route (as for the golden ratio in `RequestProject/Golden.lean`) is
an inductive invariant: exhibit the set of reachable configurations as data,
prove by kernel computation that it contains `∅`, is closed under the three
moves, and that every member has at most seven elements; then exhibit a run
attaining seven.

At `λ = φ` this is 12 configurations over a 5-point orbit and `decide` closes it
instantly. At `λ = ρ` the same shape of check is 25 525 configurations over a
153-point orbit, i.e. **76 575 membership tests in a 25 525-element table**,
each test itself a search. Constraint 1 forbids `native_decide`, so the whole
computation must be replayed by the kernel on unary-flavoured `Finset`/`List`
data with `Decidable` instances unfolded to normal form.

Before that, one would also need the 153 orbit points *symbolically* — each is a
`ℤ[ρ]`-combination, and every transition of the automaton needs a `ring`-style
identity modulo `ρ³ = ρ + 1`, i.e. roughly `3 × 153 = 459` survival decisions
and as many transition identities, each with an inequality against `r/2` or
`1 - r/2` that must be decided by `nlinarith`-grade reasoning on cubic
irrationals. That part alone is a larger artefact than the rest of this
development.

## Cost measurements

`experiments/PlasticCost.lean` (deliberately outside the library glob, so
`lake build` never runs it) is a *proxy* for the closure check: an orbit modelled
by `Fin k`, configurations modelled by the `k(k-1)/2` unordered pairs of distinct
points, three affine moves `x ↦ (2x+m) mod k`, and the closure test
"every image of every configuration under every move is again a configuration",
discharged by `decide`. The data structures and the membership search are of the
same kind as the real check; the arithmetic is strictly cheaper.

Measured with `lake env lean experiments/PlasticCost.lean`, `maxHeartbeats 0`,
wall clock, on the machine used for this development. The `import Mathlib`
baseline is about 9 s and is included in the "wall clock" column.

| `k` | configurations | wall clock | net of baseline |
|-----|----------------|------------|-----------------|
|   5 |     10         |     10 s   |   ~1 s          |
|  10 |     45         |     12 s   |   ~3 s          |
|  20 |    190         |     27 s   |  ~18 s          |
|  40 |    780         |    335 s   | ~326 s          |
|  60 |   1 770        |  > 1 200 s | timed out       |

A second experiment isolates an independent obstruction. Phrasing the state
space with `Finset (Fin k)` and the derived `DecidableEq`/`Fintype` instances
rather than with lists, and asking only that the *`k + 1` configurations* `∅`
and the singletons be closed under a single move — a far smaller problem than
the one above — `decide` succeeds at `k = 5` (10 s) and `k = 10` (32 s) and then
**aborts the process with a stack overflow at `k = 20`**, after 43 s. The
blocking resource there is not reduction steps but the size of the *terms* the
elaborator and kernel must build while unfolding the instances: the failure is
not one a longer timeout would fix. Proposition 9's orbit is `Fin 153`.

Fitting the three completed data points, the cost grows between quadratically
and cubically in the number of configurations (`190 → 780` configurations, a
factor 4.1, costs a factor ≈ 18, i.e. exponent ≈ 2.0; the `45 → 190` step gives
exponent ≈ 1.25 but is baseline-dominated; the timed-out `k = 60` point is
consistent with an exponent nearer 3).

Proposition 9 needs 25 525 configurations: **33× the largest instance that
completed**, and over a 153-point orbit rather than a 40-point one. Even the
optimistic quadratic extrapolation from the `k = 40` point gives
`326 s × 33² ≈ 3.5 × 10⁵ s ≈ 4 days` of single-threaded kernel reduction for the
*proxy*; a cubic fit gives `≈ 1.2 × 10⁷ s ≈ 4 months`. The real check carries in
addition the symbolic arithmetic in `ℤ[ρ]`, which the proxy omits entirely, and
the term-size problem above, which is what actually killed the first attempt.

## Conclusion

Under constraint 1 (no `native_decide`) Proposition 9 is not reachable by the
`decide`-based route, and no route that avoids a large finite computation is
visible: the numbers 153, 25 525 and 7 are assertions about a specific finite
automaton and carry no structure that a general argument could exploit. Work on
this item is stopped, as instructed.

Two things would make it feasible and neither is available here: permission to
use `native_decide` (which would move the computation to compiled code at the
cost of trusting the compiler), or a reflective decision procedure with a
verified efficient data structure (a bitmask representation with `UInt64` words
and a `csimp`-backed implementation, plus a kernel-friendly `Nat`-binary
encoding of the orbit indices). Either is a project in its own right, well
outside this commission.

---

# Round-2 addendum — the 153-point orbit *is* feasible

The report above concerns the **25 525 reachable configurations** and is
unchanged: `sup N ρ = 7` is still not certified, and the route to it is still
out of reach for the kernel.

Round 2 needs a strictly smaller object. The scheduling bound
(`KnotGame.N_le_of_separated`) turns "the orbit of `1/2` is finite with smallest
gap `δ`" into `N ≤ W + ⌈W/2⌉ + 1` whenever `ρ^W δ ≥ 1`. That needs the
**153-point orbit** and one gap — not the configurations, not the automaton, not
the reachability analysis. This is a set of size 153, against 25 525; and the
check on it is linear in the size, not quadratic.

That check does close, in `RequestProject/PlasticOrbit.lean`:

| Check | Content | Cost |
|---|---|---|
| `chk_range` | each of the 153 listed points lies in `(0,1)` | 153 integer comparisons |
| `chk_closed` | each of the 306 branch images is again listed, or provably outside `(0,1)` | 306 list lookups + comparisons |
| `chk_chain` | the list is increasing with consecutive gaps `≥ 239/100000` | 152 integer comparisons |

The whole file elaborates and kernel-checks in about 30 seconds, with `decide`
only — no `native_decide`, no new axioms.

## Why this one is cheap when the other is not

Three things, all absent from the configuration computation:

1. **Exact integral coordinates.** `ρ³ = ρ + 1` makes multiplication by `ρ` an
   integral operation on coordinates: `ρ·(a + bρ + cρ²) = c + (a+c)ρ + bρ²`.
   Every orbit point of `1/2` is `(a + bρ + cρ²)/2` with `|a|,|b|,|c| ≤ 8`, so
   the branch maps are two additions on a triple of small integers. The
   round-1 experiments carried real-number arithmetic through `Finset ℝ`
   operations, where each step grows the term.
2. **Integer-only comparisons.** Sign decisions go through the certified
   rational enclosure `1324717957/10⁹ ≤ ρ ≤ 1324717958/10⁹`, scaled by `10¹⁸`
   so that a comparison is one integer inequality with a rigorous error term
   (`Mn`/`En` in the source). The kernel's arithmetic on machine-sized integers
   is fast; no real-number normalisation ever happens.
3. **Linear, not quadratic.** The separation of *all* `153 · 152 / 2` pairs is
   obtained from the `152` consecutive gaps of a sorted list, via
   `List.IsChain → List.Pairwise`. The configuration closure has no comparable
   collapse: it genuinely visits 25 525 objects and their three images each.

## What this changes and what it does not

* **Certified now:** every knot of every reachable configuration at `λ = ρ`
  lies on the explicit 153-point list (`Plastic.run_subset_OrbSet`); distinct
  coexisting knots are at distance at least `239/100000` (`Plastic.run_sep`);
  and `N ρ n ≤ 34` for every `n` (`Plastic.N_rho_le_34`).
* **Still not certified:** `sup N ρ = 7`, the count `25 525`, and the least
  lengths `1, 3, 5, 7, 12, 17`. The paper's `153` is now certified as an upper
  bound in the sense that matters here — every reachable knot position is on the
  list — but the list is not proved *minimal*, i.e. it is not proved that all
  153 points are actually attained. Nothing in the scheduling argument needs
  that, so it was not attempted.
* **The gap.** `239/100000` is a certified lower bound for the smallest gap,
  not the smallest gap itself. The true value is about `0.0023912`; the paper's
  `≈ 0.00239` agrees. As with `153`, the exact minimum is not needed and is not
  claimed.

---

# Round-6 addendum — the proposition is now certified

**The negative report above is superseded.** All four clauses of Proposition 9
— the 153 orbit points, the 25 525 reachable configurations, `sup N ρ = 7` and
the least lengths `1, 3, 5, 7, 12, 17` — are certified, sorry-free, with kernel
`decide` only. The details are in [`PROP9-PLASTIC.md`](PROP9-PLASTIC.md); the
Lean is in `RequestProject/PlasticIndex.lean`, `PlasticTbl.lean`,
`PlasticCert.lean`, `PlasticConfig.lean` and `PlasticOrbitCount.lean`.

The two paragraphs above headed "Why it does not close" and "Cost measurements"
remain accurate about the route they measured: replaying the breadth-first
search inside the kernel over `Finset (Fin 153)` data. What made the difference
was not a longer timeout but three changes of representation:

1. **The search is not replayed.** Its result — all 25 525 configurations, each
   with a depth tag and a recorded parent — is shipped as data, and the kernel
   checks closure, size, reachability and shape. Checking is linear in the data;
   searching was not.
2. **Byte-packed transition tables.** The 153-point orbit and its three moves
   are compiled to three natural numbers, one byte per index, so a transition is
   a shift and a remainder on machine-friendly integers rather than a search
   through a `Finset` with unfolded `Decidable` instances. The tables themselves
   are checked against the certified `ℤ[ρ]` arithmetic of round 2.
3. **No long lists in the kernel.** Every traversal recurses on a balanced tree
   of depth 15. The first attempt at this route folded over a
   25 525-element list and crashed the kernel; that is the same term-size
   obstruction the round-1 experiments hit, and it is avoided rather than
   out-waited.

The whole check now costs about 11 minutes of kernel time in a single file, and
about 4 minutes of elaboration for the 1.4 MB of certificate data.
