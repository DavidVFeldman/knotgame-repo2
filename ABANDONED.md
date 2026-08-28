# ABANDONED — what this development will not deliver

A single place to look for everything that is **not** certified in this tree,
so that no reader has to infer it from the absence of a theorem.  Each entry
says what was wanted, how far it got, why it stops there, and what would be
needed to resume it.  Nothing listed here is claimed anywhere in the Lean
sources; where a weaker statement *is* certified, the entry says exactly which.

The positive record is in `CENSUS-round*.md`, the deviations in
`SCRUPLES-round*.md`, and the axiom reports in `AXIOM-AUDIT-round*.md`.

---

## 1. `prop:kinddim` — the dimension of the kind set: the lower bound and the box dimension

**Wanted.** At `λ = 3/2` the kind set `K_{3/2}` has Hausdorff *and box*
dimension **exactly** `log 2 / log 3`.

**Delivered.** `RequestProject/KindDim.lean`:
`volume_K : volume K = 0` and `dimH_K_le : dimH K ≤ ENNReal.ofReal (log 2 / log 3)`.
Both are consequences of round 8's cylinder count
`KindTree.card_kindWords_three_halves` (exactly `2^n` surviving words of length
`n`) plus a covering argument.

**Abandoned.** The lower bound `log 2 / log 3 ≤ dimH K`, and the box dimension
in either direction.

**Why.** A cylinder *count* bounds a dimension only from above.  The lower
bound needs a mass distribution (Frostman) argument: the natural measure that
gives every level-`n` surviving cylinder mass `2^{-n}`, together with a
Frostman estimate `μ(B(x,ρ)) ≲ ρ^{log 2/log 3}`, which in turn needs control of
how many level-`n` cylinders can meet a single interval of length `3^{-n}` —
i.e. a separation property of the survival tree that the count alone does not
supply and that round 8 did not establish.  The box dimension needs, in
addition, that the covering by surviving cylinders is efficient at *every*
scale, not only at the scales `3^{-n}`.

**To resume.** Establish that distinct level-`n` surviving cylinders are
separated (or bound the multiplicity of overlap), build the Bernoulli-type
measure on `K` as an inverse limit over the tree, and feed it to Mathlib's
Frostman-style lower bounds for `dimH`.  Nothing in the present tree is an
obstruction; the work simply was not done.

**Standing since:** round 8, where the same item (then called T24c) was
recorded as "not attempted and not claimed".

---

## 2. The aspirational certified growth rate `1.29` at `λ = 3/2`

**Wanted.** A kernel certificate giving `K_{3/2}(m) ≥ c^m` with `c ≥ 1.29`.

**Delivered.** A chain of improvements, each fully certified:

| Source | Bound | Rate |
| --- | --- | --- |
| `ExpLower.lean` (round 7) | `2 ^ ⌊m/5⌋` | `1.14870` |
| `ExpSharp.lean` (round 7) | `15 ^ ⌊m/12⌋` | `1.25316` |
| `ExpSharper.lean` (round 10) | `26 ^ ⌊m/14⌋` | `1.26203` |
| `ExpSharpest.lean` (round 11) | `49 ^ ⌊m/16⌋` | `1.27537` |

**Abandoned.** Anything beyond `49^(1/16) = 1.27537…`.

**Why.** The certificate is a tiling of the core interval by cells, each
carrying `k` distinct branch words of length `T`; the number of cells needed
grows like `λ^T`, and so does the kernel's working set.  At `T = 16` the
certificate is already 2 008 cells (≈ 1.57 million reduced letters), the data
has to be split over nine files to elaborate at all, and the check has to be
run in 41 separate kernel reductions.  Rate `1.29` needs `T ≈ 20–22`, roughly
an order of magnitude more data and kernel time than `T = 16`, which is beyond
what this build tolerates.  The search finds `k = 66` at `T = 17`
(rate `1.27948`), so the obstruction is cost, not the method.

**To resume.** Either a cheaper checker (the present one re-derives every
branch word from scratch inside the kernel; a shared-prefix representation
would cut the reduced size substantially), or a different argument that does
not go through a finite cover.

---

## 3. Exact record depths `d_{3/2}(k)` beyond `k = 4`

**Wanted.** The paper's Appendix A table: in particular `d_{3/2}(5) = 19`,
`d_{3/2}(6) = 23`, `d_{3/2}(7) = 52`, and `d_{3/2}(8) ≥ 57`.

**Delivered.**
* Upper bounds from explicit record words for `k = 2,…,7`
  (`RequestProject/TwoStep.lean`), certified in the exact integer model
  `RunRational.lean`.
* Matching *lower* bounds, hence exact values, only for `k ≤ 4`
  (`RequestProject/RecordDepths.lean`): `d_{3/2}(2) = 3`, `d_{3/2}(3) = 5`,
  `d_{3/2}(4) = 9`, by kernel exhaustion of all `3^n` words with `n ≤ 8`.

**Abandoned.** Exact values for `k ≥ 5`, and every other row of the Appendix A
tables.

**Why.** The lower bound for `k = 5` requires exhausting all words of length
18: `3^18 ≈ 4·10^8` words, far outside kernel reduction, and the deduplicated
breadth-first search that would replace the enumeration (over reachable
configurations rather than words) is not kernel-feasible either at that depth.
For `k = 7` the paper's own search runs to depth 52.

**To resume.** A verified breadth-first search over *configurations* in the
exact integer model with a certified deduplication step — essentially the
machinery `PlasticIndex/PlasticCert` provides at the plastic number, where the
orbit is finite.  At `λ = 3/2` the orbit is infinite, so the state space would
have to be bounded by a separate argument first.

---

## 4. The exhaustiveness half of `prop:twostep`

**Wanted.** The paper's observation that the record configurations nest along
the chains `k = 2 ⊂ 3 ⊂ 5 ⊂ 7` and `k = 4 ⊂ 6`, *for every* record, not merely
for the exhibited ones.

**Delivered.** `RequestProject/TwoStep.lean`: the exhibited record words for
`k = 2,…,7`, their configurations, and the containments along both chains,
all certified.

**Abandoned.** Exhaustiveness — that *no other* record word at these `k` breaks
the pattern.

**Why.** It quantifies over all words of the record lengths, so it inherits the
enumeration cost of §3 exactly.  It was excluded by commission at rounds 5, 8
and 10 and is excluded here for the same reason.

---

## 5. The commissioned width of the above-`φ` parameter window

**Wanted (round 10, T32).** A doubling certificate on `[17/10, 7/4]`, giving
`2^⌊m/T⌋ ≤ K λ m` for every `λ` in that window.

**Delivered.** `RequestProject/ExpAbove.lean`: the same conclusion with
`T = 18` on `[3457/2000, 4331/2500] = [1.7285, 1.7324]`, a window that lies
entirely above the golden ratio (`golden_lt_window`) and contains `√3`
(`sqrt_three_mem_window`), so `2^⌊m/18⌋ ≤ K (√3) m`
(`two_pow_le_K_sqrt_three`).

**Abandoned.** The commissioned width.

**Why.** Scanning `[1.728, 1.736]` in slices of `10^{-4}`, the search fails at
`[1.7282,1.7283]`, `[1.7324,1.7325]`, `[1.7325,1.7326]`, `[1.7327,1.7328]` and
`[1.7328,1.7329]`; the maximal contiguous success range containing `√3` is
exactly `[1.7283, 1.7324]`.  Subdividing those failing slices to width
`1.6·10^{-6}` did not clear them.  A window of the commissioned width would
need roughly thirteen times the data (about four hours of kernel time) *and*
would first have to clear those parameters.  The failures are failures of the
search, not certified obstructions — nothing here says the bound is false
there.

---

## 6. Items the paper itself marks computational or open, never commissioned

None of these is attempted, and none is claimed:

* `rem:jsr` (Remark 5) — the joint spectral radius remark.
* Remark 12 — the informal interpretation of `lem:overlap`.
* `prop:periodic` (Proposition 13) — the classification of periodic runs of
  period at most 6; a finite but unformalised search.
* Remark 17 and the itinerary counts `0,2,2,10,10,44,56,180,250`, and the `RM`
  sweep — numerical observations.
* Definition 20 and the clustering data `T(S)`.
* Questions 21–27 — the paper's open questions, including the boundedness of
  `N_{3/2}` itself, which is the central open problem of the subject and is not
  resolved here.
* The remaining Appendix A verification tables (exhaustive depths 42 and 38).

## 7. Statements about `d_λ` as a function

`d_λ(k)` is *defined* (`KnotGame.d`, as `sInf {n | k ≤ N λ n}`) and two
statements about it are certified — round 8's `d_le_pow` (`d_λ(k) ≤ B^k − 1`
under the quantitative density hypothesis) and round 11's `d_ge_two_mul_sub_one`
/ `d_succ_ge_add_two` (the paper's `prop:lowerbound` and `cor:recursive`, under
the attainability hypothesis discussed in `SCRUPLES-round11.md`).  Beyond those,
no value or bound of `d_λ` is certified; in particular the Appendix A tables
(§3) are not.

---

## 8. Hypotheses that are certified for no parameter

Three criteria in the tree are *implications*, whose hypothesis is verified at
no `λ`, and which therefore prove nothing unconditional:

* `Density.KindDense` and `DensityQuant.KindDenseQuant` (rounds 5 and 8) — the
  density and quantitative-density criteria for `N_λ = ∞`;
* `Translation.MahlerCriterion` (round 8) — the knot-free reformulation at
  `λ = 3/2`;
* `Compactness`'s condition (i) and `PeriodicYield.KindWord` (rounds 5 and 8) —
  satisfied by an explicit kind word only when one is exhibited, which is done
  nowhere at `λ = 3/2`.

Establishing any of them at `λ = 3/2` would settle the paper's central
question; that is exactly the open problem of §6 and is not attempted.
