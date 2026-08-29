# SCRUPLES — round 13

Every place where a round-13 Lean statement is not a literal transcription of
the paper or of the commission, and every convention that had to be fixed.
Conventions inherited from earlier rounds (the window open at both ends,
survival by strict inequalities, `g + r = 1`, `K λ m` for the number of
surviving words of length `m`, itineraries indexed from `0`, the kind set `K`
and the cylinder apparatus of `KindDim.lean`) are unchanged and are not
repeated.  Each item also appears in the docstring of the file it belongs to.

---

## 1. T36 — covering numbers and box dimension (`KindBox.lean`)

The commission asks, explicitly, that the scruples *display* the definitions
and argue that they are the right ones.  Here they are, verbatim from the
source.

### 1.1 The covering number

```lean
/-- The sizes of finite covers of `s` by sets of diameter at most `r`. -/
def coverSizes (s : Set ℝ) (r : ℝ) : Set ℕ :=
  {N | ∃ f : Fin N → Set ℝ, (∀ i, Metric.ediam (f i) ≤ ENNReal.ofReal r) ∧ s ⊆ ⋃ i, f i}

/-- The covering number `N(s, r)`. -/
noncomputable def coverNum (s : Set ℝ) (r : ℝ) : ℕ := sInf (coverSizes s r)
```

Four things to notice, each a deliberate choice.

* **Covers by arbitrary sets of small diameter**, not by intervals, not by
  balls, not by grid boxes.  For subsets of `ℝ` all four conventions give the
  same box dimension: a set of diameter `≤ r` is contained in a closed
  interval of length `r`, and an interval of length `r` has diameter `r`, so
  the three counts differ by a factor of at most `2` — and a bounded factor
  changes nothing after dividing by `log(1/r)`.  The diameter convention was
  chosen because it is the one both halves of the proof want: the upper bound
  produces cylinders (which are intervals) and the lower bound consumes
  arbitrary sets (which is what a Frostman estimate applies to).
* **`sInf` over a set of naturals**, so `coverNum s r = 0` when no finite
  cover of diameter `≤ r` exists.  That degenerate value is harmless here
  because `coverSizes_K_triadic` exhibits a finite cover at every triadic
  scale, and `coverNum_mono` transports it to every scale; the bracketing
  lemmas only ever use `coverNum` at scales where a cover is known to exist.
* **`Metric.ediam ≤ ENNReal.ofReal r`**, i.e. the diameter bound is
  non-strict, and for `r < 0` the condition is unsatisfiable (`ofReal r = 0`
  forces singletons or the empty set); no statement in the file uses a
  negative scale.
* **`Fin N`-indexed families**, i.e. covers of *cardinality* `N`, with
  `coverSizes_upward` supplying monotonicity in `N` so that `sInf` behaves as
  the least cardinality.

### 1.2 The box dimensions

```lean
noncomputable def upperBoxDim (s : Set ℝ) : ℝ :=
  limsup (fun r : ℝ => Real.log (coverNum s r) / Real.log (1/r)) (𝓝[>] (0:ℝ))

noncomputable def lowerBoxDim (s : Set ℝ) : ℝ :=
  liminf (fun r : ℝ => Real.log (coverNum s r) / Real.log (1/r)) (𝓝[>] (0:ℝ))
```

This is the textbook definition, letter for letter:
`dim_B s = lim_{ε → 0⁺} log N(s,ε) / log(1/ε)`, split into its `limsup` and
`liminf` halves.  Two points of faithfulness deserve to be stated.

* **The limit is over all real scales, not over a sequence.**  The filter is
  `𝓝[>] (0:ℝ)` — the punctured right neighbourhood filter of `0` — so
  `upperBoxDim` and `lowerBoxDim` quantify over *every* scale `r > 0`
  approaching `0`.  This matters: the cheap thing to prove is the statement
  along the geometric scales `r = 3^{-n}`, and a "box dimension" defined only
  along a geometric sequence would be a weaker statement than the standard
  one.  It is a standard fact that the two agree for a geometric sequence of
  scales, but that fact is exactly what needs proving, and it is proved here
  rather than assumed — see the next point.
* **The squeeze from triadic scales to all scales is `tendsto_boxQuot`, and
  it is proved.**  For `0 < r ≤ 1/3` let `k = bidx r` be the bracketing index,
  characterised by `3^{-(k+1)} < r ≤ 3^{-k}`; then monotonicity of the
  covering number in the scale gives

  `N(K, 3^{-k}) ≤ N(K, r) ≤ N(K, 3^{-(k+1)})`,

  and with the two triadic estimates `N(K,3^{-n}) ≤ 2^n` and
  `2^n ≤ 4·N(K,3^{-n})` and the bracket `k log 3 ≤ log(1/r) ≤ (k+1) log 3`
  one gets

  `loSeq k ≤ log N(K,r) / log(1/r) ≤ hiSeq k`,
  `loSeq k = (k−2) log 2 / ((k+1) log 3)`, `hiSeq k = (k+1) log 2 / (k log 3)`.

  Both comparison sequences tend to `log 2 / log 3` as `k → ∞`
  (`tendsto_hiSeq`, `tendsto_loSeq`), and `bidx r → ∞` as `r → 0⁺`
  (`tendsto_bidx`), so the quotient converges to `log 2 / log 3` **along the
  full filter `𝓝[>] 0`**.  `upperBoxDim_K` and `lowerBoxDim_K` are then
  `Tendsto.limsup_eq` and `Tendsto.liminf_eq` of that one limit — which is
  also why the two box dimensions are equal rather than merely both computed:
  the underlying function has a genuine limit.
* **The constant `4`** in `le_coverNum_K` is the Frostman constant of round 12
  (`KindLower.kindMeasure_le_of_ediam`): each member of a cover of diameter
  `≤ 3^{-n}` carries `kindMeasure`-mass at most `4·2^{-n}`, and the cover
  carries the total mass `1`.  Any bounded constant would do; it disappears in
  the `loSeq` numerator `(k−2)` and in the limit.
* **`bidx` is defined as `sInf {n | 3^{-n} < r} - 1`.**  Truncated natural
  subtraction is safe: `sInf_pos_of_le_third` shows the `sInf` is positive
  whenever `0 < r ≤ 1/3`, which is the only regime in which `bidx` is used.
  (The old, unbuildable file used a non-strict inequality here and appealed to
  a lemma that does not exist; this is one of the three faults repaired.)
* **What is *not* claimed.**  No general theory: no monotonicity of
  `upperBoxDim` under inclusion, no product or Lipschitz laws, no comparison
  with `dimH` in general.  The only comparison made is the numerical one at
  `K_{3/2}`, where the box dimensions coincide with round 12's Hausdorff
  dimension.

### 1.3 The repair itself

The old file never elaborated.  Three independent faults: it opened a
namespace `KindDimLower` that does not exist (the namespace of
`KindDimLower.lean` is `KnotGame.KindLower`), which made the whole `open` line
fail and every name it should have introduced unknown; the bracketing index
rested on a nonexistent lemma; and `tendsto_boxQuot`, the mathematical heart,
was left unproved.  The present file is a restatement against what the current
neighbours actually export, and the squeeze is proved.  Nothing was copied
from the old file on trust.

---

## 2. T38 — the counting operator (`CountingOperator.lean`)

* **The commission's identity `∫₀¹ K_λ(m,x) dx = (2/λ)^m` is false for the
  project's existing kind words, and is not asserted anywhere.**  The
  commission asks both for that constant and for the existing survival
  predicates to be reused; those requirements are incompatible.  The existing
  `KindTree.kindWords` counts words in the three-letter **move** alphabet, and
  each of `L`, `R`, `M` is a bijection from its legal domain onto `(0,1)`
  (`L` from `(g,1)`, `R` from `(0,r)`, `M` from `(0,r/2) ∪ (1−r/2,1)` in two
  pieces onto `(0,1/2)` and `(1/2,1)`), so the mean factor per step is `3/λ`.
  `integral_kcount` therefore proves `(3/λ)^m`.
* **The `(2/λ)^m` identity is proved in the reading that matches the operator
  `T`**: `integral_bcount` is over the two-branch count `bcount`, and
  `bcount_eq_card` proves that `bcount λ x m` really is the cardinality of the
  set of legal branch words of length `m` from `x`.  The move alphabet
  double-counts relative to the branch alphabet: for `x < r/2` the moves `R`
  and `M` send the knot to the same place, and for `x > 1−r/2` so do `L` and
  `M`.
* **The independent check on the constant.**  At `λ = 3/2` the move count is
  exactly `2^m` at *every* point of the survival tree of `1/2`
  (`KindTree.card_kindWords_three_halves`), and `3/λ = 2` reproduces it
  (`integral_kcount_three_halves`); `(2/λ)^m = (4/3)^m` would make the mean
  smaller than a pointwise-attained value, which is impossible.
* **`T_one` keeps the hypothesis `λ < 2`** because the commission asks for
  `λ ∈ (1,2)`, even though the identity as stated needs only `λ ≠ 0`; the
  file says so, and the unused-hypothesis warning that this produces is left
  standing rather than hidden.
* **The integrals are Bochner integrals over the open interval `(0,1)`**; the
  endpoints are Lebesgue-null, so this is the same as over `[0,1]`.
* **`bcount` and `kcount` are real-valued** (`ℝ`, not `ℕ`), because they are
  integrated; `bcount_eq_card` and the definition of `kcount` tie them to the
  underlying cardinalities.

---

## 3. T39 — the trapezoid at `λ = √2` (`Trapezoid.lean`)

* **What the paper's `prop:trapezoid` asserts** is the density of the backward
  measure at `λ = √2`: piecewise linear, rising on `[0, √2−1]`, constant at
  `(2+√2)/2` on `[√2−1, 2−√2]`, falling on `[2−√2, 1]`.  `trapDens` is exactly
  that function, written with `if`s, the breakpoints assigned to the lower
  piece (immaterial: they are null).
* **The backward series.**  By round 8's `Ternary.itinerary_tsum` a knot whose
  orbit along the itinerary `ε` stays in `[0,1]` equals
  `(1−r) ∑_j ε_j r^j`; `bval` is that series at `λ = √2`.  The splitting
  `bval_split : bval ε = evenPart ε + oddPart ε` uses only `r² = 1/2`, and
  `evenPart_mem_Icc`, `oddPart_mem_Icc` give the exact ranges `[0, 2−√2]` and
  `[0, √2−1]`, whose lengths sum to `1`.
* **The convolution is proved in general, then specialised.**
  `unifSum_eq_withDensity` says that for *arbitrary* `a, b` the pushforward of
  `(Lebesgue on (0,a)) × (Lebesgue on (0,b))` under `(u,v) ↦ u+v` has density
  `convDens a b x = max 0 (min a x − max 0 (x−b))` — the length of
  `(0,a) ∩ (x−b, x)`.  The proof is Tonelli plus translation invariance; no
  hypothesis on `a, b` is needed.  `convDens_sqrt_two` then computes, at
  `a = 2−√2`, `b = √2−1`, that `convDens a b = (3√2−4)·trapDens` with
  `3√2−4 = a·b`, and `trapezoid_law` divides by the normalisation to get the
  probability measure with density `trapDens`.
  `isProbabilityMeasure_trapDens` records that this density integrates to `1`
  — an independent check on the plateau height `(2+√2)/2 = 1/(2−√2)`.
* **The gap, stated plainly.**  Nothing here proves that for fair independent
  bits the even-indexed and odd-indexed sub-series are *independent* and
  *uniform*.  That step needs the law of the bit sequence as a measure (an
  infinite product measure, or Lebesgue measure on `[0,1)` read through binary
  digits) together with a de-interleaving measure isomorphism, and it is not
  formalised.  It is not smuggled in either: it appears as the explicit
  hypothesis `hEO` of `trapezoid_of_split`, whose conclusion is the paper's
  statement.  So the honest reading of this file is: *the algebra of the split
  and the whole convolution computation are certified; the probabilistic
  independence is assumed.*  `ABANDONED.md` §9 records it as outstanding.
* **Open intervals** are used for the uniform laws, as everywhere else in the
  tree; endpoints are null.
* `unif a` is `(ENNReal.ofReal a)⁻¹ • volume.restrict (Ioo 0 a)`, a
  probability measure for `a > 0` (`unif_univ`); for `a ≤ 0` it is the zero
  measure, and no statement uses it there.

---

## 4. Paperwork conventions

* The reconstructions `AXIOM-AUDIT-round11.md`, `CENSUS-round12.md`,
  `SCRUPLES-round12.md` and `AXIOM-AUDIT-round12.md` are written from the
  sources as they stand, and each says in its own header that it is a
  reconstruction made in round 13.  Where round 13 could not determine what an
  earlier session intended, the documents say so instead of guessing.
* Per the operating rules no tree-wide build and no tree-wide axiom audit was
  run: only `KindBox`, `CountingOperator` and `Trapezoid` were built, and only
  their own theorems were passed to `#print axioms`.  Every earlier claim in
  the tree rests on its own round's audit, unchanged.
