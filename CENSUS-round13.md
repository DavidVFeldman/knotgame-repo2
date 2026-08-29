# CENSUS — round 13 (T36–T39)

Census-first, as in every earlier round: what the inherited tree already
contained, what round 13 reuses, what it adds, and where it stops.  The
deviations are in [`SCRUPLES-round13.md`](SCRUPLES-round13.md), the axiom
reports in [`AXIOM-AUDIT-round13.md`](AXIOM-AUDIT-round13.md), and the
negative record in [`ABANDONED.md`](ABANDONED.md).

## 0. Summary of outcomes

| Task | Statement | Status | File |
| --- | --- | --- | --- |
| T36 — repair `KindBox` | covering numbers, the triadic bounds, the squeeze to all scales, and both box dimensions of `K_{3/2}` equal to `log 2 / log 3` | **done**; the file now elaborates, is imported by `All.lean`, and the squeeze `tendsto_boxQuot` (left unproved in the old file) is proved | `RequestProject/KindBox.lean` |
| T37 — the missing paperwork | `AXIOM-AUDIT-round11.md`; census, scruples and audit for round 12; `ABANDONED.md` §1; a round-9 and a round-13 section for the checklist | **done** | this and the neighbouring documents |
| T38 — the counting operator (`prop:lebeigen`) | `T 1 = (2/λ)·1`, and the mean-count integrals | **done, with a correction**: `(2/λ)^m` is proved for the *branch* count, and `(3/λ)^m` — not `(2/λ)^m` — for the kind-word count in the project's existing three-letter alphabet | `RequestProject/CountingOperator.lean` |
| T39 (optional) — the trapezoid at `λ = √2` (`prop:trapezoid`) | the even/odd splitting of the backward series; the convolution of two uniform laws; the trapezoidal density | **done except for one step**: the independence and uniformity of the two parts is *not* formalised and enters as an explicit hypothesis | `RequestProject/Trapezoid.lean` |

No `sorry`, no `admit`, no new `axiom`, no `@[implemented_by]`, no
`native_decide` in any file this round touched.

## 1. What was already present, and is reused rather than re-derived

| Inherited item | File | Used by |
| --- | --- | --- |
| `KindDim.K`, `cyl`, `cval`, `E`, `dexp`, `dimH_K_le` | `KindDim.lean` (round 11) | T36 |
| `KindLower.kindMeasure`, `kindMeasure_K`, `kindMeasure_le_of_ediam`, `dimH_K_eq` | `KindDimLower.lean` (round 12) | T36's Frostman lower bound on covering numbers |
| `KindTree.kindWords`, `words`, `card_kindWords_three_halves` | `KindTree.lean` (round 8) | T36's triadic upper bound; T38's kind-word count and the check on its constant |
| `f`, `r`, `g`, `survives`, `survivesWord`, `act`, `posAfter`, `Move` | `Basic.lean` | T38 (all survival predicates reused, none redefined) |
| `Sqrt2.lam2`, `lam2_sq`, `one_lt_lam2`, `r_lam2` | `Sqrt2.lean` (round 11) | T39 |
| `Ternary.summable_itinerary`, `itinerary_tsum` (`prop:itinerary`) | `Mahler.lean` (round 8) | T39: the identification of the backward series with the knot value |
| Mathlib's `Measure.prod`, `Measure.map`, `withDensity`, Tonelli | — | T38, T39 |

Nothing in the inherited tree contained a covering number, a box dimension, a
transfer operator, a branch-word count, or any measure on the backward orbit;
`rg` over the sources returns no occurrence of `coverNum`, `boxDim`,
`bcount`, `kcount`, `convDens` or `trapDens` before this round.

## 2. What round 13 adds

| File | Lines | Contents |
| --- | --- | --- |
| `RequestProject/KindBox.lean` | 410 | `coverSizes`, `coverNum`, `coverSizes_mono_scale`, `coverSizes_upward`, `coverNum_le`, `coverNum_mono`, `coverSizes_of_finset`, `coverSizes_K_triadic`, `coverNum_K_le`, `le_coverNum_K`; the bracketing index `bidx` with `bidx_succ_lt`, `le_bidx_pow`, `bidx_ge`, `tendsto_bidx`; `upperBoxDim`, `lowerBoxDim`, `hiSeq`, `loSeq`, `tendsto_hiSeq`, `tendsto_loSeq`, the bracketing lemmas, **`tendsto_boxQuot`**, **`upperBoxDim_K`**, **`lowerBoxDim_K`**, **`boxDim_K`** |
| `RequestProject/CountingOperator.lean` | 664 | `T`, the four preimage lemmas, `f_zero_injective`, `f_one_injective`, **`T_one`**; the measure engine (`integral_Ioo_comp_affine`, `integral_Ioo_comp_mul`, `integral_indicator_Ioi/Iio`, `integral_add4`); the branch count `bcount` with `measurable_bcount`, `integrableOn_bcount`, `integral_bcount_succ`, **`integral_bcount`**, and `binWords`, `branchLegal`, `branchSurvivesWord`, `branchWords`, **`bcount_eq_card`**; the kind count `kcount` with `kcount_eq_sum`, `measurable_kcount`, `kcount_succ`, `integral_kcount_succ`, **`integral_kcount`**, **`integral_kcount_three_halves`** |
| `RequestProject/Trapezoid.lean` | 405 | `bval`, `evenPart`, `oddPart`, `r_lam2_sq`, `summable_half`, `tsum_half_le_two`, **`bval_split`**, **`evenPart_mem_Icc`**, **`oddPart_mem_Icc`**; `convDens`, `unifSum`, `unif`, `inner_convDens`, **`unifSum_apply`**, **`unifSum_eq_withDensity`**; `trapDens`, `measurable_trapDens`, `trapDens_nonneg`, **`convDens_sqrt_two`**, `unif_univ`, **`trapezoid_law`**, **`isProbabilityMeasure_trapDens`**, **`trapezoid_of_split`** |

The only inherited Lean file edited is `RequestProject/All.lean` (three
imports added), plus one docstring correction in
`RequestProject/KindDimLower.lean` (a forward reference to three declarations
that were never written; see `SCRUPLES-round12.md` §4).  `.github/workflows/ci.yml`
gains the three new modules in its explicit module list.

Documents added or corrected: `AXIOM-AUDIT-round11.md` (reconstructed),
`CENSUS-round12.md`, `SCRUPLES-round12.md`, `AXIOM-AUDIT-round12.md`
(reconstructions), this census, `SCRUPLES-round13.md`,
`AXIOM-AUDIT-round13.md`, `ABANDONED.md` §1 (rewritten: no longer stale),
`UNBUILT.md` (the `KindBox.lean` entry closed), and
`GITHUB_HANDOFF_CHECKLIST` (a round-9 section, a round-13 section, and §15.6
pruned of what this round closes).

## 3. The one correction to the commission

T38 asks for `∫₀¹ K_λ(m,x) dx = (2/λ)^m` with `K_λ(m,x)` the number of kind
words of length `m` from `x`, *and* asks that the existing survival predicates
be reused.  Those two requirements are incompatible: the existing predicate
counts words in the three-letter **move** alphabet `L, M, R`, and each of the
three moves is a bijection from its legal domain onto `(0,1)` (`M` in two
pieces), so the mean factor per step is `3/λ`.  Both true statements are
formalised — `integral_bcount : (2/λ)^m` for the two-branch count that the
operator `T` transfers, and `integral_kcount : (3/λ)^m` for the move-word
count — and neither the false one nor any claim that they agree is anywhere
in the tree.  The independent check is at `λ = 3/2`, where `3/λ = 2` matches
round 8's exact count `KindTree.card_kindWords_three_halves = 2^n`.

## 4. Where the round stops

* T39's missing step: that the even-indexed and odd-indexed sub-series of the
  backward expansion at `λ = √2` are *independent and uniform*.  Everything
  downstream of that fact is proved; the fact itself is a hypothesis of
  `trapezoid_of_split`.  See `SCRUPLES-round13.md` §3 and `ABANDONED.md` §9.
* Everything already listed in `ABANDONED.md` §2–§8 is untouched by this
  round, including the out-of-closure `ExpSharpest` certificate: the strongest
  *audited* growth rate at `λ = 3/2` remains `ExpSharper`'s `26 ^ ⌊m/14⌋`.
* Per the operating rules, no tree-wide build and no tree-wide axiom audit was
  run; only the three modules of this round were built and audited.
