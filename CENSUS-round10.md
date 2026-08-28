# CENSUS — round 10 (T30–T32)

Census-first, as in the earlier rounds: what the inherited round-8 tree already
contained, what round 10 reuses, what round 10 adds, and — for T32 — the
infeasibility report the commission asks for.

## 0. Summary of outcomes

| Target | Status |
| --- | --- |
| T30 `prop:norecur` (+ `no_identity_block`) | **done** — `RequestProject/NoRecurrence.lean` |
| T31 sharper exponential certificate at `λ = 3/2` | **done** — `26 ^ ⌊m/14⌋`, rate `26^(1/14) ≈ 1.26203 > 15^(1/12) ≈ 1.25316` — `RequestProject/ExpSharper.lean` |
| T32 doubling certificate above `φ` containing `√3` | **done on a narrower window than commissioned** — `[3457/2000, 4331/2500] = [1.7285, 1.7324]` instead of `[17/10, 7/4]`; see §4 — `RequestProject/ExpAbove.lean` |

No `sorry`, no `admit`, no new `axiom`, no `native_decide`.  The semantic axiom
audit passes over the whole tree: *axiom audit passed: 1290 theorems, axioms
confined to [propext, Classical.choice, Quot.sound]* (1198 at the end of
round 8).

**Parallel-run clause observed.**  Every Lean declaration of this round lives in
a new file.  The only inherited file touched is `RequestProject/All.lean`, and
only to add three imports (`NoRecurrence`, `ExpSharper`, `ExpAbove`).
`Translation.lean`, `PeriodicYield.lean` and `TwoStep.lean` are untouched, and
no file whose name begins `Fourier` or `Floor` was added.  (The one non-Lean
inherited file that changed is `scripts/expcert_dfs.py`, an untrusted search
program: see §5.)

## 1. What was already present, and is reused rather than re-derived

| Inherited item | File | Used by |
| --- | --- | --- |
| `Ternary.Dyadic`, `dyadic_act`, `dyadic_posAfter`, `three_mul_ne_one/two` (round 8's dyadic invariant) | `Ternary.lean` | T30 — **reused verbatim**; the paper's `3^B − 2^B` computation is *not* redone (see SCRUPLES-round10 §1) |
| `Permanence`, `KnotAt`, `run`, `posAfter` | `Permanence.lean`, `Basic.lean` | T30 |
| `ExpCount.K`, `kappa`, `Kx_mono`, `image_append_subset` | `ExpCount.lean` | T31, T32 |
| `ExpCount.Doubling`, `two_pow_le_K_of_doubling` | `ExpCount.lean` | reference point for T32's weakened hypothesis |
| `ExpMulti.MDoubling`, `k_pow_le_K_of_mdoubling` | `ExpMulti.lean` | T31 — the machinery the commission asks to be used |
| `ExpCert.Cell`, `iok`, `chained`, `exists_cell`, `mcellOK` interval arithmetic | `ExpCert.lean`, `ExpMultiCert.lean` | T31, T32 |
| round 7's certificate `15 ^ ⌊m/12⌋` at `3/2` | `ExpSharp.lean`, `ExpSharpData.lean` | T31's baseline (`sharper_rate`, `sharper_rate_real` compare against it) |
| the certified two-cycle `{1/(λ+1), λ/(λ+1)}` and the branching window `(1 − 1/λ, 1/λ)` | `Branching.lean` | T32's diagnosis of *why* the window above `φ` is hard |

Nothing in the tree contained: a recurrence statement of any kind (`rg
"no_recurrence|identity_block"` over the round-8 tree returns nothing); any
certificate at `λ = 3/2` beyond round 7's `15/12`; any statement at all about
parameters above the golden ratio — every exponential bound in the inherited
tree carries `λ² < λ + 1` or lives in `[1000/667, 8/5]`.

## 2. What round 10 adds

| File | Contents |
| --- | --- |
| `RequestProject/NoRecurrence.lean` | T30: `dyadic_level_unique`, `dyadic_posAfter_of_dyadic`, `dyadic_of_knotAt`, `posAfter_length_eq`, `no_recurrence`, `no_recurrence_knotAt`, `positions_pairwise_ne`, `knot_positions_injective`, `no_identity_block`, `no_identity_block_config` |
| `RequestProject/ExpSharperData.lean` | T31 data: 747 cells tiling `J = [1/6, 5/6]`, each with 26 branch words of length 14, in 15 groups |
| `RequestProject/ExpSharper.lean` | T31 checks and conclusions: `cells_chained`, `cellsG0_ok`…`cellsG14_ok`, `mdoubling_three_halves`, `twentysix_pow_le_K`, `sharper_rate`, `sharper_rate_real` |
| `RequestProject/ExpVar.lean` | T32 machinery: `Divergent`, `append_ne_of_divergent`, `VDoubling` (doubling with a **variable** return time), `two_mul_kappa_le_var`, `two_pow_le_kappa_var`, `two_pow_le_K_of_vdoubling`, the checkers `vcellOK`, `vlamCellOK`, and the soundness theorems `vdoubling_of_cert`, `vdoubling_of_window` |
| `RequestProject/ExpAboveData0.lean` … `ExpAboveData11.lean`, `ExpAboveData.lean` | T32 data: 180 parameter cells carrying 17 141 point cells, 246 225 letters, max word length 18 |
| `RequestProject/ExpAboveChecks.lean` | T32 kernel checks: `pcells_chained`, `pcellsG0_ok`…`pcellsG35_ok`, `pcells_ok`, `Tbound = 18` |
| `RequestProject/ExpAbove.lean` | T32 conclusions: `vdoubling_above`, `two_pow_le_K_above`, `golden_lt_window`, `sqrt_three_mem_window`, `two_pow_le_K_sqrt_three`, `K_unbounded_above` |

Search programs added (untrusted): `scripts/gen_expsharper.py` (T31 data),
`scripts/expvar_search.py` and `scripts/gen_expabove.py` (T32 data and checks).

## 3. T31 — the practical ceiling

The commission asks for the ceiling actually hit.  Measured with
`scripts/expcert_dfs.py` at `λ = 3/2` (the multiplicity `k` is the largest for
which a full tiling of `J` was found at return time `T`; "cells" is the size of
the tiling, i.e. the kernel's workload):

| `J` | `T` | best `k` | cells | rate `k^(1/T)` |
| --- | --- | --- | --- | --- |
| `[1/4, 3/4]` | 12 | 15 | 503 | 1.25316 (round 7) |
| `[1/4, 3/4]` | 13 | 20 | 747 | 1.25916 |
| `[1/4, 3/4]` | 14 | 26 | 1016 | 1.26203 |
| `[1/4, 3/4]` | 15 | 34 | 1425 | 1.26502 |
| `[1/4, 3/4]` | 16 | 49 | 2859 | 1.27537 |
| `[1/4, 3/4]` | 17 | 66 | 4449 | 1.27948 |
| `[1/6, 5/6]` | 14 | **26** | **747** | **1.26203** (shipped) |
| `[1/6, 5/6]` | 15 | 34 | 1097 | 1.26502 |

The shipped certificate is the `[1/6, 5/6]`, `T = 14`, `k = 26` one: the same
rate as the `[1/4, 3/4]` row at a quarter fewer letters.  Its kernel cost is
**790 s** for 272 250 letters, in 15 groups; a single ungrouped reduction does
not go through.

**The ceiling.**  The kernel cost is essentially linear in `cells × k × T`
(the number of "letters" the checker reduces), while the cell count grows like
`λ^T`.  Extrapolating the table, `T = 17, k = 66` is roughly `10×` the shipped
cost — some three hours of kernel time for one file, and the *elaboration* of
the data literal (not the reduction) becomes the binding constraint first: the
`T = 17` data is ≈ 5 MB of Lean source.  The commission's aspiration of rate
`1.29` needs, on the observed trend, `T ≈ 20–22`, i.e. tens of thousands of
cells and tens of millions of letters.  **That was not kernel-feasible here**
and is reported as such.  The shipped improvement is `1.25316 → 1.26203`,
certified in both the integer form (`sharper_rate : 15^14 < 26^12`) and the
real form (`sharper_rate_real : 15^(1/12) < 26^(1/14)`).

## 4. T32 — what is certified, and the infeasibility report

### 4.1 What is certified

> **The commissioned window `[17/10, 7/4]` is NOT certified.**  What is
> certified is `[3457/2000, 4331/2500] = [1.7285, 1.7324]`, a strictly narrower
> rational window that still lies entirely above the golden ratio
> (`golden_lt_window`) and still **contains `√3 = 1.7320508…`**
> (`sqrt_three_mem_window`).

On that window, for every parameter,

```
2 ^ ⌊m / 18⌋  ≤  K λ m          (two_pow_le_K_above)
2 ^ ⌊m / 18⌋  ≤  K (√3) m       (two_pow_le_K_sqrt_three)
```

certified by 180 parameter cells carrying 17 141 point cells in all
(246 225 letters, maximal word length 18), checked in 36 kernel groups.
Rate `2^(1/18) ≈ 1.0393`.

### 4.2 Why the wider window fails — parameters tried

1. **Fixed-length doubling is hopeless above `φ`.**  Round 7's `Doubling`
   hypothesis asks the two words issued from a point to have a *common* length
   `T`.  With `scripts/expcert_dfs.py` at single parameters of `[1.70, 1.75]`
   no tiling was found at any `T ≤ 18`, at any core interval tried.  This is the
   two-cycle's shadow: above `φ` the certified two-cycle
   `{1/(λ+1), λ/(λ+1)}` of `Branching.lean` lies *outside* the branching window
   `(1 − 1/λ, 1/λ)`, so points near its preimages take many, and irregularly
   many, steps to return.  Hence the weakened hypothesis `VDoubling` of
   `ExpVar.lean`, in which the two words may have different lengths provided
   they *diverge*.
2. **The core interval must sit inside the branching window.**  With
   `J = [2/5, 3/5]` the search provably stalls: `J` then contains points whose
   whole forward orbit avoids the branching window (the survivor set of the hole
   above `φ` is nonempty), e.g. at `λ ≈ 1.7325` the point `x* ≈ 0.43633`, a
   preimage of the two-cycle.  `J = [43/100, 57/100]` is inside the branching
   window for every parameter of the window and is what is shipped.
3. **Two search fixes were needed** (both in `scripts/expvar_search.py`):
   candidate words must have admissible right endpoint *strictly* greater than
   the cell's left endpoint — otherwise the greedy stalls forever at preimages
   of `1` — and the greedy backtracks by halving the previous cell when it
   stalls.
4. **Parameter resolution.**  A single certificate serves an interval of
   parameters, but only a short one: parameter cells of width `≈ 2·10⁻⁵` carry
   100–130 point cells each; a slice of width `10⁻⁴` typically needs 2–15
   parameter cells.  This is the reason the certified window is short: the
   parameter-cell count, hence the kernel cost, is essentially proportional to
   the *width* of the window.
5. **Where it breaks.**  Scanning `[1.728, 1.736]` in slices of width `10⁻⁴`
   (adaptive subdivision to depth 6, `Tmax = 20`), the search **fails** on
   `[1.7282, 1.7283]`, `[1.7324, 1.7325]`, `[1.7325, 1.7326]`,
   `[1.7327, 1.7328]`, `[1.7328, 1.7329]` and succeeds elsewhere.  The maximal
   contiguous successful range containing `√3` is exactly
   `[1.7283, 1.7324]`; the shipped window `[1.7285, 1.7324]` is inside it.
   The failures cluster where the tiling cells shrink to nothing — again the
   shadow of the two-cycle, whose preimages accumulate at those parameters.
   Whether they are genuine obstructions or only obstructions to *this* greedy
   is not decided here.
6. **Cost.**  Generating the shipped data takes ≈ 5 min of Python.  Elaborating
   it took the split into twelve files (`ExpAboveData0`…`11`): as a single
   18 213-line file it exceeded 17 min and 8.6 GB before being abandoned.  Split,
   elaboration is ≈ 300 s and the kernel checks ≈ 1 100 s.  A window of the
   commissioned width `[17/10, 7/4]` would need, at the observed density,
   roughly 2 300 parameter cells and 220 000 point cells — about `13×` the
   shipped data, i.e. some four hours of kernel time and ≈ 240 000 lines of
   generated Lean — *and* it would first have to get past the failure
   parameters of item 5, which no subdivision depth tried (up to 6, i.e. cells
   of width `1.6·10⁻⁶`) cleared.

## 5. Files changed outside `RequestProject/`

* `scripts/expcert_dfs.py` — inherited from round 7; the one change is the
  strict `q > p` test on candidate right endpoints described in §4.2(3).  It is
  an untrusted search program; no Lean statement depends on it.
* `knotgame.tex` — replaced with the round-10 paper source shipped with the
  commission.
* New: `scripts/gen_expsharper.py`, `scripts/expvar_search.py`,
  `scripts/gen_expabove.py`.

## 6. Still not commissioned, still not attempted

Exhaustiveness for `prop:twostep`; `d_{3/2}(7) = 52` and `d_{3/2}(8) ≥ 57`; the
Hausdorff/box dimensions of `prop:kinddim`; and round 9's targets (immortal
births, record min-gaps, the Fourier floor at `φ`), which are out of scope by
the parallel-run clause.
