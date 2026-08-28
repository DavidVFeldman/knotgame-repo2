# CENSUS — round 7 (the three items the notes flag as open)

Census-first, as in the earlier rounds: what the inherited tree already contained,
what round 7 reuses, and what is new.

## 1. What was inherited

The inherited tree (rounds 1–6) was rebuilt in place before any new work.  It builds, contains
no `sorry`, `admit`, `axiom` or `native_decide`, and the semantic axiom audit
passes.  **No inherited definition was changed and no inherited statement was
re-derived.**  The only edits to inherited files are

* three added imports in `RequestProject/All.lean` (`ExpLower`, `ExpWindow`,
  `ReturnTail`);
* nothing else.

| Item reused by round 7 | Identifier | File |
| --- | --- | --- |
| the two branch maps and their images | `KnotGame.f`, `f_zero`, `f_one`, `f_mem_Ioo` | `Basic.lean`, `Branching.lean` |
| legality of a branch and of a branch word | `KnotGame.BLegal`, `KnotGame.bSurvives` | `Branching.lean` |
| the kind count | `KnotGame.K`, `K_eq_card_bSurvives` | `BranchingCount.lean` |
| `r = λ⁻¹`, `g = 1 − r` and their arithmetic | `KnotGame.r`, `KnotGame.g`, `lam_mul_r`, `lam_mul_g`, `g_add_r` | `Basic.lean` |
| the window and the chosen child | `KnotGame.Window`, `KnotGame.cb`, `cb_legal`, `cb_eq_zero`, `cb_eq_one`, `cb_of_le_g`, `cb_of_r_le` | `Branching.lean` |
| the no-jump lemma | `KnotGame.no_jump_low`, `no_jump_high` | `Branching.lean` |
| `λ < φ` in the usable form | `KnotGame.lt_two_of_sq_lt` | `Branching.lean` |
| the common parameter window `[1000/667, 8/5]` | `KnotGame.common_window` | `CommonWindow.lean` |
| the semantic axiom audit | `KnotGame.Audit` | `AxiomAudit.lean` |

**Census finding.**  Nothing in the inherited tree addressed any of the three
items the notes mark `[open]`: the return-time tail bound, the renewal
inequality, and the exponential lower bound for `K_m`.  Round 4's
`K_m ≥ ⌊m/(B+1)⌋` (linear) was the strongest count available.

## 2. What is new in round 7

| File | Content |
| --- | --- |
| `RequestProject/ExpCount.lean` | the covering machinery: `rapp` (image of a point under a branch word), absorption (`bSurvives_of_image_mem`), the localized counts `Kx`, `kappa`, the doubling property `Doubling`, the **renewal step** `two_mul_kappa_le`, and the export `two_pow_le_K_of_doubling` |
| `RequestProject/ExpCert.lean` | interval arithmetic in the point *and in the parameter*: `ilo`, `ihi`, the checker `iok` with its soundness lemma `rapp_mem_of_iok`, certificates (`Cell`, `chained`, `cellOK`, `exists_cell`) and `doubling_of_cert` |
| `RequestProject/ExpLower.lean` | the instance at `λ = 3/2`: a 15-cell certificate for `J = [1/4,3/4]` with `T = 5`, giving `doubling_three_halves` and `2 ^ (m/5) ≤ K (3/2) m` |
| `RequestProject/ExpWindowData.lean` | generated data: 24 parameter cells covering `[1000/667, 8/5]`, carrying 1333 interval cells in all, word length `T ≤ 8` |
| `RequestProject/ExpWindow.lean` | the checks of that data (`lamCells_chained`, `lamCells_ok`, both by kernel reduction) and the uniform results `doubling_window`, `two_pow_le_K_window : 2 ^ (m/8) ≤ K lam m` for every `λ ∈ [1000/667, 8/5]` |
| `RequestProject/ExpMulti.lean` | the same argument at multiplicity `k`: `MDoubling`, the renewal step `mul_kappa_le` and `pow_le_K_of_mdoubling` (`k ^ (m/T) ≤ K lam m`) |
| `RequestProject/ExpMultiCert.lean` | certificates at multiplicity `k` (`MCell`, `mcellOK`, `mdoubling_of_cert`) |
| `RequestProject/ExpSharpData.lean` | generated data: 503 cells tiling `[1/4,3/4]`, each with 15 distinct words of length 12, at `lam = 3/2` |
| `RequestProject/ExpSharp.lean` | the sharper bound at `lam = 3/2`: `15 ^ (m/12) ≤ K (3/2) m` (`fifteen_pow_le_K`) |
| `RequestProject/ReturnTail.lean` | the return time `retTime` of the discarded child, its finiteness (`exists_return`, `retTime_spec`), the sublevel description `lt_retTime_iff`, and the tail bounds `return_time_tail`, `return_time_tail_three_halves`, `return_time_tail_prob_three_halves` |

New search programs (never trusted by any Lean statement; the kernel checks
what they produce): `scripts/expcover.py`, `scripts/expcert.py`,
`scripts/expcert_interval.py`, and the generators `scripts/gen_expwindow.py`
and `scripts/gen_expsharp.py`, which write `RequestProject/ExpWindowData.lean`
and `RequestProject/ExpSharpData.lean`.

## 3. Correspondence with the notes

| Note item | What round 7 proves | Where |
| --- | --- | --- |
| `[open]` tail bound `P(S > t) ≤ C λ₀^{-t}` | `volume {x ∈ Window λ ∣ t < retTime λ x} ≤ 2g/λ^{t+1}` for all `λ ∈ (1, φ)`; at `3/2` the normalized form `≤ (4/3)(2/3)^t · volume (Window (3/2))` | `ReturnTail.lean` |
| the renewal inequality | replaced by its deterministic analogue: inside a doubling interval the localized count at least doubles every `T` steps (`two_mul_kappa_le`) | `ExpCount.lean` |
| exponential lower bound for `K_m` | `2 ^ (m/5) ≤ K (3/2) m`, sharpened to `15 ^ (m/12) ≤ K (3/2) m`, and `2 ^ (m/8) ≤ K λ m` uniformly on `[1000/667, 8/5]` | `ExpLower.lean`, `ExpSharp.lean`, `ExpWindow.lean` |

The deviations — in particular that the exponential bound does *not* go through
the return-time statistics, and that the rates obtained are below the measured
`(2/λ)^m` — are recorded in `SCRUPLES-round7.md`.
