# CENSUS — round 9 (T27–T29)

Census-first, as in the earlier rounds: what the inherited round-8 tree already
contained, what round 9 reuses, what round 9 adds, and what was deliberately
left alone.

## 0. Summary of outcomes

| Target | Status |
| --- | --- |
| T27 `prop:immortal32` (immortal births) | **done** — `RequestProject/Immortal.lean` |
| T28 caption facts of `fig:records32` | **done** — `RequestProject/RecordGaps.lean` |
| T29a(i) the scaling identity `(1−r) r^j ξ_N = λ^{N−j}` | **done** — `RequestProject/FourierFloor.lean` |
| T29a(ii) Lucas trace identity, `‖φ^m‖ ≤ φ^{−m}` | **done** — `RequestProject/Lucas.lean` |
| T29a(iii) positivity of `∏_{m∈ℤ}|cos(π φ^m)|` | **done** — `RequestProject/FourierFloor.lean` |
| T29a(iv) `N → ∞` limit of `\|ν̂_r(ξ_N)\|` | **done** — `RequestProject/FourierFloor.lean` |
| T29b certified enclosure `[66/10⁴, 67/10⁴]` (optional) | **done** — `RequestProject/FourierEnclosure.lean` |
| T29c analogues of (ii)–(iv) at the **plastic** number (optional) | **done** — `RequestProject/FourierGeneral.lean`, `RequestProject/PlasticFourier.lean` |
| T29c at the **supergolden** parameter (optional) | **done** — `RequestProject/SupergoldenFourier.lean` |
| T29c at the **tribonacci** parameter (optional) | **done** — `RequestProject/TribonacciFourier.lean` |

No `sorry`, no `admit`, no new `axiom`, no `native_decide`.  The semantic axiom
audit passes over the whole tree.

## 1. Census: what was already present

Read and rebuilt in place before any new work.  All of these are genuine and
none of them was modified.

| Item the commission points at | Identifier(s) | File | Finding |
| --- | --- | --- | --- |
| the `w`-coordinate dictionary at `λ = 3/2` | `Ternary.wstep`, `witer`, `witer_succ`, `witer_shift`, `two_mul_act`, `translate_core` | `Translation.lean` | present and proved; T27 does **not** re-derive it |
| the finite Mahler criterion and the equivalence | `Ternary.MahlerAlive`, `MahlerCriterion`, `ctrl`, `moveOf`, `mahlerAlive_iff`, `unbounded_iff_mahler` | `Translation.lean` | present and proved; this is the whole engine of T27 |
| distinct births give distinct knots (`lem:distinct`) | `Ternary.birthSet`, `card_birthSet`, together with `card_run` | `Translation.lean`, `Suffix.lean` | present and proved; already packaged inside `unbounded_iff_mahler`, so T27 needs no new bookkeeping |
| periodic kind words | `KindWord`, `N_unbounded_of_kindWord` | `PeriodicYield.lean` | present and proved; **not** used by T27 — the immortality route goes through `Translation.lean` directly and is shorter |
| the seven record words and their configurations | `record2 … record7`, `runZ_record2 … runZ_record7`, the containments `2 ⊂ 3 ⊂ 5 ⊂ 7`, `4 ⊂ 6` | `TwoStep.lean` | present and proved (round 5); T28 extends this file through a sibling |
| the integer model of a configuration | `runZ`, `runZFrom`, `emb`, `emb_injective`, `run_eq_image_runZ` | `RunRational.lean` | present and proved; this is the bridge every T28 statement uses |
| minimal depths `d_{3/2}(k)` for `k ≤ 4` | `RecordDepths.lean` | `RecordDepths.lean` | present and proved; T28 makes **no** minimality claim beyond it |
| the golden ratio, its conjugate and `φ⁻¹` | `Real.goldenRatio`, `Real.goldenConj`, `Real.goldenRatio_sq`, `Real.inv_goldenRatio` | Mathlib | present |
| the five-point golden orbit | `Golden.p`, `absSurv`, `absAct` | `Golden.lean` | present and proved; unrelated to T29 and untouched |
| the semantic axiom audit | `KnotGame.Audit` | `AxiomAudit.lean` | present; extended automatically to the new modules |

**Census findings that shaped the plan.**

* **Nothing Fourier-analytic existed in the tree.**  There is no Bernoulli
  convolution, no cosine product, no Lucas sequence, and no `Multipliable`
  anywhere in the round-8 tree.  `Lucas.lean` and `FourierFloor.lean` are
  wholly new.  Mathlib supplies `Real.goldenRatio` and the infinite-product
  API (`Multipliable`, `Real.multipliable_of_summable_log`,
  `Real.rexp_tsum_eq_tprod`) but no Lucas numbers as such: `Nat.fib` is there,
  `lucas` is not, so it is defined here.
* **T27 was *not* partly present.**  `Translation.lean` states avoidance only
  up to a *finite horizon* `N` (`MahlerAlive c b N`).  The horizon-free
  ("immortal") condition of `prop:immortal32` had no counterpart; that is the
  one genuinely new definition of T27.
* **T28's inputs were all present.**  Round 5 had already certified the seven
  configurations as exact finite sets of integers over `2^j`; every caption
  claim of round 9 is a decidable statement about those same integer sets.
  The only new *definition* is the packaging predicate `IsMinGapAt`.
* **`record1` was missing.**  `TwoStep.lean` starts at `k = 2`.  The one-move
  word `[M]` is added in `RecordGaps.lean` so that claim (a) covers all seven
  values `k = 1, …, 7` of the caption.

## 2. What round 9 reuses

| Item reused | Identifier | File |
| --- | --- | --- |
| the game | `Move`, `act`, `survives`, `survivesWord`, `posAfter`, `run`, `N`, `d` | `Basic.lean` |
| `r = λ⁻¹`, `g = 1 − r` | `r`, `g`, `r_pos`, `g_add_r` | `Basic.lean` |
| the `3/2` dictionary and the unboundedness equivalence | `witer`, `MahlerAlive`, `MahlerCriterion`, `unbounded_iff_mahler` | `Translation.lean` |
| the integer configuration model | `runZ`, `run_eq_image_runZ`, `emb`, `emb_injective` | `RunRational.lean` |
| the seven record words and configurations | `record2 … record7`, `runZ_record2 … runZ_record7` | `TwoStep.lean` |
| the golden ratio API | `Real.goldenRatio`, `goldenConj`, `goldenRatio_sq`, `goldenConj_sq`, `inv_goldenRatio`, `goldenRatio_mul_fib_succ_add_fib` | Mathlib |
| infinite products and sums | `Multipliable`, `Real.multipliable_of_summable_log`, `Real.rexp_tsum_eq_tprod`, `tsum_of_nat_of_neg_add_one`, `Summable.of_nat_of_neg_add_one`, `tendsto_sum_nat_add` | Mathlib |
| the semantic axiom audit | `KnotGame.Audit` | `AxiomAudit.lean` |

**No inherited definition was changed and no inherited statement was
re-derived.**  The only edit to an inherited file is the four new imports in
`RequestProject/All.lean`.

## 3. What is new in round 9

| File | Content |
| --- | --- |
| `RequestProject/Immortal.lean` | **T27**.  `Ternary.MahlerImmortal c b` (the horizon-free avoidance condition), `mahlerAlive_of_immortal`, and the two conclusions `unbounded_of_infinite_immortal` (control `c : ℕ → ℤ` with values in `{0,1,2}`) and `unbounded_of_infinite_immortal_fin` (control `c : ℕ → Fin 3`, the paper's phrasing).  The proof selects `k` immortal births below a common index with `Nat.nth` and feeds them to `unbounded_iff_mahler`. |
| `RequestProject/RecordGaps.lean` | **T28**.  Two bridges to the integer model, `mem_run_of_emb_eq` and `gap_lower_bound_of_runZ`; the packaging predicate `IsMinGapAt S δ a b`; the one-move record `record1` with `runZ_record1`, `card_run_record1`, `d_le_one`; claim (a) as `half_mem_record1 … half_mem_record7` and the aggregate `half_mem_records`; claim (b) as `minGap_record2`, `minGap_record3` (gap `1/8`, realised by `(3/8, 1/2)`); claim (c) as `minGap_record4 … minGap_record7` (gap `13/512`, realised by `(243/512, 1/2)` at `k = 4, 6` and `(1/2, 269/512)` at `k = 5, 7`).  Every check is a kernel `decide` on exact integers. |
| `RequestProject/Lucas.lean` | **T29a(ii)**.  `Fourier.lucas : ℕ → ℤ` (`2, 1, L_{n+2} = L_n + L_{n+1}`); the trace identity `goldenRatio_pow_add_goldenConj_pow : φ^m + ψ^m = L_m`; `abs_goldenConj`, `goldenRatio_inv_pos`, `goldenRatio_inv_lt_one`; the distance bound `abs_goldenRatio_pow_sub_lucas : \|φ^m − L_m\| = (φ⁻¹)^m` and its nearest-integer form `abs_goldenRatio_pow_sub_round_le`; and `irrational_goldenRatio_pow_succ`. |
| `RequestProject/FourierFloor.lean` | **T29a(i), (iii), (iv)**.  `xi lam N = λ^N/(1−r)` and the scaling identity `xi_scaling`; `cosProd rr ξ = ∏'_{j≥0} \|cos(π (1−rr) rr^j ξ)\|`, `cosFac lam m = \|cos(π λ^m)\|`, and `cosProd_xi` (the transform along `ξ_N` is `∏_{j} \|cos(π λ^{N−j})\|`); at `λ = φ`: `goldenFac`, its positivity `goldenFac_pos` (via irrationality of `φ^m`), the two-sided log-summability chain `one_sub_goldenFac_le → abs_log_goldenFac_le → summable_log_goldenFac`, hence `multipliable_goldenFac`, `tprod_goldenFac_eq_exp` and **T29a(iii)** `goldenFourierFloor_pos`; the partial-product convergence `tendsto_log_partial`, `tendsto_tprod_partial` and **T29a(iv)** `tendsto_cosProd_xi_golden`; and the reflection symmetry `goldenFac_neg_natCast` with the square form `goldenFourierFloor_eq_sq`. |

| `RequestProject/FourierEnclosure.lean` | **T29b**.  The alternating-series Taylor bound `cos_taylor_err` and the interval lemma `cos_enclosure`; rational enclosures `gc_lb`, `gc_ub` of `φ⁻¹` and `pi_gc_pow_bounds` of the arguments `π φ^{−k}`; the coincidence `goldenFac_neg_one_eq` of the first two factors; the twelve factor enclosures `fac1 … fac12`; the head/tail split `tprod_neg_split` with the tail estimate `tail_abs_le` (`≤ 6·10⁻⁵`); and the conclusions `tprod_neg_enclosure` (the one-sided product to seven decimals) and **`goldenFourierFloor_enclosure`**, `66/10⁴ ≤ ∏_{m∈ℤ}|cos(π φ^m)| ≤ 67/10⁴`.  All arithmetic is `norm_num` over `ℚ` in the kernel. |
| `RequestProject/FourierGeneral.lean` | **T29c, engine**.  The structure `ConjApprox lam` (a constant `C`, a rate `t ∈ (0,1)`, the squared-distance hypothesis `(λ^m − n)² ≤ C t^{|m|}`, and non-vanishing of the factors) and, from it alone, `summable_log_cosFac`, `multipliable_cosFac`, `tprod_cosFac_eq_exp`, `tprod_cosFac_pos`, `tendsto_tprod_partial_gen` and `tendsto_cosProd_xi_gen`.  The golden case is **not** re-derived through it. |
| `RequestProject/PlasticFourier.lean` | **T29c at the plastic number**.  Sharp rational bounds `rho_lb`, `rho_ub`; `rho_sq_sub_one_eq_inv` (`ρ²−1 = ρ^{-1}`); the Perrin sequence `perrin` and the error `perr`; the second-order recurrence `perr_add_two`; the invariant form `pQ` with `pQ_succ`, `pQ_eq`; the distance bound **`perr_sq_le`** (`e_m² ≤ 4(ρ²−1)^m`); the certificate `plasticApprox`; and the conclusions `multipliable_plasticFac`, **`plasticFourierFloor_pos`**, **`tendsto_cosProd_xi_plastic`**.  Positivity of the factors uses `cos_pi_ne_zero_of_between` plus kernel arithmetic on the exponents `0 … 9` and the negative ones. |
| `RequestProject/SupergoldenFourier.lean` | **T29c at the supergolden ratio** `ψ` (`x³ = x²+1`).  `sg_t_eq_inv` (`ψ²−ψ = ψ^{-1}`) with the enclosures `sg_t_lb`, `sg_t_ub`; the trace `sgTrace` (`3, 1, 1`, `A_{m+3} = A_{m+2} + A_m`) and the error `sgErr`; the second-order recurrence `sgErr_add_two`; the invariant form `sgQ` with `sgQ_succ`, `sgQ_eq`; the distance bound **`sgErr_sq_le`** (`e_m² ≤ 4(ψ²−ψ)^m`); the certificate `supergoldenApprox`; and the conclusions `multipliable_supergoldenFac`, **`supergoldenFourierFloor_pos`**, **`tendsto_cosProd_xi_supergolden`**.  The half-integer exclusions cover the exponents `0 … 7` and the negative ones. |
| `RequestProject/TribonacciFourier.lean` | **T29c at the tribonacci constant** `τ` (`x³ = x²+x+1`).  The same skeleton: `tri_t_eq_inv` (`τ²−τ−1 = τ^{-1}`) with `tri_t_lb`, `tri_t_ub`; the trace `triTrace` (`3, 1, 3`, `A_{m+3} = A_{m+2} + A_{m+1} + A_m`), the error `triErr`, the recurrence `triErr_add_two`, the form `triQ` with `triQ_succ`, `triQ_eq`, the distance bound **`triErr_sq_le`** (`e_m² ≤ 4(τ²−τ−1)^m`), the certificate `tribonacciApprox`, and `multipliable_tribonacciFac`, **`tribonacciFourierFloor_pos`**, **`tendsto_cosProd_xi_tribonacci`**.  Here the exponents `0 … 4` need the finite check. |

No new search program was needed: round 9 adds no external numerical
certificate — every number in `FourierEnclosure.lean` and in the three
parameter files is checked by the kernel over exact rationals.

## 4. Correspondence with the paper

| Paper label | Lean identifier | File |
| --- | --- | --- |
| `prop:immortal32` | `KnotGame.Ternary.unbounded_of_infinite_immortal`, `…_fin` | `Immortal.lean` |
| `fig:records32` caption, "1/2 is in every record" | `KnotGame.half_mem_records` | `RecordGaps.lean` |
| `fig:records32` caption, min gap `1/8` at `k = 2, 3` | `KnotGame.minGap_record2`, `minGap_record3` | `RecordGaps.lean` |
| `fig:records32` caption, min gap `13/512` at `k = 4,…,7` | `KnotGame.minGap_record4 … minGap_record7` | `RecordGaps.lean` |
| §11, `(1−r) r^j ξ_N = λ^{N−j}` | `KnotGame.Fourier.xi_scaling`, `cosProd_xi` | `FourierFloor.lean` |
| §11, Lucas trace and `‖φ^m‖ ≤ φ^{−m}` | `KnotGame.Fourier.goldenRatio_pow_add_goldenConj_pow`, `abs_goldenRatio_pow_sub_lucas`, `abs_goldenRatio_pow_sub_round_le` | `Lucas.lean` |
| §11, the Fourier floor is positive | `KnotGame.Fourier.goldenFourierFloor_pos` | `FourierFloor.lean` |
| §11, `\|ν̂_r(ξ_N)\| → ∏_{m∈ℤ}\|cos(π φ^m)\|` | `KnotGame.Fourier.tendsto_cosProd_xi_golden` | `FourierFloor.lean` |
| §11, the numerical value `6.6135 × 10⁻³` | `KnotGame.Fourier.goldenFourierFloor_enclosure` (as the enclosure `[66/10⁴, 67/10⁴]`; the value itself is not asserted) | `FourierEnclosure.lean` |
| §11 at the plastic number (T29c) | `KnotGame.Fourier.perr_sq_le`, `plasticFourierFloor_pos`, `tendsto_cosProd_xi_plastic` | `PlasticFourier.lean` |
| §11 at the supergolden ratio (T29c) | `KnotGame.Fourier.sgErr_sq_le`, `supergoldenFourierFloor_pos`, `tendsto_cosProd_xi_supergolden` | `SupergoldenFourier.lean` |
| §11 at the tribonacci constant (T29c) | `KnotGame.Fourier.triErr_sq_le`, `tribonacciFourierFloor_pos`, `tendsto_cosProd_xi_tribonacci` | `TribonacciFourier.lean` |
| `prop:twostep` exhaustiveness | — not commissioned, not attempted | — |
| `prop:kinddim` dimension statements | — not commissioned, not attempted | — |

## 5. Not commissioned, not attempted

Exhaustiveness for `prop:twostep`; the exact values `d_{3/2}(7) = 52` and
`d_{3/2}(8) ≥ 57`; the Hausdorff/box dimension statements of `prop:kinddim`.
None of these was touched.  Both optional targets are delivered in full: T29b,
and T29c at all three parameters (plastic, supergolden, tribonacci).  What each
of those statements does and does not assert is recorded in
`SCRUPLES-round9.md` §§5–6.
