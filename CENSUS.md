# Work Order 0 — Census

Map from every numbered statement of *Knot counts in an interval deletion game*
to its intended Lean identifier in the `KnotGame` namespace.

Two numbering schemes appear in the material. The commission refers to
statements in `section.index` form ("Lemma 1.1", "Proposition 6.5"). The paper
itself declares a single unsectioned counter
(`\newtheorem{theorem}{Theorem}` with all other environments sharing it), so the
compiled PDF numbers the statements sequentially `1 … 27`. The two schemes
therefore disagree; the table below carries both, keyed by the `\label` of the
source, which is unambiguous. **This numbering discrepancy is flag (B) below.**

Status values are exactly the three the commission allows: *in scope*,
*out of scope (computational)*, *deferred*.

## Table

| Paper (PDF) | `\label` | Commission | Statement | Lean identifier | Status | Done |
|---|---|---|---|---|---|---|
| Lemma 1 | `lem:distinct` | Lemma 1.1 | two survivors of a move have distinct images; `M` carries no survivor to `1/2`; card of `step` | `act_injOn`, `act_M_ne_half`, `card_step` | in scope | yes |
| Lemma 2 | `lem:suffix` | Lemma 2.1 | suffix decomposition of the knot count | `card_run` (with `card_runFrom`) | in scope | yes |
| Theorem 3 | `thm:mono` | Theorem 2.2 | `N λ n ≤ N λ (n+1)` | `N_mono` | in scope | yes |
| Proposition 4 | `prop:circle` | Prop. 2.3 | circle normal form, seam at `0` | — | deferred (no work order) | no |
| Remark 5 | `rem:jsr` | Remark 2.4 | joint spectral radius remark | — | out of scope (computational) | no |
| Theorem 6 | `thm:pisot` | Theorem 3.1 | `λ` Pisot ⟹ `Orb λ` finite | `orb_finite`, with the extracted uniform bound `conj_bound` | in scope | yes |
| Corollary 7 | `cor:decide` | Cor. 3.2 | for Pisot `λ` the reachable configurations form a finite set, `N` eventually periodic/decidable | — | deferred (only orbit finiteness is certified; see flag (G)) | no |
| Theorem 8 | `thm:phi` | Theorem 3.3 | `λ = φ`: five orbit points, `sup N = 2` | `Golden.sup_N_phi` (with `Golden.N_phi_le_two`, `Golden.N_phi_three`, `Golden.reach_closed`, `Golden.reach_card`) | in scope | yes |
| Proposition 9 | `prop:plastic` | Prop. 3.4 | `λ = ρ`: 153 orbit points, 25 525 configurations, `sup N = 7`, least lengths `1,3,5,7,12,17` | `Plastic.card_Orb_rho`, `Plastic.card_reachable_configs`, `Plastic.sup_N_rho`, `Plastic.d_rho_one`–`d_rho_seven` | in scope | **certified in round 6** — see `PROP9-PLASTIC.md`, flag (C) |
| Proposition 10 | `prop:big` | Prop. 4.1 | `N λ n = 1` for all `n ≥ 1` iff `2 ≤ λ` | `N_eq_one_iff` (with `survives_imp_min_lt_r`, `births_MRM`) | in scope | yes |
| Lemma 11 | `lem:overlap` | Lemma 5.1 | exact-overlap criterion: `1/√2`, `2/3` not roots of `{-1,0,1}`-polynomials | — | deferred (no work order) | no |
| Remark 12 | — | Remark 5.2 | interpretation of Lemma 11 | — | out of scope | no |
| Proposition 13 | `prop:periodic` | Prop. 5.3 | periodic runs of period at most 6 | — | out of scope (computational) | no |
| Proposition 14 | `prop:littlewood` | Prop. 6.1 | Littlewood identity for the orbit of `1/2` | `littlewood` (with `orbit`, `orbit_eq`) | in scope | yes |
| Corollary 15 | `cor:noperiodic` | Cor. 6.3 | under a periodic run the orbit of a knot born at an `M` never returns to `1/2` | `no_return_to_half` — **hypothesis `p ∣ q` added explicitly** | in scope, **flagged** | yes, as amended; see flag (A) |
| Proposition 16 | `prop:kindyield` | Prop. 6.5 | `v` kind with `v_p = M` ⟹ `N λ = ∞` | `N_unbounded_of_kind` (with `Kind`, `births_period_succ`) | in scope | yes, with no extra hypothesis |
| Remark 17 | — | Remark 6.4 | `√2`, `3/2` not Littlewood roots | — | out of scope (computational) | no |
| — | — | — | itinerary counts `0,2,2,10,10,44,56,180,250`; `RM` sweep | — | out of scope (computational) | no |
| Proposition 18 | `prop:blocks` | Prop. 7.1 | composition of two branch maps at `λ = √2`; `RR`/`LL` preserve `{x<1/2}`/`{x>1/2}` and act as `2x`, `2x-1` | `Sqrt2.comp_branch`, `Sqrt2.survivesWord_RR`, `Sqrt2.survivesWord_LL`, `Sqrt2.posAfter_RR`, `Sqrt2.posAfter_LL` | in scope | yes |
| Proposition 19 | `prop:closed` | Prop. 7.2 | `b` doubles under a block; position after `n` blocks is `fract(2^(n-1) b √2)` | `Sqrt2.block_coords`, `Sqrt2.posAfter_blocks` — **needs `0 < x < 1` and `n ≥ 1`** | in scope, **flagged** | yes, as amended; see flag (E) |
| Definition 20 | — | — | `T(S)`, common binary prefix length | — | out of scope (clustering data) | no |
| Questions 21–27 | `q:kind`, … | — | open questions | — | out of scope | no |
| Appendix A | `app:verify` | — | verification notes, exhaustive depths 42 and 38, all `d(k)` tables | `d` is *defined* (`KnotGame.d`) but no claim about it is certified | out of scope (computational) | no — flag (F) |
| Appendix B | `app:phi` | — | golden-ratio transition table | `Golden.absSurv`, `Golden.absAct`, certified by `Golden.survives_p`, `Golden.act_p`, boundary equalities `Golden.p1_eq`, `Golden.p3_eq` | in scope | yes |

Work Order 1 (the definitions) has no paper number of its own; it is
`RequestProject/Basic.lean`: `Move`, `r`, `g`, `deleted`, `volume_deleted`,
`survives`, `survives_iff_not_mem_deleted`, `f`, `branch`, `act`, `survivors`,
`step`, `runFrom`, `run`, `N`, `d`, `survivesWord`, `posAfter`, `births`.

## Flags

**(A) Corollary 15 / Cor. 6.3 — hypothesis not explicit in the paper.**
The paper's proof reads: "A return to `1/2` at time `q` makes the full state,
position together with phase, periodic, which forces `p ∣ q`; the move at time
`q` is then the move at phase `p`, namely `M`, contradicting Lemma 1." The step
"forces `p ∣ q`" is not proved and does not follow from Lemma 1 alone: Lemma 1
forbids a *surviving* knot from being carried to `1/2` by `M`, but says nothing
about the moves `L` and `R`, and under `L` the point `1 - r/2` *is* carried to
`1/2` (at `λ = φ` this is exactly the transition `p₄ ↦ p₃` of the Appendix B
table). So a return to `1/2` at a time `q` with `p ∤ q` is not excluded by the
cited lemma, and the corollary as literally stated is not a consequence of the
material the paper supplies. Following constraint 3 (report, do not repair) the
missing step is carried as an explicit hypothesis `hpq : p ∣ q` in
`no_return_to_half`, and flagged here rather than being quietly assumed.

**(B) Numbering.** The commission's `section.index` labels do not match the
compiled numbering of the PDF, which is sequential over a single counter. The
table above gives the correspondence. No mathematical content is affected.

**(C) Proposition 9 / Prop. 3.4 — negative report in round 1, certified in
round 6.** The round-1 report (`PLASTIC-REPORT.md`) recorded that the
kernel-checked closure computation at the required size did not terminate in
reasonable time, `native_decide` being forbidden by constraint 1; its cost
measurements stand for the route they measured. Round 6 certifies all four
clauses by shipping the breadth-first search *result* as checkable data instead
of replaying the search: see `PROP9-PLASTIC.md` and
`RequestProject/PlasticConfig.lean`, `RequestProject/PlasticOrbitCount.lean`.
The hypothesis of the proposition remains certified as before:
`Plastic.isPisot_rho` (the plastic number is Pisot) and hence
`Plastic.orb_rho_finite` (its orbit is finite, by Theorem 6).

**(D) Configurations are unconstrained `Finset ℝ`.** Work Order 1 asks for "a
`Finset ℝ` contained in the open interval". Carrying the containment inside the
type would leak a proof obligation into every statement, so `step`, `run` and
`N` are stated for an arbitrary `Finset ℝ` and the invariance of `(0,1)` is
proved separately as `posAfter_mem_Ioo` / `orb_subset_Ioo`. This is a
formalisation choice, not a change of content.

**(E) Proposition 19 / Prop. 7.2 — hypotheses not explicit in the paper.**
`posAfter_blocks` requires `0 < x < 1` and at least one block (`s ≠ []`, i.e.
`n ≥ 1`). Both are implicit in the paper: the formula `fract(2^(n-1) b √2)` is
false for `n = 0`, and a knot outside the open unit interval is not a knot. They
are stated explicitly rather than assumed.

**(F) `d(k)`.** `KnotGame.d k` is defined (Work Order 1 asks for it), but every
statement about its values is a table in Appendix A and hence out of scope. No
numerical claim about `d` is certified.

**(G) Corollary 7 / Cor. 3.2.** Deferred: no work order covers it, and only the
finiteness of the orbit (Theorem 6) is certified here, not the finiteness of the
set of reachable configurations or the eventual periodicity of `N`.

**(H) No unused hypotheses were found.** Per the commission's hazard note, the
earlier draft's eventual-periodicity hypothesis on Proposition 16 is absent:
`N_unbounded_of_kind` assumes only kindness, periodicity, and `v_p = M`.
