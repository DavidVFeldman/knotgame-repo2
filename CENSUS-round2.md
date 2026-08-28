# Round 2 — census and target map

*Order, gaps, and the scheduling bound.*  Census first, as the commission
requires: what the round-1 tree already proves, what of it is reusable for the
round-2 targets, and where each target ends up.

Round-1 material is used **as is**.  No round-1 definition was changed and no
round-1 statement was re-derived.

## Part 1 — audit of the round-1 tree against the round-2 targets

| Round-2 target | Round-1 material found | Usable? | Action |
|---|---|---|---|
| T1 order | `KnotGame.straddle` (`Distinct.lean`): `x < r/2`, `y > 1-r/2` ⟹ `λx < λy-(λ-1)`; `act_M_of_lt`, `act_M_of_gt`, `r_lt_one` | yes, as the `M` case | reused; T1 proved on top of it |
| T2 gap law | the same three `act_M_*` equations | yes | reused; T2 is pure case analysis |
| T3 one service per move | nothing | — | proved fresh (`straddles_unique`) |
| T4 birth spacing | **nothing.**  The commission expected `d ≥ 2k-1` and `d(k+1) ≥ d(k)+2` from round 1.  They are not there.  `KnotGame.d` is *defined* in `Basic.lean`, but round 1's own census records (flag (F)) that no claim about its values is certified.  The nearest relative is `Threshold.births_le_one`, which is the special case `2 ≤ λ` and does not generalise. | no | proved fresh (`birth_head_ne_M`, `two_mul_births_le_length_succ`, `births_le_ceil_half`) |
| T5 scheduling | `card_runFrom` (`Suffix.lean`) — the suffix decomposition, which supplies exactly the window bookkeeping: knots at the end of `a ++ b` = survivors of `run a` along `b`, plus `births b`.  `act_injOn` (`Distinct.lean`), `act_mem_Ioo` (`Pisot.lean`). | yes, decisive | reused; the window split is `card_runFrom` applied at `w = a ++ b` |
| T6 golden ratio | `Golden.run_eq` (every configuration is `p '' T` for `T` a subset of the five orbit points), `Golden.p`, `phi_sq`, `phi_gt`, `phi_lt` | yes | reused verbatim |
| T7 plastic | `Plastic.rho`, `rho_cubic`, `rho_gt`, `rho_lt`, `isPisot_rho`, `orb_rho_finite`; and the negative report `PLASTIC-REPORT.md` on the *configuration* closure | partly | the 153-point *orbit* closure is certified here; see the round-2 addendum in `PLASTIC-REPORT.md` |

Two findings worth a reviewer's eye:

**(R2-a) T4's premise is wrong about round 1.**  The commission says "Round 1
certified `d ≥ 2k-1` and `d(k+1) ≥ d(k)+2` (or close variants)".  It did not.
Round 1's census flags this explicitly under (F): `d` is defined but nothing is
proved about it, because every statement about its values sits in the paper's
Appendix A and was ruled out of scope as computational.  T4 is therefore proved
from scratch here, in the form the scheduling argument actually consumes
(a bound on `births` of a word, not on `d`).

**(R2-b) T7 is not infeasible.**  The commission offered an infeasibility report
as an acceptable outcome, on the strength of round 1's finding that the 25 525
reachable *configurations* are out of reach for the kernel.  That finding stands
unchanged.  But the scheduling route needs only the 153-point *orbit* and one
gap, which is four orders of magnitude smaller, and it does close.  T7 is
certified.  See the round-2 addendum to `PLASTIC-REPORT.md`.

## Part 2 — the round-2 targets

All identifiers are in the `KnotGame` namespace.  Everything below is proved,
sorry-free, and inside the semantic axiom audit.

| Target | Statement | Lean identifier | File | Status |
|---|---|---|---|---|
| T1 | each move is strictly order preserving on its survivors | `act_lt_act` | `Gaps.lean` | proved |
| T2 | `image c y - image c x = λ(y-x)`, or `λ(y-x)-(λ-1)` for a pair straddling an `M` | `gap_law` (with `Straddles`) | `Gaps.lean` | proved |
| T3 | at most one consecutive pair straddles a given move | `straddles_unique`, `straddles_at_most_one` | `Gaps.lean` | proved |
| T4 | a knot born at `1/2` dies if the next move is `M`; hence at most `⌈n/2⌉ ` surviving births in a word of length `n` | `birth_head_ne_M`, `two_mul_births_le_length_succ`, `births_le_ceil_half` | `Gaps.lean` | proved |
| T5 | `k ≤ W + ⌈W/2⌉ + 1` | `scheduling_bound`, and `N_le_of_separated` for `N` | `Gaps.lean` | proved |
| T6 | `N_φ ≤ 9`, via `φ⁵(φ-3/2) = φ²/2 ≥ 1` | `Golden.N_phi_le_nine`, `Golden.card_run_phi_le_nine`, `Golden.phi_pow_five_mul_delta0` | `GoldenEffective.lean` | proved |
| T7 | `N_ρ ≤ 34`, via the 153-point orbit and gap `≥ 239/100000` | `Plastic.N_rho_le_34`, `Plastic.card_run_rho_le_34`, `Plastic.run_subset_OrbSet`, `Plastic.run_sep` | `PlasticOrbit.lean` | proved |

Supporting results introduced along the way, also in `Gaps.lean`:

| Identifier | Statement |
|---|---|
| `card_le_length_succ` | the combinatorial core of T5: a set of knots in `(0,1)` all surviving a word `b`, pairwise so far apart that `λ^{|b|}` times their distance is `≥ 1`, has at most `|b| + 1` elements |
| `run_subset_Ioo` | every knot of every reachable configuration lies in `(0,1)` |
| `run_subset` | invariance principle: a set containing `1/2` and closed under `act` on its survivors contains every knot of every reachable configuration |
| `runFrom_append` | `runFrom S (u ++ v) = runFrom (runFrom S u) v` |
| `near_collision` | the paper's corollary in the other direction: a run reaching `k` knots with `3m + 4 < 2k` has a moment at which two distinct coexisting knots lie within `(λ^m)⁻¹` |

## Part 3 — how the formalisation reads the paper

**The window.**  The paper's proof fixes a run of length `n`, looks at the last
`W` moves and splits the knots into *old* (age `≥ W`) and *young*.  Formally the
run is split as a word, `w = a ++ b` with `|b| = W`, and `card_runFrom` does the
splitting: the knots at the end are the survivors of `run a` along `b`
(the old knots — those alive throughout the window) together with `births b`
(the young ones — those born inside the window).  No age function is needed.

**Old knots: `card_le_length_succ`.**  The paper argues by pigeonhole: each
consecutive old pair must straddle some move of the window (T2 plus
`λ^W δ ≥ 1` plus "distances stay below 1"), each move serves at most one pair
(T3), so there are at most `W` pairs.  The formalisation runs the same argument
as an induction on the window word.  After one move either no pair straddles,
in which case every distance is multiplied by `λ` and the induction hypothesis
applies to the whole image; or one pair does, in which case deleting the largest
knot lying below the deleted interval restores the hypothesis for the image
(the deleted point's left neighbours inherit the bound through it, by T1 and
`straddle`) and drops the count by one.  This is the pigeonhole with the
injection built into the recursion, and it needs no ordering of the
configuration and no indexing of the moves.

**Young knots: T4.**  `births` counts positions carrying `M` whose suffix keeps
`1/2` alive; two such positions are never adjacent, because `1/2` lies strictly
inside the interval deleted by `M` for every `λ > 1`.  A word of length `n`
therefore carries at most `⌈n/2⌉` of them.

**Hypotheses.**  `scheduling_bound` asks for the separation at every prefix of
the run (the paper's "throughout the run") and for `1 ≤ λ^W δ`.  The paper's
`δ > 0` is *not* carried as a separate hypothesis: it follows from
`1 ≤ λ^W δ`, and the commission's SCRUPLES rule forbids stating more than is
used.  The paper defines `W = ⌈log_λ(1/δ)⌉`; the formalisation takes `W` as
given with `1 ≤ λ^W δ`, which is the same condition without the logarithm, and
is what both corollaries supply directly.

**`⌈W/2⌉`.**  Written `(W + 1) / 2` in natural-number division.

## Part 4 — consistency remarks required by the commission

* **T6 versus round 1.**  Round 1 certified the sharp value `sup N φ = 2`
  (`Golden.sup_N_phi`).  T6 certifies `N φ n ≤ 9`.  The second is strictly
  weaker and strictly independent: it uses the five orbit points and their
  minimum gap, and never inspects the twelve reachable configurations.  Both
  statements stand; there is no conflict.
* **T7 versus the paper.**  The paper reports the true value `sup N ρ = 7` and
  the bound `34` from this argument.  Only the bound `34` is certified here;
  `7` is certified neither here nor in round 1.
* **T7 versus `PLASTIC-REPORT.md`.**  The round-1 negative report concerns the
  25 525-configuration closure and is unaffected.
