# Summary of changes for run c1c40e35-9e72-4e68-b832-2f9a24d346de
Round 17 of the knot-game commission is delivered. The supplied archive was unpacked into the project root (the commission document is kept alongside it as `COMMISSION-knotgame17.md`), and one new module, `RequestProject/Closures17.lean` (namespace `KnotGame.Closures17`, 230 lines), was written. It builds cleanly with no `sorry`, no `admit`, no added `axiom`, no `@[implemented_by]`, no `decide` and no `native_decide`.

**T47 — no contracting weight exists.** `no_contracting_weight`: for `1 < lam < 2`, no `w : ℝ → ℝ` with `1 ≤ w` on `(0,1)` satisfies `w (act lam m x) ≤ θ · w x` for every `x ∈ (0,1)` and every move `m` legal at `x`, with a fixed `θ < 1`. The route: `g lam < r lam` exactly when `lam < 2` (`g_lt_r`), so the moves `R` and `L` between them are legal everywhere on `(0,1)`; an explicit infinite legal orbit is built as a plain recursion (no choice function), the inherited `act_mem_Ioo` keeps it inside `(0,1)`, and the weight would decay below its own lower bound. Negative `θ` is disposed of in one step.

**T48 — sharpness of the contraction constant.** `P_id`: `P lam id = fun y => r lam * y + (1 - r lam)/2`, with no hypothesis on `lam`. `dist_P_id`: `dist (P lam id y) (P lam id z) = r lam * dist y z`, an equality, so the factor `r lam` of the inherited Lipschitz contraction theorem is attained; `not_lipschitzWith_P_id` states this negatively for any `K < r lam`.

**T49 — the density criterion fails at every Pisot parameter.** `not_kindDense_of_orb_finite` (no hypothesis on `lam`) refutes `KindDense` from finiteness of `Orb lam`, by pigeonhole on `|Orb| + 1` disjoint subintervals of `(0,1)`; `not_denseFrom_half_of_finite` transports this to the branch-word form `DenseFrom lam (1/2)`; `not_kindDense_of_isPisot` and `not_denseFrom_half_of_isPisot` compose with `orb_finite`.

**Census findings.** `act_mem_Ioo` already existed in the expected shape and is reused verbatim; the one-letter "some move is legal at `x`" fact did not exist and is proved here in three lines. `Orb lam` and the endpoint set of `KindDense lam` are literally the same data (both `survivesWord`/`posAfter` from `1/2`), so the bridge is `Iff.rfl` and no definition was duplicated; only the bridge to the branch-word form was needed, and the inherited `denseFrom_half_imp_kindDense` supplies it — which is why `1 < lam` is dropped from the T49 statements.

**Audit and constraints.** `#print axioms` for all twelve declarations of the module reports `[propext, Classical.choice, Quot.sound]`; the transcript is `AXIOM-AUDIT-round17.md`, produced in a scratch file kept outside `RequestProject/` and removed afterwards. No inherited module was edited, so no importer needed rebuilding; only `RequestProject.Closures17` was built (with its dependencies), never the union, and no tree-wide audit was run. No scratch files were left in `RequestProject/`.

**Caveats.** The failure of the density criterion at a Pisot parameter is the failure of a *sufficient* condition for unboundedness and is not evidence for boundedness (that is the separate inherited `PisotDecide.N_le_card_orb`). T47 says nothing for `lam ≥ 2`, and its hypothesis `1 ≤ w` is what makes it false rather than merely useless. Nothing here touches Question 50, `nu`, or `N lam` at non-Pisot parameters.

**Documents.** `CENSUS-round17.md`, `SCRUPLES-round17.md`, `AXIOM-AUDIT-round17.md`, a round-17 section `14D` in `GITHUB_HANDOFF_CHECKLIST` (including the appendix edit that T48 makes due — the paper's "sharpness remains unformalised" line should now come out), a row in `README.md`, an addendum in `STATE-OF-PLAY.md`, and a fresh run summary in `ARISTOTLE_SUMMARY.md`. The module is imported by `RequestProject/All.lean` and named in the CI module list. All work is committed and pushed.

# Summary of changes — round 17 (T47, T48, T49)

Round 17 is delivered. The archive supplied with the request has been unpacked
into the project root, so the tree is now the working project, with
`COMMISSION-knotgame17.md` kept alongside it. (This file previously carried the
round-16 summary; that round's record is in `CENSUS-round16.md`,
`SCRUPLES-round16.md` and `AXIOM-AUDIT-round16.md`.)

## What was built

One new module, `RequestProject/Closures17.lean` (namespace
`KnotGame.Closures17`, 230 lines), imported by `RequestProject/All.lean` and
added to the CI module list. **No inherited module was edited**, so operating
rule 9 was not triggered; the only targeted build required was
`lake build RequestProject.Closures17`, which succeeds with no warnings arising
from the module. `RequestProject.All` was not built.

* **T47** `no_contracting_weight` — for `1 < lam < 2`, no weight `w` with
  `1 ≤ w` on `(0,1)` contracts by a fixed factor `< 1` along every legal move.
  The mechanism is `g lam < r lam` (equivalent to `lam < 2`), so the moves `R`
  and `L` between them are legal at every point of `(0,1)`; an explicit
  infinite legal orbit is built (a plain recursion, not a choice function), the
  inherited `Pisot.act_mem_Ioo` keeps it inside `(0,1)`, and the weight would
  decay below its own lower bound along it.
* **T48** `P_id` — `Contraction.P lam id = fun y => r lam * y + (1 - r lam)/2`,
  with no hypothesis on `lam`; `dist_P_id` — the operator scales distances at
  the identity by exactly `r lam`; `not_lipschitzWith_P_id` — hence it is not
  `LipschitzWith K` for any `K < r lam`. The contraction factor of
  `Contraction.lipschitz_contraction` is therefore best possible.
* **T49** `not_kindDense_of_orb_finite`, `not_denseFrom_half_of_finite`,
  `not_kindDense_of_isPisot`, `not_denseFrom_half_of_isPisot` — the density
  criterion of §10 fails at every Pisot parameter, `Orb lam` being finite there
  and a finite set not dense in `(0,1)`.

## Census findings worth recording

`Pisot.act_mem_Ioo` already existed in the shape the commission expected and is
reused verbatim; the one-letter fact "some move is legal at `x`" did not exist
and is proved here in three lines. `Orb lam` and the endpoint set of
`KindDense lam` turned out to be *literally the same data* — both are stated
through `survivesWord` and `posAfter` from `1/2` — so `mem_orb_iff` is
`Iff.rfl` and no definition was duplicated; the only real bridge needed was to
the branch-word form `DenseFrom`, and the inherited
`denseFrom_half_imp_kindDense` supplies it. `1 < lam` is consequently dropped
from the T49 statements, since the direction of round 15's equivalence that is
used carries no hypothesis on `lam`.

## Audit

`#print axioms` for all twelve declarations of the module, elaborated in a
scratch file outside `RequestProject/` and since removed, reports
`[propext, Classical.choice, Quot.sound]` in every case; the transcript is
`AXIOM-AUDIT-round17.md`. No `sorry`, `admit`, added `axiom`,
`@[implemented_by]`, `native_decide` or `decide` in the round's source.

## Caveats, stated plainly

The failure of the density criterion at a Pisot parameter is the failure of a
*sufficient* condition for unboundedness; it is not evidence for boundedness,
which is the separate inherited `PisotDecide.N_le_card_orb`. T47 is stated for
`1 < lam < 2` and nothing is claimed for `lam ≥ 2`; its hypothesis `1 ≤ w` is
what makes it false rather than merely useless, since with `inf w = 0` a
contracting weight exists trivially. The paper's remark that the collective
Lyapunov condition collapses to the pointwise one is not formalised. Nothing in
this round touches Question 50, `nu`, or `N lam` at non-Pisot parameters.

## Documents

`CENSUS-round17.md`, `SCRUPLES-round17.md`, `AXIOM-AUDIT-round17.md`, a round-17
section (`14D`) in `GITHUB_HANDOFF_CHECKLIST` — including the appendix edit that
T48 makes due — a row in `README.md`, and an addendum in `STATE-OF-PLAY.md`.
