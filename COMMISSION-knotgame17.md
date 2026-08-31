# COMMISSION: knotgame round 17 — three small closures (T47–T49)

## OPERATING RULES — read first

The tree in this tarball is GREEN under continuous integration. Verifying the
whole tree is NOT your job.

1. FIRST COMMAND: `lake exe cache get`. A progress report of the form
   "8125 of 8145" means you are compiling Mathlib from source and have not
   started on this project.
2. NEVER a bare `lake build`. Build only the modules you author, one at a
   time: `lake build RequestProject.<YourModule>`. Never build
   `RequestProject.All`, which imports everything and is the tree build under
   another name.
3. NEVER a tree-wide axiom audit. `#print axioms` on YOUR OWN theorems only,
   elaborated in a scratch file kept outside `RequestProject/`.
4. If one of your modules takes more than ~10 minutes to elaborate, stop and
   report it; do not retry in a loop.
5. `RequestProject` is built by directory glob — anything you leave in that
   directory is compiled. Do not leave scratch files there.
6. Do not attempt anything listed in `UNBUILT.md`.
7. Deliver source plus documents. Do not build the union, do not push.
8. Every module you author must be imported by `RequestProject/All.lean` and
   named in the CI module list before you deliver.
9. If you edit an inherited module, build the modules that import it. Nothing
   in this round should require that.

Census-first; report rather than repair; no sorry/admit/new axiom/
native_decide; SCRUPLES for every convention or deviation. The textual gate
strips `--` comments, so prose may mention a forbidden token; code may not.

Read `STATE-OF-PLAY.md` before starting.

This is a small round: three independent statements, each short, none of which
depends on the others. One new module for all three is fine. Do them in the
order given; each is a complete deliverable on its own.

## T47 — no contracting weight exists

The paper will record that no Lyapunov-weight argument can bound the knot
count, at any parameter. The formal content is this. Every point of `(0,1)`
has a legal move that keeps it in `(0,1)` — because `g lam < r lam` for
`1 < lam < 2` — so from any starting point there is an infinite legal orbit.
A weight that contracts along every legal move by a fixed factor would
therefore decay to zero along that orbit, contradicting a positive lower bound.

```
no_contracting_weight :
  1 < lam → lam < 2 →
  ∀ (w : ℝ → ℝ) (θ : ℝ), θ < 1 →
    (∀ x ∈ Ioo 0 1, 1 ≤ w x) →
    ¬ (∀ x ∈ Ioo 0 1, ∀ m, survives lam m x → w (act lam m x) ≤ θ * w x)
```

Census first for the "every point has a legal move" fact; something of that
shape almost certainly exists already (the survivor counts are never zero, and
`K lam m x ≥ 1` or its branch-word cousin should be in the tree). If you build
the infinite orbit yourself, `Nat.rec` with the choice of a legal move at each
step is enough; do not reach for anything heavier. Note that `act lam m x ∈
Ioo 0 1` whenever `survives lam m x` and `x ∈ Ioo 0 1` — check whether that is
already a lemma before proving it.

State in SCRUPLES that the hypothesis `1 ≤ w x` is the reason the statement is
false rather than merely useless: with `inf w = 0` a contracting weight exists
trivially. The paper's remark that the *collective* condition collapses to this
pointwise one (single-knot configurations are reachable) is a paper remark and
is not commissioned.

## T48 — sharpness of the contraction constant

`Contraction.lipschitz_contraction` gives `LipschitzWith (r*K) (P lam h)` from
`LipschitzWith K h`. The paper claims the constant `r` is best possible,
attained at the identity, and the appendix records that this was not
certified. Certify it:

```
P_id : 1 < lam → P lam id = fun y => r lam * y + (1 - r lam)/2
```

together with whatever form of "hence `P lam id` is not `LipschitzWith K'` for
any `K' < r lam`" is cleanest — the equation itself is the content, and
`dist (P lam id y) (P lam id z) = r lam * dist y z` is a fine way to say it.
Keep it to a few lines; if it grows beyond that, something is being done the
hard way.

After this the appendix's "sharpness remains unformalised" can come out; note
in the handoff section that the paper needs that edit.

## T49 — the density criterion fails at every Pisot parameter

The paper's §10.2 now argues: `Orb lam` is finite at Pisot `lam`
(`Pisot.orb_finite`), a finite set is not dense in `(0,1)`, and the endpoint
sets of kind words and branch words coincide (`BackwardClosure.
denseFrom_half_iff_kindDense`), so the hypothesis of the density criterion
fails. Certify the chain:

```
not_denseFrom_half_of_finite : (Orb lam).Finite → ¬ DenseFrom lam (1/2)
not_kindDense_of_isPisot     : IsPisot lam → 1 < lam → ¬ KindDense lam
```

Check the exact relationship between `Orb lam` and the endpoint set in
`DenseFrom` before writing anything: `Orb` is defined in `Pisot.lean` and
`DenseFrom` in `BackwardClosure.lean`, and round 15's `BranchBridge` may or may
not already identify them. If they differ (e.g. one includes `1/2` itself, or
one is stated through `branchIter` and the other through `rapp`), bridge with
one lemma and say so in SCRUPLES rather than duplicating either definition.

The `1 < lam` hypothesis is inherited from the `iff`'s second direction; if the
direction you need is the one that does not use it, drop it and say so.

## Explicitly NOT commissioned

Question 50 in any form. Any statement about `N lam` being bounded at
non-Pisot parameters. Anything involving `nu` beyond what round 15 certified.
Everything in `UNBUILT.md`; two-step exhaustiveness; `d_{3/2}(7) = 52` and
`d_{3/2}(8) ≥ 57`.

## Note on where this runs

Round 17 is to be run by a prover with a working Lean toolchain and Mathlib
cache. A session without one should NOT write these modules and report them
done — see working rule 7 and the files in `UNBUILT.md` that were reported
complete without ever being elaborated. A session without a toolchain should
deliver census and design decisions only, and say so.

## Deliverables

`CENSUS-round17.md`; sources; `#print axioms` for your own theorems in
`AXIOM-AUDIT-round17.md`; `SCRUPLES-round17.md`; a round-17 section for
`GITHUB_HANDOFF_CHECKLIST`, including the appendix edit T48 makes due. There
is no `knotgame.tex` in this tarball and none should be added.
