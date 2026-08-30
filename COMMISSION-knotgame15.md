# COMMISSION: knotgame round 15 — closing the round-14 hypotheses (T43–T45)

## OPERATING RULES — read first

The tree in this tarball is GREEN under continuous integration. Verifying the
whole tree is NOT your job.

1. FIRST COMMAND: `lake exe cache get`. A progress report of the form
   "8125 of 8145" means you are compiling Mathlib from source and have not
   started on this project.
2. NEVER a bare `lake build`. Build only the modules you author, one at a
   time: `lake build RequestProject.<YourModule>`.
3. NEVER a tree-wide axiom audit. `#print axioms` on YOUR OWN theorems only.
4. If one of your modules takes more than ~10 minutes to elaborate, stop and
   report it; do not retry in a loop.
5. `RequestProject` is built by directory glob — anything you leave in that
   directory is compiled. Do not leave scratch files there.
6. Do not attempt anything listed in `UNBUILT.md`.
7. Deliver source plus documents. Do not build the union, do not push.
8. Every module you author must be imported by `RequestProject/All.lean` and
   named in the CI module list before you deliver. Round 14 found two of its
   four modules outside the import closure; the round that inherited them
   corrected it. Do not make that the next round's job.

Census-first; report rather than repair; no sorry/admit/new axiom/
native_decide; SCRUPLES for every convention or deviation. The textual gate
strips `--` comments, so prose may mention a forbidden token; code may not.

Read `STATE-OF-PLAY.md` before starting.

This round has one small task, one cheap task, and one substantial task with an
explicit stopping rule. Do them in that order. T43 and T44 are the round's
floor: if T45 stalls, T43 and T44 delivered clean is a successful round.

## T43 — make `const_eq_integral_of_invariant` dischargeable (small, first)

Round 14's `RequestProject/Contraction.lean` proves

```
const_eq_integral_of_invariant :
  ... (hint : ∀ m, Integrable ((P lam)^[m] h) nu)
      (hinv : ∀ m, ∫ y, ((P lam)^[m] h) y ∂nu = ∫ y, h y ∂nu) → ∫ y, h y ∂nu = c
```

Both hypotheses are in a shape that a construction of an invariant measure does
not produce, so as it stands T45 would have to rebuild them before it could use
the theorem. Fix that here, in `Contraction.lean` itself:

(a) **Delete `hint`.** It is derivable, not assumable: `lipBound_iterate` gives
    `LipBound ((r lam)^m * K) ((P lam)^[m] h)`, so each iterate is Lipschitz,
    hence measurable, and bounded on `Icc 0 1`; with `nu` a probability measure
    and `nu (Icc 0 1)ᶜ = 0`, integrability follows. Prove it as a lemma and use
    it.

(b) **Replace `hinv` by one-step invariance quantified over test functions.**
    The hypothesis a construction supplies is
    `∀ φ : ℝ → ℝ, (regularity on φ) → ∫ y, P lam φ y ∂nu = ∫ y, φ y ∂nu`,
    for `φ` ranging over a class closed under `P` — Lipschitz, or bounded
    measurable, your choice, but state which and say why in SCRUPLES. Derive
    the `m`-fold form by induction inside the module (the induction applies
    invariance to `P^[m-1] h`, not to `h`, which is why the quantifier is
    needed), and keep the conclusion as it is.

Keep the old statement as a corollary if that is cheaper than rewriting call
sites; `EquiMean.equidistribution_in_mean` must still compile unchanged in
substance.

## T44 — the converse inclusion (cheap)

The paper's §10.2 now argues, and round 15 should certify, that forbidding `M`
loses no endpoint. In `RequestProject/BackwardClosure.lean` vocabulary:

```
kindDense_imp_denseFrom_half : 1 < lam → KindDense lam → DenseFrom lam (1/2)
```

The step lemma is `survives lam m x → branchLegal lam (branch lam m x) x`, by
cases on the move: `L` and `R` are the identical predicates already used by
`survives_toMove`, and for `M` survival puts `x` in `(0, r/2) ∪ (1 - r/2, 1)`,
where `r/2 < r` and `1 - r/2 > g` make both branches legal. Note that this
direction needs `0 < r`, hence `1 < lam`, unlike
`denseFrom_half_imp_kindDense`, which needs no hypothesis on `lam` — say so in
SCRUPLES. `act lam m x = f lam (branch lam m x) x` holds definitionally;
`Pisot.posAfter_eq_branchIter` and `BranchBridge.rapp_eq_branchIter` supply the
endpoint half.

With T44 the two density hypotheses are equivalent and the paper's claim that
the two-letter analysis is the whole of the spreading problem rests on a
certified biconditional rather than on one inclusion plus an argument.

## T45 — exhibit a measure satisfying the invariance hypothesis (substantial)

The target is NOT "construct the Bernoulli convolution and develop its theory".
It is exactly this: produce a probability measure `nu` on `ℝ` with
`nu (Icc 0 1)ᶜ = 0` satisfying the invariance hypothesis of T43(b), and
thereby discharge that hypothesis in `Contraction.const_eq_integral_of_invariant`
and in `EquiMean.equidistribution_in_mean`. Deliver it in a new module; do not
edit round 14's statements beyond what T43 requires.

Census first: the project has no invariant measure anywhere, and
`FourierFloor.lean` records in its own scruples that `ν_r` is not constructed.

Suggested route, to be confirmed or rejected by your census of Mathlib:

* Take the Bernoulli(1/2) product measure on `ℕ → Fin 2`. Establish what
  Mathlib actually provides for countable products of probability measures at
  this toolchain (`Measure.infinitePi`, `Measure.productMeasure`, or whatever
  the current name is) BEFORE building on it.
* Push it forward under `bval : (ℕ → Fin 2) → ℝ`,
  `bval ε = (1 - r) * ∑' j, ε j * r ^ j`. `Trapezoid.lean` already has a `bval`
  and its summability lemmas at `λ = √2`; this is the same series in general.
* Invariance is the shift identity `bval ε = r * bval (σ ε) + (1 - r) * ε 0`
  together with the factorisation of the product measure into the first
  coordinate and the shift. That is where the work is.

**Stopping rule.** If the product-measure layer you need is not in Mathlib at
this toolchain, or if the invariance argument is turning into a module of its
own several hundred lines long, STOP and report what is missing, with the
precise names you looked for and what they would have to provide. A clean
report that T45 is a round-sized project on its own is a successful outcome;
an approximation of it is not. Do not substitute a measure that satisfies the
hypothesis vacuously or by construction-from-the-conclusion, and do not weaken
the invariance hypothesis to something the tree can already prove.

## Explicitly NOT commissioned

The pointwise upgrade at `x = 1/2` (paper Question 50) — unproved on paper, and
the Lasota–Yorke route is closed for the reason given there. No weakened
variant. Sharpness of the contraction constant in `prop:gap` (the paper claims
it, attained at `h(y) = y`; the appendix records that only the inequality is
certified — leave it that way unless T43 makes it free). Everything in
`UNBUILT.md`; two-step exhaustiveness; `d_{3/2}(7) = 52` and
`d_{3/2}(8) ≥ 57`.

## Note on where this runs

Round 15 is to be run by a prover with a working Lean toolchain and Mathlib
cache. A session without one should NOT write these modules and report them
done — see working rule 7 and the files in `UNBUILT.md` that were reported
complete without ever being elaborated. A session without a toolchain should
deliver census and design decisions only, and say so.

## Deliverables

`CENSUS-round15.md`; sources; `#print axioms` for your own theorems in
`AXIOM-AUDIT-round15.md`; `SCRUPLES-round15.md` — in particular: which
regularity class the T43(b) invariance hypothesis quantifies over and why, the
`1 < lam` asymmetry between the two directions in T44, and, for T45, either the
construction's conventions or the stopping report; a round-15 section for
`GITHUB_HANDOFF_CHECKLIST`. Do not modify `knotgame.tex`.
