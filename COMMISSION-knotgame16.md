# COMMISSION: knotgame round 16 — the Pisot separation bound (T46)

## OPERATING RULES — read first

The tree in this tarball is GREEN under continuous integration. Verifying the
whole tree is NOT your job.

1. FIRST COMMAND: `lake exe cache get`. A progress report of the form
   "8125 of 8145" means you are compiling Mathlib from source and have not
   started on this project.
2. NEVER a bare `lake build`. Build only the modules you author, one at a
   time: `lake build RequestProject.<YourModule>`. In particular never build
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

## The mathematics

`Pisot.orb_finite` proves that `Orb lam` is finite for Pisot `lam`, by a
lattice-discreteness argument. The result is qualitative: it gives no bound on
how many points there are, and none on how close two of them can be. Round 16
makes it quantitative, by a norm argument that the existing module has already
laid nearly all the groundwork for.

For distinct `x, y ∈ Orb lam`, the number `2*(x - y)` is a nonzero algebraic
integer of `ℤ[lam]`. Under the embedding of `ℚ(lam)` carrying `lam` to a
conjugate `z`, the doubled orbit is `iterC z w 1`, and `conj_bound` already
proves this is bounded in modulus by `(2 + 2‖z‖)/(1 - ‖z‖)`. So every conjugate
of `2*(x - y)` is at most twice that. The field norm of a nonzero algebraic
integer is a nonzero rational integer, so at least `1` in absolute value, and
it is the product of `2*(x - y)` with its `d - 1` conjugate values. Hence
`2*(x - y)` is bounded below, uniformly.

## T46(a) — the separation estimate

In a new module. With `c` a bound on the moduli of the conjugates and
`B = (2 + 2*c)/(1 - c)`, and `d` the degree:

```
orb_separated : IsPisot lam → x ∈ Orb lam → y ∈ Orb lam → x ≠ y →
  1 / (2 * (2*B)^(d-1)) ≤ |x - y|
```

The exact shape of the constant is yours to choose — a product over the
conjugates rather than a power of the maximum is sharper and may be easier or
harder depending on how the norm is expressed; either is acceptable, but state
in SCRUPLES which you took and why. What must not happen is a constant that
depends on the orbit, on `x` and `y`, or on the length of the branch words.

Census first. The pieces you need that already exist in `Pisot.lean`:
`IsPisot`, `Orb`, `iterC`, `two_mul_branchIter`, `map_iterC`,
`isIntegral_iterC`, `conj_bound`, and the number-field scaffolding inside
`orb_finite` (`ℚ⟮lam⟯`, `NumberField`, the embedding `co`). Reuse them; do not
rebuild them. The piece that is NOT in the tree is the norm step: an element of
the ring of integers of a number field is nonzero exactly when its norm is,
and the norm is a rational integer, so its absolute value is at least one. Find
what Mathlib provides here before writing anything — the relevant names to look
for concern `Algebra.norm`, its integrality on `𝓞 K`, and its expression as a
product over the complex embeddings.

**Stopping rule.** If Mathlib does not provide the norm-as-product-over-
embeddings in a form that composes with the `IntermediateField` scaffolding
`orb_finite` already uses, STOP and report, naming precisely what you looked
for and what it would have to say. A clean report that the norm step needs a
module of its own is a successful outcome. Do not substitute an estimate that
depends on the word length, and do not weaken the statement to a fixed `lam`
without saying so prominently.

## T46(b) — the cardinality bound

```
orb_card_le : IsPisot lam → (Orb lam).Finite ∧ card bound in terms of the same constant
```

A `δ`-separated subset of `Ioo 0 1` has at most `1/δ + 1` elements. This
strengthens `orb_finite` from a finiteness statement to an explicit count, and
it is the point of the round: the paper's table records `|Orb(λ)|` as `5`, `7`,
`43`, `153` at four parameters with no general bound behind those numbers.

Whether to restate `orb_finite` in terms of T46(b) or leave it standing beside
the new result is yours; if you restate it, rule 9 applies.

## Explicitly NOT commissioned

The passage from separation to a bound on `N_λ`. The scheduling bound of the
paper (`thm:schedule`) is what makes that step, and it is not formalised in the
shape T46 would need; the paper draws the consequence, and this round does not.

The pointwise upgrade at `x = 1/2` (paper Question 50). Sharpness of the
contraction constant in `prop:gap`. Any regularity of the measure built in
round 15 — density, singularity, Fourier decay, the Pisot dichotomy — none of
which this round touches despite the shared vocabulary. Everything in
`UNBUILT.md`; two-step exhaustiveness; `d_{3/2}(7) = 52` and
`d_{3/2}(8) ≥ 57`.

## Note on where this runs

Round 16 is to be run by a prover with a working Lean toolchain and Mathlib
cache. A session without one should NOT write these modules and report them
done — see working rule 7 and the files in `UNBUILT.md` that were reported
complete without ever being elaborated. A session without a toolchain should
deliver census and design decisions only, and say so.

## Deliverables

`CENSUS-round16.md`; sources; `#print axioms` for your own theorems in
`AXIOM-AUDIT-round16.md`; `SCRUPLES-round16.md` — in particular the shape of
the constant, anything assumed about the degree, and any place where the
statement is narrower than the prose above; a round-16 section for
`GITHUB_HANDOFF_CHECKLIST`. There is no `knotgame.tex` in this tarball and none
should be added.
