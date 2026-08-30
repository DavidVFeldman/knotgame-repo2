# Summary of changes for run b1c5b5f7-ea7d-49b4-8973-8865eae9af46
Round 16 (T46, the Pisot separation bound) is delivered, and the archive that was supplied has been unpacked into the project root so the tree is now the working project (with `COMMISSION-knotgame16.md` kept alongside it).

**New module: `RequestProject/PisotSeparation.lean` (299 lines, builds cleanly, no `sorry`).**

- **T46(a) `orb_separated_of_conj_le`** — for `1 < lam` a root of a monic integer polynomial `p`, and `0 ≤ c < 1` bounding the moduli of the complex roots of `p` other than `lam`, distinct points `x, y` of `Orb lam` satisfy `1 / (2 * (2B)^(d-1)) ≤ |x - y|`, where `B = (2 + 2c)/(1 - c)` and `d = Module.finrank ℚ ℚ⟮lam⟯`. The constant mentions only `c` and `d` — never the orbit, the two points, or the branch words.
- **T46(b) `orb_ncard_le_of_conj_le`** — `(Orb lam).Finite` together with `(Orb lam).ncard ≤ ⌊2 * (2B)^(d-1)⌋₊ + 1`. Finiteness is re-derived from the separation estimate, so the earlier qualitative finiteness result is untouched and unused (no inherited module was edited, so no importer needed rebuilding).
- **`orb_separated`** — both results from `IsPisot lam` alone; `exists_conj_bound` supplies the uniform `c` from the finitely many roots of the witnessing polynomial.
- Supporting public results: `one_le_prod_norm_embeddings` (the product of the moduli of the complex embeddings of a nonzero algebraic integer is at least 1), `one_le_norm_mul_pow`, `finite_ncard_le_of_separated` (a δ-separated subset of `(0,1)` has at most `⌊1/δ⌋ + 1` elements), and `exists_iterC_eq_two_mul`.

**The commission's stopping rule was not reached.** The norm layer needed does exist at this toolchain and composes with the existing `IntermediateField` scaffolding: `Algebra.norm_eq_prod_embeddings`, `RingHom.equivRatAlgHom`, `Algebra.isIntegral_norm` with `IsIntegrallyClosed.isIntegral_iff`, `Algebra.norm_ne_zero_iff`, and `NumberField.Embeddings.card`. What was searched for, used, and examined-and-rejected (the infinite-place product formula, stated for the ring of integers and carrying multiplicities) is recorded in the census.

**Audit.** Every public declaration of the module reports `[propext, Classical.choice, Quot.sound]`; the transcript is in `AXIOM-AUDIT-round16.md`. No `sorry`, `admit`, added `axiom`, `@[implemented_by]`, `native_decide` or `decide` in the round's source. Only the new module was built, one target at a time; the union was not built.

**Caveats stated plainly.** Nothing about `N_λ` follows here — that step runs through the scheduling bound, which the commission excludes. The constant is uniform but weak (by hand, at the golden ratio it gives a cardinality bound of about 34); nothing in the sources evaluates it at a specific parameter, and that arithmetic is flagged in the scruples as hand computation, not a machine check.

**Documents and wiring.** `CENSUS-round16.md`, `SCRUPLES-round16.md` (shape of the constant, the degree convention, `Set.ncard`, and the slack in the bound), `AXIOM-AUDIT-round16.md`, a round-16 section `14C` in `GITHUB_HANDOFF_CHECKLIST`, a table row in `README.md`, an addendum in `STATE-OF-PLAY.md`, and a fresh run summary in `ARISTOTLE_SUMMARY.md`. The module is imported by `RequestProject/All.lean` and added to the CI module list. All work is committed and pushed.

# Summary of changes — round 16 (T46, the Pisot separation bound)

Round 16 is delivered. No whole-tree build was run and `RequestProject.All` was
not built. (This file previously carried the round-15 summary; that round's
record is in `CENSUS-round15.md`, `SCRUPLES-round15.md` and
`AXIOM-AUDIT-round15.md`.)

## What was built

One new module, `RequestProject/PisotSeparation.lean` (299 lines), imported by
`RequestProject/All.lean` and added to the CI module list. **No inherited
module was edited**, so operating rule 9 was not triggered and no importer
needed rebuilding; the only targeted build required was
`lake build RequestProject.PisotSeparation`, which succeeds with no warnings.

* **T46(a)** `orb_separated_of_conj_le` — for `1 < lam` a root of a monic
  integer polynomial `p`, and `0 ≤ c < 1` bounding the moduli of the complex
  roots of `p` other than `lam`, distinct `x, y ∈ Orb lam` satisfy
  `1 / (2 * (2B)^(d-1)) ≤ |x - y|` with `B = (2 + 2c)/(1 - c)` and
  `d = Module.finrank ℚ ℚ⟮lam⟯`.
* **T46(b)** `orb_ncard_le_of_conj_le` — `(Orb lam).Finite` together with
  `(Orb lam).ncard ≤ ⌊2 * (2B)^(d-1)⌋₊ + 1`. Finiteness is re-derived from the
  separation estimate, so `Pisot.orb_finite` is untouched and unused.
* `orb_separated` — both of the above from `IsPisot lam` alone, the uniform `c`
  being produced by `exists_conj_bound` from the finitely many roots.
* Supporting results of independent interest: `one_le_prod_norm_embeddings`
  (the product of the moduli of the complex embeddings of a nonzero algebraic
  integer is at least `1`), `one_le_norm_mul_pow`, and
  `finite_ncard_le_of_separated` (a `δ`-separated subset of `(0,1)` is finite
  with at most `⌊1/δ⌋ + 1` elements).

## The stopping rule was not reached

The commission allowed the round to stop and report if Mathlib's norm layer did
not compose with the `IntermediateField` scaffolding of `orb_finite`. It does:
`Algebra.norm_eq_prod_embeddings`, `RingHom.equivRatAlgHom`,
`Algebra.isIntegral_norm`, `IsIntegrallyClosed.isIntegral_iff`,
`Algebra.norm_ne_zero_iff` and `NumberField.Embeddings.card` are all available
at this toolchain and all apply to `K = ℚ⟮lam⟯`. `CENSUS-round16.md` §2 records
what was looked for, what was used, and what was examined and rejected.

## Audit

`#print axioms` for all eight public declarations of the module, elaborated in a
scratch file outside `RequestProject/` and since removed, reports
`[propext, Classical.choice, Quot.sound]` in every case; the transcript is
`AXIOM-AUDIT-round16.md`. No `sorry`, `admit`, added `axiom`,
`@[implemented_by]`, `native_decide` or `decide` in the round's source.

## Caveats, stated plainly

The constant is uniform in the sense required — it names only a bound on the
conjugate moduli and the degree, never the orbit, the points, or the branch
words — but it is weak: by hand, at the golden ratio it yields a cardinality
bound of about 34. Nothing in the sources evaluates it at any specific `lam`.
Nothing about `N_λ` follows here: the passage from separation to a bound on the
knot count runs through `thm:schedule`, which the commission excludes.

## Documents

`CENSUS-round16.md`, `SCRUPLES-round16.md`, `AXIOM-AUDIT-round16.md`, a round-16
section (`14C`) in `GITHUB_HANDOFF_CHECKLIST`, a row in `README.md`, and an
addendum in `STATE-OF-PLAY.md`.
