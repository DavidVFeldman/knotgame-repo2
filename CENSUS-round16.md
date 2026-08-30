# CENSUS — round 16 (T46)

Census first, as the commission requires: what was in the tree when round 16 was
picked up, what Mathlib provides for the one step the tree did not have, and
what round 16 adds.

## 1. Inherited and reused

Everything round 16 needs about the game side was already in
`RequestProject/Pisot.lean`; nothing there was edited, so operating rule 9 is
not triggered.

| Inherited identifier | Module | Used by round 16 for |
| --- | --- | --- |
| `KnotGame.IsPisot` | `Pisot` | the hypothesis of the top-level statement |
| `KnotGame.Orb` | `Pisot` | the set being separated and counted |
| `KnotGame.orb_subset`, `orb_subset_Ioo` | `Pisot` | orbit points are branch-word images of `1/2` inside `(0,1)` |
| `KnotGame.iterC`, `two_mul_branchIter`, `map_iterC`, `isIntegral_iterC` | `Pisot` | the doubled orbit as an algebraic integer, and its image under any ring map |
| `KnotGame.conj_bound` | `Pisot` | `‖iterC z w 1‖ ≤ (2 + 2‖z‖)/(1 − ‖z‖)` for `‖z‖ < 1` |
| the number-field scaffolding of `orb_finite` (`ℚ⟮lam⟯`, `IntermediateField.adjoin.finiteDimensional`, `NumberField`, the embedding `IntermediateField.val`) | `Pisot` | the same field `K = ℚ⟮lam⟯` and the same distinguished real embedding |

`orb_finite` itself is **not** used by round 16 and is left standing: the
finiteness half of T46(b) is re-derived from the separation estimate, so the new
result does not depend on the old one. Nothing else in the tree separates or
counts orbit points; a search for `orb_separated`, `orb_ncard`, and for any
statement bounding `|x − y|` for `x, y ∈ Orb` found nothing.

## 2. The step that was not in the tree: the norm

The commission's stopping rule concerns the norm step. It is **not** reached:
Mathlib at this toolchain (`v4.28.0`) provides everything needed, and it
composes with the `IntermediateField` scaffolding `orb_finite` already uses,
because that scaffolding produces an honest `NumberField K` instance for
`K = ℚ⟮lam⟯` and all four lemmas below are stated for an arbitrary number field.

Looked for, and found:

* `Algebra.norm_eq_prod_embeddings (K := ℚ) (E := ℂ)` —
  `algebraMap ℚ ℂ (Algebra.norm ℚ x) = ∏ σ : K →ₐ[ℚ] ℂ, σ x`, for
  `FiniteDimensional ℚ K`, `Algebra.IsSeparable ℚ K` and `IsAlgClosed ℂ`; all
  three are instances here (separability is free in characteristic zero).
  This is the norm-as-product-over-embeddings the commission asks about.
* `RingHom.equivRatAlgHom : (K →+* ℂ) ≃ (K →ₐ[ℚ] ℂ)` — needed because the
  project's `conj_bound` is stated for ring homomorphisms, while
  `norm_eq_prod_embeddings` indexes over `ℚ`-algebra homomorphisms. The two
  products are transported by `Fintype.prod_equiv`.
* `Algebra.isIntegral_norm ℚ : IsIntegral ℤ x → IsIntegral ℤ (Algebra.norm ℚ x)`
  and `IsIntegrallyClosed.isIntegral_iff` — together: the norm of an algebraic
  integer of `K` is a rational number integral over `ℤ`, hence of the form
  `(n : ℚ)` with `n : ℤ`.
* `Algebra.norm_ne_zero_iff` — the norm of a nonzero element is nonzero; with
  `Int.one_le_abs` this gives `1 ≤ |n|`.
* `NumberField.Embeddings.card K ℂ : Fintype.card (K →+* ℂ) = Module.finrank ℚ K`
  — this is what turns "product over the embeddings" into a power of the degree.

Also examined and **not** used: `NumberField.InfinitePlace.prod_eq_abs_norm`
(the product formula over infinite places, with multiplicities) and
`NumberField.InfinitePlace.one_le_of_lt_one`. Both are stated for elements of
the ring of integers `𝓞 K`; the objects here arrive as elements of `K`
carrying an `IsIntegral ℤ` hypothesis (that is the form `isIntegral_iterC`
produces), and places carry the extra bookkeeping of `mult w`, which the
argument does not need. Working directly with the `Fintype (K →+* ℂ)` of
complex embeddings keeps the statement in the same vocabulary as `conj_bound`.

Searched for and **not** found, hence proved here: any statement of the form
"the product of the moduli of the complex embeddings of a nonzero algebraic
integer is at least one" (`one_le_prod_norm_embeddings` below), and any
statement bounding the cardinality of a `δ`-separated subset of an interval
(`finite_ncard_le_of_separated` below).

## 3. What round 16 adds

One new module, `RequestProject/PisotSeparation.lean` (299 lines), imported by
`RequestProject/All.lean` and added to the CI module list.

| New identifier | Statement |
| --- | --- |
| `one_le_prod_norm_embeddings` | for `a ≠ 0` in a number field `K`, integral over `ℤ`: `1 ≤ ∏ ψ : K →+* ℂ, ‖ψ a‖` |
| `one_le_norm_mul_pow` | if moreover `‖ψ a‖ ≤ C` for every embedding, then `1 ≤ ‖φ a‖ * C ^ (finrank ℚ K − 1)` for any chosen embedding `φ` |
| `finite_ncard_le_of_separated` | a `δ`-separated subset of `(0,1)` is finite with at most `⌊1/δ⌋ + 1` elements |
| `exists_iterC_eq_two_mul` | every `x ∈ Orb lam` satisfies `iterC lam w 1 = 2x` for some branch word `w` |
| `orb_separated_of_conj_le` | **T46(a)**: distinct orbit points are at distance at least `1 / (2 * (2B)^(d−1))`, `B = (2 + 2c)/(1 − c)`, `d = [ℚ⟮lam⟯ : ℚ]` |
| `orb_ncard_le_of_conj_le` | **T46(b)**: `(Orb lam).Finite` and `(Orb lam).ncard ≤ ⌊2 * (2B)^(d−1)⌋ + 1` |
| `exists_conj_bound` | from `IsPisot lam`: a single `c` with `0 ≤ c < 1` bounding the moduli of all conjugate roots |
| `orb_separated` | the two above packaged from `IsPisot lam` alone, with `B` existentially quantified but fixed before `x` and `y` |

## 4. Not attempted

Everything the commission excludes: the passage from separation to a bound on
`N_λ` (which needs `thm:schedule`, not formalised in the shape required), the
pointwise upgrade at `x = 1/2`, the sharpness of the contraction constant, any
regularity of round 15's measure, everything in `UNBUILT.md`, two-step
exhaustiveness, and the `d_{3/2}` values.

No instantiation of T46 at a specific Pisot parameter (golden ratio, plastic
number, …) is delivered; none was commissioned, and the numerical comparison
with the paper's table is discussed in `SCRUPLES-round16.md` §4.
