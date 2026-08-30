# SCRUPLES — round 16

Every convention fixed, and every place where the Lean statement is not a
literal transcription of the commission.

## 1. The shape of the constant: a power of the maximum, not a product

The commission allows either "a product over the conjugates" or "a power of the
maximum" and asks which was taken and why. **A power of the maximum** was
taken:

```
B     = (2 + 2*c) / (1 - c)              c a bound on the conjugate moduli
delta = 1 / (2 * (2*B) ^ (d - 1))        d = Module.finrank ℚ ℚ⟮lam⟯
```

Reasons, in order of weight.

1. It composes with what the tree already proves. `Pisot.conj_bound` gives one
   bound, `(2 + 2‖z‖)/(1 − ‖z‖)`, valid for *every* conjugate `z` with
   `‖z‖ < 1`, and the round-14 proof of `orb_finite` already collapses those
   bounds into a single number. A product over the conjugates would require the
   bound to be indexed by the embedding all the way through
   `one_le_norm_mul_pow`, which buys sharpness the round is not asked for.
2. The uniform `c` is where the arbitrary choice is, not the exponent: the
   function `t ↦ (2 + 2t)/(1 − t)` is increasing on `[0,1)`, so replacing each
   `‖ψ lamK‖` by the common bound `c` is a single monotonicity step
   (`hmono` in the source) and nothing else in the argument changes.
3. The separated-set count of T46(b) consumes only `1/δ`, so a product would
   have to be evaluated to a number there anyway.

The estimate proved is exactly
`1 ≤ 2*|x − y| * (2B)^(d−1)`, that is `δ ≤ |x − y|`, and the constant `δ`
mentions only `c` and `d`. It does not mention the orbit, the two points, or
the length of the branch words: in the source, `w` and `w'` are introduced
*after* `B` is fixed and appear in no bound.

## 2. Where the degree enters, and what is assumed about it

`d` is `Module.finrank ℚ (ℚ⟮lam⟯ : IntermediateField ℚ ℝ)` — the degree of the
field the orbit actually lives in, not the degree of the witnessing polynomial
`p`. Nothing is assumed about it: `Pisot.lean`'s scaffolding
(`IsIntegral.tower_top`, `IntermediateField.adjoin.finiteDimensional`) makes
`ℚ⟮lam⟯` a number field from `IsPisot`'s integrality alone, and
`NumberField.Embeddings.card` identifies `d` with the number of complex
embeddings. The exponent `d − 1` is truncated natural subtraction; `d ≥ 1`
always, so no degenerate case arises, and no hypothesis `d ≥ 1` is carried.

If one prefers the degree of `p`, the bound only weakens: `2B ≥ 4 > 1`, so the
right-hand side is monotone in the exponent and `deg p ≥ d` may be substituted
freely. That substitution is not performed in the sources.

## 3. Three further conventions

**(a) The hypotheses are the polynomial and a uniform `c`, not `IsPisot`.**
`orb_separated_of_conj_le` and `orb_ncard_le_of_conj_le` take `1 < lam`, a monic
integer polynomial `p` with `lam` as a root, and a single `c` with `0 ≤ c < 1`
bounding `‖z‖` for every complex root `z ≠ lam`. `IsPisot` gives `‖z‖ < 1` root
by root, with no uniform `c`; `exists_conj_bound` produces one by taking the
maximum of `0` and the finitely many `‖z‖` over `q = p.map (Int.cast)`'s roots
other than `lam`, and `orb_separated` packages the result from `IsPisot` alone.
This is a strengthening, not a weakening: the parametrised form is what a caller
with an explicit polynomial wants, and the `IsPisot` form loses nothing.

**(b) The distinguished embedding is not characterised.** The commission's
sketch bounds the *conjugate* embeddings and treats the real one separately.
The source bounds **all** embeddings by `2B` — for the real one because
`x, y ∈ (0,1)` gives `|2x − 2y| ≤ 2 ≤ 2B`, for the others by `conj_bound`. The
case split is on `ψ lamK = (lam : ℂ)`, not on `ψ ≠ φ`, so no argument is needed
that an embedding fixing `lam` is the identity of `ℚ⟮lam⟯`. `one_le_norm_mul_pow`
is stated with the bound quantified over all embeddings for the same reason;
it loses a factor of at most `2B/(2|x − y|)` and buys a shorter proof.

**(c) Cardinality is `Set.ncard`, and finiteness is re-derived.**
T46(b) is stated as `(Orb lam).Finite ∧ (Orb lam).ncard ≤ ⌊2*(2B)^(d−1)⌋₊ + 1`.
Both conjuncts come from `finite_ncard_le_of_separated`, which injects a
`δ`-separated subset of `(0,1)` into `Set.Iic ⌊1/δ⌋₊` by `x ↦ ⌊x/δ⌋₊`; so the
new statement does **not** depend on `orb_finite`. Round 14's `orb_finite` is
therefore left standing, untouched and unrestated, and operating rule 9 is not
triggered: no inherited module was edited this round.

## 4. How weak the constant is, and what that means

The constant is uniform but far from the truth. For the golden ratio, where
`c = (√5 − 1)/2 ≈ 0.618` and `d = 2`, the formula gives `B ≈ 8.47`,
`δ ≈ 0.0295` and a cardinality bound of `34`. The paper's table records orbit
sizes of `5`, `7`, `43`, `153`. So the bound is of the right kind — a number
computed from `λ` alone — and is not competitive with the observed values; it is
also not directly comparable to them without knowing which parameters the table
rows are. **This paragraph is ordinary arithmetic done by hand, not a Lean
computation**: nothing in the sources evaluates the constant at any specific
`λ`, and no such instantiation was commissioned.

Two identified sources of slack: the uniform `c` in place of the individual
conjugate moduli (§1), and the crude `|2x − 2y| ≤ 2` used for the real
embedding, which is a bound on the diameter of `(0,1)` doubled rather than on
the separation being estimated.

## 5. Nothing else was touched

No inherited source was edited. The only files changed outside the new module
are `RequestProject/All.lean` (one import) and `.github/workflows/ci.yml` (one
module name), both required by operating rule 8, plus the round documents,
`README.md` and `STATE-OF-PLAY.md`. No `sorry`, no `admit`, no added `axiom`,
no `@[implemented_by]`, no `native_decide`, no `decide` in the round's source.
