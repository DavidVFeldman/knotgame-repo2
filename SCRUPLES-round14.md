# SCRUPLES — round 14

Every convention fixed, and every place where the Lean statement is not a
literal transcription of the commission or of the paper.

## 1. Which formulation of the Lipschitz bound (asked for explicitly)

The commission asks which of the two formulations of T40(b) was chosen.  It is
the **`LipschitzWith` formulation**, as recommended:

```
lipschitz_contraction :
  LipschitzWith K h → LipschitzWith (Real.toNNReal (r lam) * K) (P lam h)
```

No differentiability is assumed anywhere in the file; the derivative identity
`(Ph)'(y) = (r/2)[h'(ry) + h'(ry+1−r)]` of the paper is the idea of the proof,
not a statement.

Inside the module the working form is the equivalent explicit inequality

```
LipBound K h  :  ∀ x y, |h x - h y| ≤ K * |x - y|
```

with a **real** constant, because the iteration multiplies the constant by
`r = 1/λ`, which is real, and `ℝ≥0` arithmetic with `Real.toNNReal` adds noise
at every step.  `lipBound_of_lipschitzWith` and `lipschitzWith_of_lipBound`
convert in both directions, and both `lipschitz_contraction` and
`lipschitz_contraction_iterate` are stated in the `LipschitzWith` form.

## 2. Is the limit constant identified? (asked for explicitly)

**No — it is hypothesised, not proved**, exactly as the commission directs and
exactly as round 13 handled the trapezoid's independence hypothesis.

* `tendsto_const` produces *a* constant `c` and the rate `r^m` on `[0,1]`.  It
  says nothing about what `c` is.
* `const_eq_integral_of_invariant` identifies it: if `ν` is a probability
  measure carried by `[0,1]`, if the iterates are `ν`-integrable and if
  `∫ (P^[m] h) dν = ∫ h dν` for every `m`, then `∫ h dν = c`.  The invariance is
  an explicit hypothesis of the theorem.  What a construction of the Bernoulli
  convolution `ν_r` would supply is precisely that hypothesis.
* `equidistribution_in_mean` accordingly states the limit as
  `(∫₀¹ h dx)·c` with the same `c`, not as `(∫₀¹ h)(∫ g dν_r)`.

## 3. Conventions in T40

* `P` is defined on all of `ℝ`.  The contraction estimate is global; the
  convergence statement is confined to `[0,1]`, where it belongs — on the whole
  line the iterates of a nonconstant Lipschitz function do not converge to a
  constant.
* The route to the limit is the recommended nested-interval one.  The values of
  `P^[m] h` on `[0,1]` lie within `r^m K` of each other because both branch
  images `ry`, `ry+1−r` of a point of `[0,1]` are again in `[0,1]`; the midpoint
  sequence `P^[m] h (1/2)` is therefore geometrically Cauchy, and its limit
  traps everything on `[0,1]`.  No Cauchy estimate in a function space and no
  completeness of a space of functions is used.
* The explicit rate is `|P^[m] h y − c| ≤ (2K/(1−r))·r^m` for `y ∈ [0,1]`.  The
  constant `2/(1−r)` is not claimed to be optimal; the commission asks for the
  rate `r^m`, and that is what the geometric factor is.

## 4. Conventions in T41

* **Alphabet.**  The two-letter *branch* alphabet is used throughout, via the
  T39.5 bridge, as the commission requires.  The three-letter move alphabet
  carries the constant `3/λ` instead — round 13's correction to T38 — and does
  not appear in this module.
* **The endpoint measure `μˣ_m` is not constructed as a `Measure`.**  It is the
  sum of the Dirac masses at the endpoints `Φ_ε(x)` of the branch words legal
  from `x`, counted with multiplicity, so `∫ h dμˣ_m` is literally the finite
  sum `∑_{ε ∈ branchWords λ x m} h (rapp λ x ε)`.  `endpoint_propagator` proves
  the identity in that form.  Nothing is lost: the paper's `∫ h dμˣ_m` is by
  definition that sum.
* **Regularity.**  `h` and `k` are assumed *bounded and measurable* (`BddMeas`),
  where the paper says "continuous on `[0,1]`".  A continuous function on
  `[0,1]`, extended boundedly to `ℝ`, satisfies this.  The weakening is
  necessary, not cosmetic: `S h` carries two indicators and is discontinuous, so
  continuity cannot be propagated along the induction that moves the `m`
  iterates from `S` to `T`, whereas boundedness and measurability can.  For the
  limit statement `k` is in addition `LipBound K`, which is what T40 consumes.
* **The order of the two functions.**  In `equidistribution_in_mean` the
  Lipschitz function is the one the operator `T`/`P` acts on (the paper's `g`),
  and the merely bounded measurable one is the one `S` acts on (the paper's
  `h`).  This matches the paper's proof, in which the spectral gap is applied to
  `g`.
* **Domain of integration.**  All integrals are over the open interval
  `Ioo 0 1`, as everywhere in `CountingOperator`; the endpoints are Lebesgue-null
  so this agrees with the paper's `∫₀¹`.

## 5. Conventions in T42 (recorded again here for completeness)

* `DenseFrom lam x` has the same shape as `KnotGame.KindDense`: every `c < d`
  with `0 ≤ c`, `d ≤ 1` contains an endpoint strictly inside.  It is certified
  for no particular `λ`; the content of T42 is that it *implies* the paper's
  hypothesis, not that it holds.
* Words act on the left: `rapp lam x (u ++ v)` applies `u` first, so `ε` is a
  prefix and the level shift in `endpoints_subset_of_legal` is `m + |ε|`.

## 6. What is deliberately absent

* No construction of `ν_r`, and no statement that presupposes one.
* No pointwise upgrade at `x = 1/2`, and no weakened variant of it (paper
  Question 50).
* No fourth copy of the branch-word layer.
* No `sorry`, no `admit`, no new `axiom`, no `@[implemented_by]`, no
  `native_decide`.
