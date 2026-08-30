# SCRUPLES — round 15

Every convention fixed, and every place where the Lean statement is not a
literal transcription of the commission or of the paper.

## 1. T43(b): which regularity class the invariance hypothesis quantifies over

**Lipschitz functions**, in the file's own working form:

```
Lip h        :  ∃ K : ℝ, LipBound K h      (LipBound K h : ∀ x y, |h x - h y| ≤ K |x - y|)
InvariantOn lam nu : ∀ φ, Lip φ → ∫ y, P lam φ y ∂nu = ∫ y, φ y ∂nu
```

Why this class and not "bounded measurable":

1. It is closed under `P` with the constant *improving*: `lipBound_P` gives
   `LipBound (r·K) (P φ)` from `LipBound K φ`.  The induction of
   `integral_iterate_eq` applies invariance to `P^[m] h`, so closure is exactly
   what is needed, and Lipschitz closure is already proved in the module.
2. It is the class the rest of the round-14 development lives in: `tendsto_const`
   and `const_eq_integral_of_invariant` both take a `LipBound` on `h`, so a
   hypothesis quantified over Lipschitz test functions costs the caller nothing.
3. It is the class a construction can supply cheaply.  For `nu` of round 15 the
   verification of `InvariantOn` needs only continuity of the test function and
   an elementary change of variables (T45 below); with bounded measurable test
   functions the same proof would go through, but the integrability side
   conditions would have to be carried by hand rather than being read off
   `integrable_of_lipBound`.

The constant is a **real** `K`, not `ℝ≥0`, for the reason recorded in round 14's
scruples: the iteration multiplies it by `r = 1/λ`.

## 2. T43(a): nothing is assumed about integrability

`hint` is gone.  `integrable_of_lipBound` proves that a function with a
Lipschitz bound is integrable against any probability measure `nu` with
`nu (Icc 0 1)ᶜ = 0`: it is continuous, hence measurable, and on `[0,1]` it is
bounded by `|h(1/2)| + K` (`abs_le_of_lipBound_on_Icc`), which is where the
support hypothesis is used.  `integrable_iterate` composes this with
`lipBound_iterate`.

Round 14's statement is **not deleted**: it survives verbatim, renamed
`const_eq_integral_of_iterate_invariant`, and the new
`const_eq_integral_of_invariant` is derived from it.  Anything that was true
before is still true under a name.

Two further statements were added because they are free once T43 is in place:
`integral_eq_of_invariant` (any two invariant probability measures carried by
`[0,1]` give every Lipschitz function the same integral — uniqueness on the test
class) and `tendsto_integral_of_invariant` (the packaged rate statement).  The
sharpness of the contraction constant in `prop:gap` is **not** among them; it
was explicitly not commissioned and remains uncertified, as round 14 left it.

## 3. T44: the `1 < lam` asymmetry between the two directions

`denseFrom_half_imp_kindDense` (round 14) needs **no hypothesis on `lam`**: a
branch letter is turned into a move by `toMove`, and `survives lam (toMove i) x`
is *the same predicate* as `branchLegal lam i x`, whatever `lam` is.

`kindDense_imp_denseFrom_half` (round 15) needs `1 < lam`, and the hypothesis is
used exactly once, in `branchLegal_branch`, and only for the middle move:

* `L`: `branch = 1` and `survives L x` is `g < x` is `branchLegal 1 x` — same
  predicate, no hypothesis.
* `R`: `branch = 0` and `survives R x` is `x < r` is `branchLegal 0 x` — same.
* `M`: survival is `x < r/2 ∨ 1 - r/2 < x`.  On the first branch we must know
  `x < r`, and `x < r/2 ≤ r` needs `0 ≤ r`; on the second we must know
  `g = 1 - r < x`, and `1 - r ≤ 1 - r/2 < x` needs `0 ≤ r` again.  With `r < 0`
  (i.e. `lam < 0`) both fail, so the hypothesis is not an artefact of the proof.

`0 < r` — equivalently `1 < lam`, the standing hypothesis of the paper — is what
is assumed; `0 ≤ r` would do.

The biconditional `denseFrom_half_iff_kindDense` therefore carries `1 < lam`,
inherited from this direction only.

## 4. T45: the conventions of the construction

**What is constructed.**  A probability measure `nu lam` on `ℝ` with
`nu (Icc 0 1)ᶜ = 0` and `Contraction.InvariantOn lam (nu lam)`, for every
`1 < lam`.  Nothing else about it is claimed — see §6 for the precise limit of
what this certifies.  What *is* proved beyond the invariance is that any two
measures with these properties integrate Lipschitz functions alike
(`integral_eq_of_invariant`), so "the" invariant measure is legitimate on the
test class.

**The route taken, and why it is an improvement rather than a retreat.**  The
commission's suggested route — the product of Bernoulli(1/2) laws on
`ℕ → Fin 2` pushed forward by `ε ↦ (1-r) ∑ ε_j r^j`, with invariance coming from
the factorisation of the product into the first coordinate and the shift — was
advisory, and it is recorded here as *rejected on the merits*, not as a
deviation forced by circumstance.  It is more expensive for exactly the reason
that the alternative is cheap.  `Measure.infinitePi` exists at this toolchain,
but the factorisation lemma does not: one would have to build the measurable
equivalence `(ℕ → X) ≃ᵐ X × (ℕ → X)`, identify the push-forward of the infinite
product under it with a binary product, and only then start on the invariance.
That scaffolding is the bulk of the work and none of it is about the operator
`P`.

Taking instead the **binary digits of a uniform real** costs none of it, and
gives the three ingredients directly:

* the digits of a uniform point of `(0,1]` *are* i.i.d. Bernoulli(1/2) — no
  product measure has to be constructed for that, because Lebesgue measure is
  already the law of the digit sequence, and the only fact used downstream is
  that each half of `(0,1]` maps onto the whole of it;
* the shift on digit sequences becomes the **doubling map** `t ↦ fract (2t)`,
  an ordinary self-map of the line, so the self-similarity `bval_rec` is an
  identity between real numbers rather than a statement about a product
  σ-algebra;
* the two branches of the doubling map supply the **factor of one half** in
  `P` by the elementary change of variables `s = 2t` on `(0,1/2)` and on
  `(1/2,1)`, each contributing `1/2` of the integral.  This is the step that
  the product-measure route pays for with the factorisation lemma.

So a later round should not re-derive the product-measure construction: it
would reach the same measure by a longer road.  Concretely, the same law is
obtained here from

```
digit j t = if fract (2^j t) < 1/2 then 0 else 1
bval lam t = (1 - r) ∑' j, digit j t · r^j
nu lam = map (bval lam) (volume.restrict (Ioc 0 1))
```

Everything the invariance proof needs is then interval-integral calculus on
`(0,1]`.

**Where the exceptional points are.**  `bval_rec` — the self-similarity
`bval t = (1-r)·digit₀ t + r·bval (fract 2t)` — holds for **every** real `t`.
The two branch forms specialise it:

* `bval t = r · bval (2t)` for `0 ≤ t < 1/2`;
* `bval t = (1-r) + r · bval (2t-1)` for `1/2 ≤ t < 1`.

Both fail at `t = 1`, where every digit vanishes and `bval 1 = 0`.  The change
of variables is therefore performed with `intervalIntegral.integral_congr_ae`,
the exceptional set being the single point `1/2` on the first half and `1` on
the second.  No approximation is involved: the identity of the two integrals is
exact.

**`Ioc 0 1`.**  The uniform point ranges over `Ioc 0 1`, which is a probability
measure for Lebesgue and is what `∫ t in 0..1` unfolds to.  `Icc`, `Ico` or
`Ioo` would give the same measure `nu`.

**Test functions in `invariantOn_nu`.**  Only continuity of `φ` is used, through
`integral_nu` and the interval-integrability lemma
`intervalIntegrable_comp_bval`; the Lipschitz hypothesis of `InvariantOn` is
thus stronger than this proof needs, but it is what the interface asks for, and
supplying more than is needed costs the construction nothing.  Boundedness comes
free:
`bval` takes values in `[0,1]` and a continuous function is bounded there
(`exists_bound_on_Icc`).

**What is still open after round 15.**  The pointwise upgrade at `x = 1/2`
(paper Question 50) is untouched, as commissioned.  `equidistribution_in_mean_nu`
identifies the limit constant of `thm:equimean` as `∫ k dν`, which is the
paper's phrasing; the density `dν_r/dx` is *not* constructed, so the weak
convergence statement in the form "`K(m,x)/(2/λ)^m → dν_r/dx`" remains as round
14 left it.

## 5. Where the two regularity classes meet, and why they do not clash

`Contraction.InvariantOn` quantifies over **Lipschitz** test functions (§1),
while `EquiMean` works in the **bounded measurable** class `BddMeas`, because
`S h` carries two indicators and is discontinuous.  That is a genuine
difference of classes, so it was checked rather than assumed.  The check is:
every place where invariance is *eliminated* — i.e. where the universally
quantified `InvariantOn` hypothesis is applied to an argument — is applied to a
function carrying a `LipBound`.

There is exactly one such place in the whole development:

* `Contraction.integral_iterate_eq`, in the successor step of its induction,
  applies `hinv` to `(P lam)^[m] h`, with the Lipschitz witness
  `Lip.of_lipBound (lipBound_iterate hlam m hK)`.  This is the closure property
  of §1 and is why the class had to be closed under `P`.

Every other occurrence of `InvariantOn` in the tree is a hypothesis being
carried, not applied: `const_eq_integral_of_invariant`,
`integral_eq_of_invariant` and `tendsto_integral_of_invariant` in
`Contraction.lean` pass `hinv` on to `integral_iterate_eq`, and
`const_eq_integral_nu`, `tendsto_integral_nu` in `InvariantMeasure.lean`
discharge it with `invariantOn_nu`.  All five of those statements require a
`LipBound` on the function being integrated, so no caller can reach invariance
with a merely bounded measurable function.

The one statement in which the two classes appear together is
`InvariantMeasure.equidistribution_in_mean_nu`:

```
(hh : EquiMean.BddMeas Ch h) (hk : EquiMean.BddMeas Cg k) (hlip : LipBound K k)
```

Here `h`, the function the operator `S` iterates, is bounded measurable only —
it never meets the invariance — while `k`, the test function paired with the
iterates and the one fed to `P`, `tendsto_const` and hence to
`const_eq_integral_nu`, carries `hlip`.  So `k` is Lipschitz at the point of
use, and `EquiMean.equidistribution_in_mean` already demanded exactly that in
round 14 (it takes `hlip : Contraction.LipBound K k` alongside `hk`).  The
round-15 statement adds no regularity to round 14's and drops none: the only
change is that the constant `c` and its estimate `hc` are supplied rather than
assumed.

Two consequences worth recording.  First, `EquiMean` never mentions
`InvariantOn` or `const_eq_integral_of_invariant` as a *term*: the only two
occurrences of that name in the module are in its module docstring and in the
docstring of `equidistribution_in_mean`, which is why round 15's rename of the
round-14 statement to `const_eq_integral_of_iterate_invariant` did not touch it.
This was confirmed by inspection of the two occurrences and by building the
module, not assumed.  Second, nothing here weakens `EquiMean`: the bounded
measurable class is still where the operator identities live, and the Lipschitz
class is still where the contraction lives; they meet only through `k`.

## 6. The limit of what T45 certifies

Stated exactly, so that no later round reads more into it:

* `nu lam` is a probability measure on `ℝ` (`isProbabilityMeasure_nu`), carried
  by `[0,1]` (`nu_compl_Icc`), invariant for `P` against Lipschitz test
  functions (`invariantOn_nu`), for every `1 < lam`.  That is the whole of the
  certified content, together with the three consequences
  `const_eq_integral_nu`, `tendsto_integral_nu`, `equidistribution_in_mean_nu`.
* **Nothing connects `nu` to `FourierFloor.cosProd`.**  `FourierFloor.lean`
  records in its own scruples that its statements are theorems about the
  explicit cosine product and that no identification of that product with the
  Fourier transform of a measure is asserted.  Round 15 does not change this in
  either direction: no transform of `nu` is computed, no relation between `nu`
  and `cosProd` is stated, and the Fourier-side results remain statements about
  a function of a real variable.
* No regularity of `nu` is proved: no density, no absolute continuity, no
  singularity, no dimension, no decay, and no Pisot dichotomy.
* Accordingly `nu` is *not* described anywhere in these documents or in the
  sources as the Bernoulli convolution.  It is the law of the digit series, and
  it is invariant; whether it coincides with any measure of the literature is
  not part of what is certified.

**Why this is cheaper than it looks to close later.**
`Contraction.integral_eq_of_invariant` is a *uniqueness* statement: any two
probability measures carried by `[0,1]` and invariant for `P` give every
Lipschitz function the same integral.  A later round that wishes to identify
`nu` with a measure defined some other way therefore does not need a second
construction, nor any property of `nu` beyond what is already proved.  It needs
only to exhibit that other measure as a probability measure carried by `[0,1]`
satisfying `InvariantOn`; uniqueness on the Lipschitz test class then does the
identification.  That is the intended use of `integral_eq_of_invariant`, and it
is the reason it was proved here even though nothing in round 15 consumes it.

## 7. What was built, and what was audited

The round's own modules were built one at a time, never the union and never a
bare `lake build`:

```
lake build RequestProject.Contraction        -- success
lake build RequestProject.InvariantMeasure   -- success
lake build RequestProject.EquiMean           -- success
lake build RequestProject.BackwardClosure    -- success
```

These four cover the round's blast radius.  `Contraction.lean` is an inherited
module that round 15 edited (T43 dropped a hypothesis and renamed round 14's
statement), so everything importing it had to be rebuilt; the modules whose
import list names `RequestProject.Contraction` are exactly `EquiMean`,
`InvariantMeasure` and `All`, and no other file in the tree imports it, directly
or transitively.  `BackwardClosure` is in the list for a different reason: T44
edited it, and it is a leaf (nothing imports it but `All`).  `All` is
deliberately **not** built here: it imports the whole tree, so building it is a
whole-tree build under another name, and the union is CI's job, not the round's.
The union of the four builds is therefore the complete set of modules whose
elaboration this round could have changed.

`#print axioms` was run on this round's own theorems only; the transcript is
`AXIOM-AUDIT-round15.md` and every report is
`[propext, Classical.choice, Quot.sound]`.
