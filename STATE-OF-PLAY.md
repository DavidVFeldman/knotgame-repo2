# State of play — handoff to a new session

## Where things stand

**The paper** (`knotgame.tex`, 42pp, clean compile): *On a problem of Eugene
Lawler: knot counts in an interval deletion game*, dedicated to the memory of
Steven Rudich, who communicated the problem. Organised around a table of
relaxations (§2), each row stating what it buys and what it costs. The central
question — is the knot count bounded at λ = 3/2 — is open.

**The formal development**: green under CI at every commit; the last audit
reported 1667 theorems with axioms confined to propext, Classical.choice,
Quot.sound, before round 13 added three more modules (KindBox,
CountingOperator, Trapezoid). Round 13 was the first run under the working
rule that has made rounds fast: **the prover builds only the modules it
writes; the union is built and audited by CI.**

**Round 14 (the spectral material) is delivered**: `BranchBridge` (the three
copies of the branch-word layer are now identified), `Contraction`
(Proposition 48 as far as it can go without ν_r), `EquiMean` (Theorem 49 in
the same sense) and `BackwardClosure` (the two-letter reduction and the
backward closure of D). Per-theorem `#print axioms` for all four modules is in
`AXIOM-AUDIT-round14.md`. **One caveat, stated plainly:** the invariant measure
ν_r is still nowhere constructed, so what is certified is convergence of
`P^m h` to *a* constant at rate `r^m`, together with the identification of that
constant *given* an invariance hypothesis on a probability measure carried by
[0,1]. Constructing ν_r is the first item a later round should take up if the
paper's phrasing is to be matched literally.

## The live mathematical frontier

The paper's one conditional route to unboundedness is the density criterion
(§10): if the endpoints of kind words are dense in (0,1), then N_λ = ∞. The
counting half is settled — an unconditional exponential lower bound on the
number of surviving branch words, uniform on a window containing 3/2. The
spreading half is open, and the last session sharpened it:

* **Proposition 48 (proved).** P = (λ/2)T, the normalised counting operator,
  contracts the Lipschitz seminorm by exactly r = 1/λ. Hence P^m h converges
  uniformly to ∫h dν_r at rate r^m, where ν_r is the Bernoulli convolution.
* **Theorem 49 (proved).** Dually, averaged over the starting point the
  normalised endpoint measures converge weakly to **Lebesgue**, while the
  total mass is governed by ν_r: K(m,x)/(2/λ)^m → dν_r/dx weakly in x.
  Numerically at √2 the ratio matches the exact trapezoid to relative L¹
  error 0.0037 by m = 20; endpoints from 1/2 flatten as 0.185, 0.0275,
  0.0114, 0.0046 at m = 12, 16, 20, 24 — the predicted r^m.
* **The obstruction, identified.** The upgrade needed is mean → pointwise at
  x = 1/2. The obvious route (Lasota–Yorke on BV) is CLOSED: Var(Sh) ≤ 2Var(h)
  with 2 attained, and 2 > 2/λ for every λ > 1, so the essential radius would
  exceed the peripheral eigenvalue; iterating does not help.
* **A structural handle.** Let D be the starting points whose endpoint sets
  become dense. If y is any legal image of x then y ∈ D ⟹ x ∈ D. So it
  suffices to put ONE point of the forward orbit of 1/2 into D — a set of
  positive measure whenever ν_r has a density. The orbit is countable, which
  is exactly why the measure statement does not reach it.
* **Why Pisot is different, in one line.** At a Pisot parameter ν_r is
  singular (Erdős), so the multiplicity density ψ does not exist; those are
  precisely the parameters where the game is bounded.

## Working rules that made rounds fast (do not regress)

1. `lake exe cache get` FIRST. A report of "8125 of 8145" means Mathlib is
   being compiled from source and the project has not been reached.
2. Never a bare `lake build`; build only your own modules, one at a time.
3. Never a tree-wide audit; `#print axioms` on your own theorems only.
4. Exit code 143 is SIGTERM — a module too large for the machine, not a Lean
   error and not a timeout.
5. `RequestProject` is a Lake library built by DIRECTORY GLOB: a file sitting
   in it is compiled whether or not All.lean imports it. To exclude a file,
   remove it from the directory.
6. file set = transitive import closure of All.lean. Two files in this
   project (Square.lean, KindBox.lean) were reported complete by the sessions
   that wrote them and had never been elaborated; both were caught this way.
7. A session's report is not an audit. The test is whether an AXIOM-AUDIT
   document names the identifier.

See GITHUB_HANDOFF_CHECKLIST §15 for the full version, and UNBUILT.md for the
three modules held outside the closure and why.

## Open items, ranked

1. The spreading half above (Question 50).
2. The one open step of the trapezoid: that the even- and odd-indexed
   sub-series at √2 are independent and uniform (ABANDONED.md §9).
3. A cheaper certificate checker (shared prefixes): the search already finds
   better data than the kernel can afford, so the certified rate at 3/2 is
   26^(1/14) ≈ 1.262 against a true 4/3.
4. The quarantined modules via heavy.yml: the plastic closure (audited, held
   out for memory only) and the multiplicity-49 certificate (never audited).
5. Publication: verify the Lawler attribution in the literature; check the
   Erdős–Joó–Komornik citation precisely; find a reader who knows Z-numbers
   for §12.

## Addendum — round 15 (T43, T44, T45)

Three things above are now out of date, and this addendum records what
replaces them.

1. **"ν_r is still nowhere constructed" is no longer true.**
   `RequestProject/InvariantMeasure.lean` builds a probability measure `nu lam`
   on `ℝ`, carried by `[0,1]`, and proves it invariant for the normalised
   counting operator (`invariantOn_nu`).  It is the law of the binary digit
   series `bval lam t = (1-r) ∑ digit_j(t) r^j` under a uniform point of
   `(0,1]`.  It is *not* identified with any measure named elsewhere in the
   project or in the literature: in particular nothing connects it to
   `FourierFloor.cosProd`, whose own scruples record that no identification of
   that cosine product with the Fourier transform of a measure is asserted.
   Consequently `P^m h` converges
   uniformly on `[0,1]` to `∫ h dν` at rate `r^m` with no hypothesis beyond
   `1 < λ` (`tendsto_integral_nu`), and `thm:equimean` holds with its constant
   identified (`equidistribution_in_mean_nu`).  No regularity of `nu` — density,
   singularity, Fourier decay, the Pisot dichotomy — is proved; those remain
   open here.  Note that `integral_eq_of_invariant` makes a later
   identification cheap: it is a uniqueness statement, so exhibiting any other
   probability measure carried by `[0,1]` as invariant identifies it with `nu`
   on the Lipschitz test class, with no second construction needed.
2. **The identification is no longer hypothetical in shape either.**  The
   round-14 statement assumed integrability of every iterate and `m`-fold
   invariance; both are now proved rather than assumed (`integrable_iterate`,
   `integral_iterate_eq`), from one-step invariance against Lipschitz test
   functions (`InvariantOn`).  Any two such measures integrate Lipschitz
   functions alike (`integral_eq_of_invariant`).
3. **The two density hypotheses are equivalent.**
   `kindDense_imp_denseFrom_half` supplies the converse of round 14's
   inclusion, so `denseFrom_half_iff_kindDense` (for `1 < λ`) certifies that
   the two-letter analysis is the whole of the spreading problem.

The live frontier is unchanged: Question 50, the pointwise upgrade at `x = 1/2`,
is untouched, and the Lasota–Yorke route to it is still closed.  The remaining
open items are as ranked above, minus the construction of `ν_r`.

## Addendum — round 16 (T46)

`Pisot.orb_finite` is no longer the only thing known about the orbit at a Pisot
parameter.  `RequestProject/PisotSeparation.lean` makes it quantitative:

1. **Separation.**  `orb_separated_of_conj_le`: with `c < 1` a bound on the
   moduli of the conjugates of `λ`, `B = (2 + 2c)/(1 − c)` and
   `d = [ℚ(λ) : ℚ]`, distinct points of `Orb λ` are at distance at least
   `1 / (2·(2B)^(d−1))`.  The constant names only `c` and `d` — not the orbit,
   not the two points, not the branch words.  The mechanism is the field norm:
   `2(x − y)` is a nonzero algebraic integer of `ℚ(λ)`, every conjugate of it is
   bounded by `2B` (round 14's `conj_bound`), and the product of the moduli of
   its complex embeddings is at least `1` (`one_le_prod_norm_embeddings`, proved
   here from Mathlib's `Algebra.norm_eq_prod_embeddings`).
2. **A count, not just finiteness.**  `orb_ncard_le_of_conj_le`:
   `Orb λ` is finite with `ncard ≤ ⌊2·(2B)^(d−1)⌋ + 1`, by the elementary fact
   that a `δ`-separated subset of `(0,1)` has at most `1/δ + 1` elements
   (`finite_ncard_le_of_separated`).  Finiteness is re-derived rather than
   inherited, so `orb_finite` is untouched and unused by the new module.
3. **Packaged from `IsPisot`.**  `orb_separated` supplies the uniform `c` from
   the finitely many roots of the witnessing polynomial.

What this does **not** do: it says nothing about `N_λ`.  The passage from
separation to a bound on the knot count runs through `thm:schedule`, which is
not formalised in the shape that step needs.  The constant is also weak — at the
golden ratio it gives a cardinality bound of about 34 by hand, against orbit
sizes of 5, 7, 43, 153 in the paper's table — and nothing in the sources
evaluates it at a specific `λ`.

The live frontier is unchanged: Question 50, the pointwise upgrade at `x = 1/2`.
