# SCRUPLES — round 8

Every place where a round-8 Lean statement is not a literal transcription of
the paper, and every convention that had to be fixed.  Conventions inherited
from earlier rounds (the window open at both ends, survival by strict
inequalities, `g + r = 1`, `N_λ` unbounded written `∀ K, ∃ n, K ≤ N λ n`) are
unchanged and not repeated.  Each item also appears in the docstring of the
file it belongs to.

## 1. T22a — the ternary reformulation (`prop:ternary`)

* **`D` is `⌊3x⌋`, an integer.**  The paper's cell index `D(x) ∈ {0,1,2}` is
  `Ternary.D x = ⌊3x⌋`.  On `[0,1)` this is exactly `{0,1,2}`
  (`D_eq_zero_iff`, `D_eq_one_iff`, `D_eq_two_iff`, `D_cases`).  Moves are
  coded `L, M, R ↦ 0, 1, 2` by `Ternary.code`.
* **Cell boundaries.**  The three closed intervals `[0,1/3]`, `[1/3,2/3]`,
  `[2/3,1]` of the paper overlap at `1/3` and `2/3`; `D` resolves the overlap
  by taking the *left-closed* cells.  This costs nothing along the game: the
  dyadic invariant (`Dyadic`, `dyadic_act`, `dyadic_posAfter`, together with
  `three_mul_ne_one`, `three_mul_ne_two`) shows a reachable position is never
  on a boundary.  That invariant is the same fact that "adjoins `1/2`" when
  `c = 1` in the paper's phrasing.
* **The image formula.**  `act_eq_ternary` is `x ↦ (3x − [D x > c]) / 2`, with
  the Iverson bracket as an `if … then 1 else 0` over `ℤ` cast to `ℝ`.
* **Exactly one fatal digit.**  `exists_unique_fatal` is stated as a
  `∃!` over the three moves, for any `x` with `0 ≤ x` and `x < 1`.

## 2. T22b/c — base 3/2 and Mahler (`prop:base32`, `prop:mahler`)

* **Indexing.**  Itineraries are 0-based in Lean: `eps k` is the paper's
  `ε_{k+1}`.  `orbit lam eps x` is the paper's `x_n`.
* **`prop:itinerary` is proved for general `λ`,** not only `3/2`:
  `itinerary_tsum` gives `x = (1 − r) ∑_{k≥0} ε_{k+1} r^k` whenever the orbit
  stays in `[0,1]`.  `base32_tsum` is the specialisation at `λ = 3/2`,
  `x = 1/2`.
* **Non-strict vs strict bracket.**  The paper writes
  `D(x_n) = ε_{n+1} + [2x_{n+1} > 1]`.  The identity that holds with no further
  hypothesis is the **non-strict** one, `D(x_n) = ε_{n+1} + [2x_{n+1} ≥ 1]`
  (`digit_eq_eps_add`).  The two differ only at `x_{n+1} = 1/2`;
  `digit_eq_eps_add_strict` records the paper's strict form under the
  hypothesis `x_{n+1} ≠ 1/2`, which `dyadic_posAfter` supplies along the game
  after the first move.  This is a real deviation and is flagged as such.
* **What T22c does and does not claim.**  `mahler_recursion` and
  `mahler_of_survives` certify that the game's recursion *is* the recursion of
  Mahler's problem in the `(p, y)` coordinates.  **Nothing is claimed about
  Mahler's problem itself**; no `3/2`-number result is imported or asserted.
* `Int.fract` is Lean's `{·}`.

## 3. T22d — the knot-free equivalent (`prop:translation`)

* **0-based control indexing.**  `c j` is the letter applied between time `j`
  and time `j+1`.  A birth at letter `b` (`c b = 1`) therefore produces a knot
  at *time* `b+1`, driven thereafter by `c (b+1), c (b+2), …`.  The paper
  indexes from `1`, where birth letter and birth time carry the same number.
  The two conventions describe the same object; the shift is visible in
  `witer_shift` and in `ctrl`.
* **The control is a total function.**  `c : ℕ → ℤ` with values in `{0,1,2}`
  (`ctrl_mem`); only `c 0, …, c (N−1)` are used, the rest is junk that no
  statement reads.
* **"Stay in `(0,2)`" is not a separate condition.**  A trajectory that avoids
  the control stays in `(0,1)` in the `x`-coordinate automatically
  (`act_mem_Ioo`), so `MahlerAlive` is exactly the avoidance condition and the
  interval constraint of the paper is a consequence, not a hypothesis.
* The equivalence `unbounded_iff_mahler` is stated at `λ = 3/2` only, as in the
  paper.

## 4. T23 — periodic kind words (`prop:kindyield`)

* **The distinction from `no_return_to_half` — the important one.**
  `RequestProject/Littlewood.lean` certifies (paper `cor:noperiodic`) that
  under a periodic run the orbit of a knot born at an `M` never *returns to its
  birth point* `1/2` at a time divisible by the period.  That closes the
  algebraic route to unboundedness: one cannot manufacture a periodic kind word
  by solving for a parameter at which `1/2` is a periodic point, because there
  is none.

  It does **not** close the route certified here, in which the knot merely
  *stays alive*.  `KindWord lam v` asks only that `1/2` survive every power of
  `v`; it asks the orbit of `1/2` to return nowhere.  The paper's remark after
  `cor:noperiodic` says precisely this, and `PeriodicYield.lean` repeats it in
  its docstring.  Round 8 adds **no evidence either way** about whether a kind
  periodic word exists at any particular `λ`.
* **Relation to `Littlewood.N_unbounded_of_kind`.**  Round 1 already derived
  unboundedness from an *infinite* kind sequence periodic with an `M` at the
  end of the period.  Round 8's contribution is (a) the finite-word
  formulation of the paper, and (b) the conclusion delivered as condition (i)
  of the certified `thm:compactness` (`InfinitelyManyKnots`), i.e. a single
  left-infinite run carrying infinitely many simultaneous knots;
  `N_unbounded_of_kindWord` then recovers the numeric statement.  This is a
  strengthening of the conclusion, not a re-derivation of the round-1 result,
  which is left untouched.
* **Period spelled as a decomposition.**  The paper writes `v_1 … v_p` with
  `v_p = M`; the Lean hypothesis is `v = u ++ [Move.M]`.  Same thing, and it
  makes the split of `v ^ n` immediate.
* **Kindness is prefix-closed.**  `KindWord lam v : ∀ n, survivesWord lam (1/2)
  (rep v n)` is equivalent to `1/2` surviving the left-infinite periodic run,
  which is the paper's phrasing.

## 5. T24 — cylinder counts, and the dimension that is *not* claimed

* **T24c (Hausdorff and box dimension) is not attempted and is not claimed.**
  Mathlib's `dimH` does not appear anywhere in the tree.  `KindTree.lean`
  proves cylinder *counts* only.  A count of `2^n` cylinders at depth `n` does
  not by itself give `dim = log 2 / log 3`: an upper box-dimension bound needs
  a diameter estimate for the cylinders, and the lower bound needs a mass
  distribution / separation argument.  Neither is proved here, and no statement
  in the file should be read as giving them.
* **A node is a word, not a point.**  Two distinct words are two distinct nodes
  of the survival tree even when they carry `1/2` to the same position.  This
  is what makes the count multiplicative and is the paper's convention too.
* **Base of the indexing.**  `N_n` of the paper is
  `(kindWords lam (1/2) n).card`, so `N_0 = 1` (the empty word).
* **T24b is a three-step recursion, not a closed form.**  What is proved is
  `N_{n+3} = 4 N_n` at `λ = φ`, from the certified five-point orbit of
  `Golden.lean`.  No closed formula for `N_n` and no growth rate is asserted.

## 6. T25 — sharpness of the transversality window

* **The search is untrusted.**  `scripts/window_sharp_search.py` produced the
  two coefficient vectors; nothing about it is trusted.  The vectors are inert
  data, and every inequality is re-checked by the kernel over exact rationals
  (`decide`/`norm_num`, no `native_decide`).
* **No tail estimate is needed, because there is no tail.**  `coeffOf l` is
  zero from `l.length` on, so `gval` and `gder` at these members are *exactly*
  the finite sums `gval_coeffOf`, `gder_coeffOf`.  The members have finite
  support (degrees 22 and 26) and are genuine members of the class: constant
  term `1`, all coefficients in `{−1,0,1}` (`coeffOf_mem`, `sharpPoly_zero`,
  `strongPoly_zero`).
* **Strength of the failure.**  The commission asks for `|g(x)| ≤ 1/1000` and
  `g′(x) ≥ −1/1000`.  `witness_at_3339` gives the strict form
  (`−1/1000 < g′ < 0`) at `x = 3339/5000`, only `8/10000` beyond the certified
  right endpoint `667/1000`.  `witness_at_3343` gives a failure with margin
  (`g ≤ 1/100000`, `g′ > 0`) at `x = 3343/5000`.
* **"Essentially optimal", not "optimal".**  `window_not_extendable` says the
  certified window cannot be extended to `[1/2, 67/100]` for this class at
  `δ = 1/1000`.  It does not locate the exact supremum of admissible right
  endpoints, and no such claim is made.
* **Series derivative vs actual derivative.**  `gder` is the termwise
  derivative series; on `(−4/5, 4/5)` it is the derivative
  (`hasDerivAt_gval`), which is what `deriv_witness_at_3339` uses.

## 7. T26 — the quantitative density criterion (`thm:density`)

* **(D_λ) is a hypothesis certified for no `λ`,** exactly like the inherited
  `KindDense`, of which it is a strengthening (`kindDense_of_quant`).
* **The `O(log |v_k|)` of the paper is made explicit.**  The extension bound
  proved is
  `|u| ≤ C(|v| log λ + log(|v|+1))` (`exists_extension_len`), the `log(|v|+1)`
  being what `exists_long_cell` yields.  The paper's
  `|v_{k+1}| ≤ (1 + C log λ)|v_k| + O(log|v_k|)` is `qword_length_step`.
* **The growth constant is explicit.**  `growth lam C = max 2 (1 + C(log λ +
  1))`; the `max 2` is a convenience that makes `B ≥ 2` (`two_le_growth`) and
  absorbs the additive `+1` per step.  The conclusion is
  `(d λ k : ℝ) ≤ B^k − 1` (`d_le_pow`), stated over `ℝ` to avoid truncated
  natural subtraction.
* **`d_λ` is the development's `KnotGame.d`,** `sInf {n | k ≤ N λ n}`.
* **Construction parameterised by an extension function.**  `qword` takes the
  extension function as an argument, so the nesting lemmas are proved once.
  `Density.dword` is the same construction with a different, unquantified
  choice, and is left untouched.

## 8. Hypotheses certified for no `λ`

Three round-8/inherited predicates are hypotheses only.  No parameter is
exhibited satisfying any of them, and no statement in the tree should be read
as asserting that one exists:

| Predicate | File | Used by |
| --- | --- | --- |
| `KnotGame.KindWord` | `PeriodicYield.lean` | T23 |
| `KnotGame.KindDense` | `Density.lean` (inherited) | round 5, T26 |
| `KnotGame.KindDenseQuant` | `DensityQuant.lean` | T26 |
