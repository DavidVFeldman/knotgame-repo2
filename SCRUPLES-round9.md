# SCRUPLES — round 9

Every place where a round-9 Lean statement is not a literal transcription of
the paper, and every convention that had to be fixed.  Conventions inherited
from earlier rounds (survival by strict inequalities, `g + r = 1`, `N_λ`
unbounded written `∀ K, ∃ n, K ≤ N λ n`, 0-based control indexing in
`Translation.lean`) are unchanged and not repeated.  Each item also appears in
the docstring of the file it belongs to.

## 1. T27 — immortal births (`prop:immortal32`)

* **"Immortal" is the horizon-free avoidance condition.**  `Translation.lean`
  states avoidance only up to a finite horizon, `MahlerAlive c b N`.
  `Ternary.MahlerImmortal c b` is the same condition with the horizon removed:
  `∀ i, ⌊(3/2) · w_i⌋ ≠ c (b+1+i)`, where `w_i = witer c (b+1) 1 i`.  The
  implication `MahlerImmortal → ∀ N, MahlerAlive … N` is `mahlerAlive_of_immortal`.
* **Index convention.**  As in `Translation.lean`, `c j` is the letter applied
  between times `j` and `j+1`, so a birth at *letter* `b` (`c b = 1`) is a knot
  at *time* `b+1` driven by `c (b+1), c (b+2), …`.  The paper indexes from `1`,
  where letter and time carry the same number.  The two conventions describe
  the same object.
* **"Infinitely many `t`" is `Set.Infinite`.**  The hypothesis is
  `{b | c b = 1 ∧ MahlerImmortal c b}.Infinite`.  From it, `Nat.nth` selects
  `k` distinct immortal births below a common index for every `k`; that is
  exactly the input `unbounded_iff_mahler` wants.
* **`lem:distinct` is not re-proved.**  The paper's "distinct births give
  distinct knots" is already inside `unbounded_iff_mahler`
  (`card_birthSet` + `card_run`).  T27 adds no new bookkeeping; it is the
  two-line proof of the paper, and no more.
* **Two forms of the control.**  The main statement takes `c : ℕ → ℤ` with
  `∀ j, c j = 0 ∨ c j = 1 ∨ c j = 2`, matching `Translation.lean`.
  `unbounded_of_infinite_immortal_fin` is the same statement for
  `c : ℕ → Fin 3`, which is the paper's phrasing.
* **`N_{3/2} = ∞` is rendered `∀ K, ∃ n, K ≤ N (3/2) n`,** as everywhere in
  this development.

## 2. T28 — the caption of Figure `fig:records32`

* **Scope guard — the important one.**  All six/seven statements are about the
  **exhibited configurations only**.  Nothing in `RecordGaps.lean` asserts
  * that `record1, …, record7` are the only record words,
  * that their lengths are the minimal depths `d_{3/2}(k)` (minimality is
    certified only for `k ≤ 4`, in the inherited `RecordDepths.lean`), or
  * that these configurations exhaust the records at their depth.

  Exhaustiveness for `prop:twostep` is explicitly **not** commissioned and is
  **not** proved.  The docstring of `RecordGaps.lean` says this in the same
  words.
* **`record1` is new.**  `TwoStep.lean` exhibits records for `k = 2, …, 7`
  only.  To cover all seven values of the caption, the one-move word
  `record1 = [M]` is added here, with `runZ_record1 = {1}`,
  `card_run_record1 = 1` and the depth bound `d_{3/2}(1) ≤ 1`.  The bound is
  stated as `≤`, not `=`: `d_{3/2}(1) = 1` would need `d_{3/2}(1) ≠ 0`, which
  is a separate (easy, but uncommissioned) fact.
* **"Minimum gap `δ`, realised by `(a,b)`" is packaged, not computed.**
  `IsMinGapAt S δ a b` says: `a ∈ S`, `b ∈ S`, `b − a = δ`, and every two
  distinct points of `S` are at distance at least `δ`.  That is exactly the
  caption's assertion.  No `minGap : Finset ℝ → ℝ` function is introduced, so
  no new definition has to be reconciled with anything else in the tree.
  The realising pair is *ordered*: the statements assert `b − a = δ` with
  `a < b`, which is why claim (c) is recorded as `(243/512, 1/2)` at
  `k = 4, 6` and `(1/2, 269/512)` at `k = 5, 7` — the caption's own pairs.
* **Everything is a kernel computation over exact integers.**  A configuration
  after a word of length `j` is `{A/2^j : A ∈ runZ w}` (`run_eq_image_runZ`,
  inherited).  Membership of `1/2` is `2^{j-1} ∈ runZ w`, and "no two points
  closer than `D/2^j`" is a decidable statement about `runZ w ⊆ ℤ`.  The two
  bridges `mem_run_of_emb_eq` and `gap_lower_bound_of_runZ` are the only real
  content; the rest is `decide` (with `maxRecDepth` raised).  No
  `native_decide`.
* **The gap constants in integer form.**  `1/8` at lengths 3 and 5 is `D = 1`
  and `D = 4`; `13/512` at lengths 9, 19, 23, 52 is `D = 13`, `13312`,
  `212992`, `114349209288704` respectively.  These are the same rational in
  each block, written over the denominator of the corresponding word length.

## 3. T29a — the Fourier floor at `φ` (paper §11)

* **The measure `ν_r` is not constructed.**  `cosProd rr ξ` is *defined* to be
  the cosine product `∏'_{j≥0} |cos(π (1−rr) rr^j ξ)|`, the classical closed
  form of `|ν̂_{rr}(ξ)|` for the Bernoulli convolution.  Every statement is
  about that product.  **Nothing asserts the identification with the Fourier
  transform of a measure**; constructing the Bernoulli convolution and proving
  its transform formula is not part of the commission, and would be a
  substantial separate development.
* **Rendering of the two-sided product (the commission asks for this choice to
  be recorded).**  It is Mathlib's unconditional `∏' m : ℤ, goldenFac m`
  (`tprod`), and convergence is `Multipliable goldenFac`.  The route is
  log-summability, not `HasProd` directly:
  1. every factor is positive (`goldenFac_pos`, from the irrationality of
     `φ^m` for `m ≠ 0`);
  2. `1 − |cos(π φ^m)| ≤ π² ‖φ^m‖²/2` and `‖φ^m‖ ≤ φ^{−|m|}` give
     `|log goldenFac m| ≤ π² (φ^{−2})^{|m|}` once the right-hand side is `≤ 1`
     (`abs_log_goldenFac_le`);
  3. the two one-sided geometric bounds give `summable_log_goldenFac` over `ℤ`
     (`Summable.of_nat_of_neg_add_one`);
  4. `Real.multipliable_of_summable_log` yields `Multipliable`, and
     `Real.rexp_tsum_eq_tprod` yields `∏' = exp (∑' log) > 0`.

  So **positivity is not a separate analytic argument**: it is exactly the
  statement that the product is an exponential.  This is the "elementary
  log-summability argument" option the commission allows.
* **The negative tail is not "trivial by `φ^m → 0`" in the same way.**  For
  `m ≤ 0` the factors tend to `|cos 0| = 1`; the quantitative bound used is
  the same one, with `‖φ^m‖ = φ^m ≤ φ^{−|m|}` for `m ≤ 0`.  Both tails are
  therefore handled by a single geometric estimate in `φ^{−2}`.
* **Which distance bound is proved.**  `Lucas.lean` proves the *exact*
  identity `|φ^m − L_m| = (φ^{−1})^m` for all `m : ℕ`
  (`abs_goldenRatio_pow_sub_lucas`), and derives the nearest-integer form
  `‖φ^m‖ ≤ (φ^{−1})^m` (`abs_goldenRatio_pow_sub_round_le`) from it.  The
  paper states this for `m ≥ 2`; the identity form holds for all `m ≥ 0`, and
  is what the analytic estimates use.
* **`lucas` is defined here.**  Mathlib has `Nat.fib` but no Lucas sequence;
  `Fourier.lucas : ℕ → ℤ` is defined by the recursion `2, 1, L_{n+2} = L_n +
  L_{n+1}` and the trace identity `φ^m + ψ^m = L_m` is proved by two-step
  induction from `Real.goldenRatio_sq` and `Real.goldenConj_sq`.
* **The limit (iv).**  `tendsto_cosProd_xi_golden` says
  `cosProd (r φ) (xi φ N) → ∏' m : ℤ, goldenFac m` as `N → ∞`, along the
  filter `atTop` on `ℕ`.  By (i) the left-hand side is
  `∏'_{j : ℕ} |cos(π φ^{N−j})|`, the paper's `∏_{m ≤ N} |cos(π λ^m)|`.
  The proof splits `∑'_{m ∈ ℤ} log` into a head and a tail and uses that the
  tail of a summable series tends to `0`.
* **Reflection and the square form.**  `goldenFac_neg_natCast` records
  `|cos(π φ^{−k})| = |cos(π φ^{k})|` (because `φ^k` and `(−1)^k φ^{−k}` differ
  by the integer `L_k`), and `goldenFourierFloor_eq_sq` rewrites the two-sided
  product as the square of its one-sided half.  These are not part of the
  commissioned list; they are recorded because they are the shape any
  numerical enclosure (T29b) would use.
* **`xi_scaling` and `cosProd_xi` are proved for every `λ > 1`,** not only at
  `φ`; only the convergence statements are golden-specific.

## 4. Conditional statements and what the audit does not certify

Round 9 introduces one hypothesis that is certified for no explicit control:
`Ternary.MahlerImmortal`.  `unbounded_of_infinite_immortal` is a genuine
implication, but **no control `c` is exhibited with infinitely many immortal
births** — that is the open problem the paper is describing, not a gap in the
formalisation.  This is the same status as the inherited `KindWord`,
`KindDense`, `KindDenseQuant` hypotheses (see `SCRUPLES-round8.md` §6).

## 5. T29b (optional) — the certified enclosure: delivered

The target is `∏_{m∈ℤ} |cos(π φ^m)| ∈ [66/10⁴, 67/10⁴]` (measured
`6.6135 × 10⁻³`).  It **is** proved, in `RequestProject/FourierEnclosure.lean`,
as `goldenFourierFloor_enclosure`.  How it is done, and where the rendering
deviates from the obvious reading:

* **Shape.**  By `goldenFourierFloor_eq_sq` the target is `Q²` with
  `Q = ∏_{k≥1} |cos(π φ^{−k})|`.  The file proves the sharper intermediate
  statement `tprod_neg_enclosure`: `813199/10⁷ ≤ Q ≤ 813281/10⁷`.  Squaring
  gives `0.0066129 ≤ ∏ ≤ 0.0066143`, comfortably inside the commissioned
  window; the commissioned window is what the headline theorem states.
* **The cosine bound is new infrastructure, built here.**  Mathlib's
  `Real.cos_bound` (order 4, error `5|x|⁴/96`) is far too coarse.  Instead
  `cos_taylor_err` proves the degree-8 alternating-series bound
  `|cos x − (1 − x²/2 + x⁴/24 − x⁶/720 + x⁸/40320)| ≤ x¹⁰/10!` for every
  `x ≥ 0` with `x² ≤ 2`, from `Real.cos_eq_tsum` and Mathlib's
  `alternating_series_error_bound` (the terms `x^{2i}/(2i)!` are antitone
  exactly because `x² ≤ 2`).  This is *not* the `Complex.exp_bound` route
  costed in the earlier draft of this section; the alternating-series route is
  shorter and gives a smaller error.
* **Only twelve factors are evaluated, and only eleven distinct ones.**
  `φ^{−1} + φ^{−2} = 1`, so `|cos(π φ^{−1})| = |cos(π φ^{−2})|`
  (`goldenFac_neg_one_eq`); this also keeps every evaluated argument at most
  `1.2 < √2`, inside the range where the Taylor bound applies.  The twelve
  factors are enclosed to `10⁻⁶` (`fac1 … fac12`), the arguments being enclosed
  from `φ⁻¹ ∈ [0.618033988, 0.618033989]` and `π ∈ [3.141592, 3.141593]`
  (Mathlib's `pi_gt_d6`, `pi_lt_d6`) and `cos` being decreasing on `[0, π]`.
* **The tail is the round-8 estimate.**  `abs_log_goldenFac_le` gives
  `|log|cos(π φ^{−k})|| ≤ π²(φ^{−2})^k`, and the geometric sum beyond `k = 12`
  is at most `6·10⁻⁵`; hence the tail product lies in `[1 − 6·10⁻⁵, 1]`.  The
  split of the product into head and tail is done on the logarithms
  (`Summable.sum_add_tsum_nat_add`), since `ℝ` under multiplication is not a
  group and Mathlib's `tprod` splitting lemma does not apply.
* **Every numerical step is exact rational arithmetic** discharged by
  `norm_num` in the kernel: no floating point, no `native_decide`, no external
  certificate.  The decimal figures quoted in this document are only
  commentary; the Lean statements carry the exact rationals.
* **What is not claimed.**  The enclosure is an enclosure, not an evaluation:
  nothing asserts the value `6.6135 × 10⁻³` itself, and no sharpness or
  optimality of the window is claimed.

## 6. T29c (optional) — the other parameters: all three delivered

The commission asks for per-parameter reports, and allows attempting T29c only
after T29a.  All three parameters are done: the **plastic number**
(`RequestProject/PlasticFourier.lean`), the **supergolden ratio**
(`RequestProject/SupergoldenFourier.lean`) and the **tribonacci constant**
(`RequestProject/TribonacciFourier.lean`).

### 6.1 Plastic (`ρ³ = ρ + 1`): delivered

* **The general engine.**  Rather than copying `FourierFloor.lean`, round 9
  isolates what the golden argument actually uses into the structure
  `ConjApprox lam` of `RequestProject/FourierGeneral.lean`: a constant `C`, a
  rate `t ∈ (0,1)`, the hypothesis `∀ m : ℤ, ∃ n : ℤ, (λ^m − n)² ≤ C t^{|m|}`,
  and the hypothesis that no `cos(π λ^m)` vanishes.  From those two inputs the
  file re-proves convergence, positivity and the `ξ_N` limit.  **The golden
  case is not re-derived through it**; `FourierFloor.lean` is untouched.
* **The distance bound avoids the complex conjugates entirely.**  The earlier
  draft of this section costed the plastic case as "name `α` explicitly and do
  a three-step induction in `ℂ`".  That is not what was done.  With
  `e_m = ρ^m − P_m` (`P` the Perrin sequence `3, 0, 2, …`), the *real*
  identity `e_{m+2} = −ρ e_{m+1} − (ρ²−1) e_m` is proved by a three-step
  induction inside `ℝ` (`perr_add_two`), and the quadratic form
  `Q_m = e_{m+1}² + ρ e_{m+1} e_m + (ρ²−1) e_m²` — positive definite because
  `3ρ² > 4` — satisfies `Q_{m+1} = (ρ²−1) Q_m` exactly.  Since
  `Q_0 = 3ρ² − 4 = 4·((3/4)ρ² − 1)`, the constants cancel and the bound is the
  clean `e_m² ≤ 4 (ρ²−1)^m` (`perr_sq_le`).  No complex number appears in the
  file, and `Plastic.lean`'s factorisation over `ℂ` is not used.
* **The bound is stated for the square of the distance.**  `ConjApprox` asks
  for `(λ^m − n)² ≤ C t^{|m|}` rather than `|λ^m − n| ≤ C t^{|m|/2}`; the
  deficit estimate `1 − |cos(π d)| ≤ π² d²/2` consumes exactly the square, and
  this keeps `√` out of the development.  At the plastic number `C = 4` and
  `t = ρ² − 1 = ρ^{−1} ≈ 0.7549`.
* **Positivity of the factors needs a finite check** (at `φ` it came free from
  irrationality).  For `m ≥ 10` the distance bound already excludes
  `ρ^m ∈ ℤ + ½`, because `4(ρ²−1)^{10} < 1/4`.  The exponents `m = 0, …, 9`,
  and the negative exponents (where `ρ^m ∈ (0,1)` and only `½` is at risk), are
  settled by rational enclosures of `ρ` in the kernel — `ρ ∈ [1.3247179,
  1.3247180]`, obtained from `ρ³ = ρ + 1` by an explicit factorisation, not by
  any external computation.  The relevant lemma is
  `cos_pi_ne_zero_of_between`: if `2x` lies strictly between two consecutive
  integers then `x` is not a half-integer.
* **What is *not* claimed at the plastic number.**  No numerical enclosure of
  the plastic Fourier floor (the analogue of T29b) is proved; nothing is
  claimed about its value beyond positivity.  The Perrin sequence is used as a
  *definition*; the statement "`P_m` is the trace `ρ^m + α^m + ᾱ^m`" is not
  formalised, and is not needed — the file only ever uses the recurrence and
  the three initial values.

### 6.2 Supergolden and tribonacci: delivered, by the same skeleton

An earlier draft of this section costed these two as "not attempted", on the
ground that neither `Supergolden.lean` nor `Tribonacci.lean` carries a
factorisation over `ℂ` or a conjugate bound.  That turned out to be the wrong
way round: the plastic route never uses the complex conjugates either, so
nothing had to be redone — only the parameter-specific input had to be
supplied.  Both files are therefore near-clones of `PlasticFourier.lean`:

| | plastic `ρ` | supergolden `ψ` | tribonacci `τ` |
| --- | --- | --- | --- |
| minimal polynomial | `x³ = x + 1` | `x³ = x² + 1` | `x³ = x² + x + 1` |
| trace `A_m` | `3, 0, 2`, `A_{m+3} = A_{m+1} + A_m` | `3, 1, 1`, `A_{m+3} = A_{m+2} + A_m` | `3, 1, 3`, `A_{m+3} = A_{m+2} + A_{m+1} + A_m` |
| error recurrence | `e_{m+2} = −ρ e_{m+1} − t e_m` | `e_{m+2} = (1−ψ) e_{m+1} − t e_m` | `e_{m+2} = (1−τ) e_{m+1} − t e_m` |
| rate `t = λ^{-1}` | `ρ²−1 ≈ 0.7549` | `ψ²−ψ ≈ 0.68233` | `τ²−τ−1 ≈ 0.54369` |
| `Q_0` (the discriminant) | `3ρ²−4` | `3ψ²−2ψ−1` | `3τ²−2τ−5` |
| distance bound | `e_m² ≤ 4 t^m` | `e_m² ≤ 4 t^m` | `e_m² ≤ 4 t^m` |
| finite half-integer check | `m = 0 … 9` | `m = 0 … 7` | `m = 0 … 4` |

In each case the rate is exactly `λ^{-1}`, so the negative exponents are powers
of `t` and the same two-line argument excludes half-integers there.  The
constant `4` is not a fudge: `Q_0` is precisely `−(p² + 4q)` for the recurrence
`e_{m+2} = p e_{m+1} + q e_m`, so it cancels against the positive-definiteness
constant and leaves the clean `e_m² ≤ 4 t^m`.

Two deviations to record.

* **The trace sequences are definitions, not identified with traces.**  As at
  the plastic number, `sgTrace` and `triTrace` are introduced by their
  recurrences and initial values; the statement "`A_m = λ^m + α^m + ᾱ^m`" is
  never formalised and is never needed.  Consequently nothing in these files
  depends on the two conjugates existing, let alone on their modulus.
* **The enclosures are inherited at the precision the inherited files give.**
  `Supergolden.lean` pins `ψ` to `10⁻⁷` and `Tribonacci.lean` pins `τ` to
  `10⁻⁴`; those are the enclosures used, and they are comfortably enough for
  the finite checks (the tightest margin is `τ⁴`, whose double is `22.885 …`,
  a distance `0.11` from the nearest integer against an interval of width
  `0.006`).

What is **not** claimed at either parameter, exactly as at the plastic number:
no numerical enclosure of the Fourier floor (the analogue of T29b), and no
statement about the Bernoulli convolution as a measure.
