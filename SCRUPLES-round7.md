# SCRUPLES — round 7

Every place where the Lean statement is not a literal transcription of the
notes, and every convention that had to be fixed.  Conventions inherited from
earlier rounds (the window open at both ends, survival by strict inequalities,
`g + r = 1`) are unchanged and are not repeated.

## 1. The return-time tail bound

* **Deterministic, not probabilistic.**  The notes state the open item as
  `P_λ(S > t) ≤ C λ₀^{-t}`.  What is proved is a *Lebesgue measure* statement
  about one parameter at a time:

  ```
  return_time_tail :  1 < λ → λ² < λ + 1 →
      volume {x | x ∈ Window λ ∧ t < retTime λ x} ≤ ENNReal.ofReal (2 * g λ / λ^(t+1))
  ```

  No probability space is introduced, and there is no integration over a
  parameter window.  `return_time_tail_prob_three_halves` divides by the
  measure of the window at `λ = 3/2` and so is the normalized form
  `≤ (4/3)·(2/3)^t · volume (Window (3/2))`; the constant `4/3` sits beside the
  measured `≈1.3`, and `2/3 = λ⁻¹`, which is the measured rate.  This is a
  restatement, not an independent confirmation of the measurement.

* **`S` is the return time of the discarded child only.**  `dchild λ x` is the
  image of `x` under the branch *not* chosen by `cb`; `retTime λ x` is the least
  `t` with the `t`-fold forced image back inside the window, and it is defined
  as a `Nat.sInf`, hence `0` on the (empty, for window points) set where no
  return happens.  `retTime_spec` supplies the return for window points, so the
  junk value never enters a statement.

* **The tail set is a sublevel set.**  `lt_retTime_iff` says `t < retTime λ x`
  exactly when the discarded child lies within `λ^{-t}`-ish distance of `{0,1}`
  — this is the "lands within `λ^{-S}` of `{0,1}`" sentence of the notes made
  precise; the measure bound is then the length of two intervals.  The
  hypothesis `λ² < λ + 1` (i.e. `λ < φ`) is used exactly where the notes use it:
  it is what makes the forced orbit enter the window rather than cross it.

## 2. The renewal inequality

* **Replaced, not proved.**  The notes' inequality
  `K_m ≥ K_{m-1-B} + Σ_t p_t K_{m-1-t}` is a statement about the empirical
  return-time law `p_t`, and its growth rate is not available in closed form.
  Round 6 proves instead a deterministic renewal step,

  ```
  two_mul_kappa_le :  Doubling λ a b T → 2 * kappa λ a b n ≤ Kx λ x (n + T)
  ```

  for every `x ∈ [a,b]`, where `kappa λ a b n` is the minimum over `[a,b]` of the
  number of surviving words of length `n`.  Iterating it gives `2^j` after `T·j`
  steps.  The two statements are different; the deterministic one is what the
  exponential bound actually rests on, and it uses no measured quantity.

* **Why doubling suffices.**  Absorption (`bSurvives_of_image_mem`) says a
  branch word issued from `x ∈ (0,1)` is legal **iff** its final image is again
  in `(0,1)`.  So a certificate only has to control images, never legality; this
  is the one structural simplification the whole round rests on.

## 3. The exponential lower bound for `K_m`

* **The route is a covering argument, not the return-time renewal.**  Nothing in
  `ExpCount`/`ExpCert`/`ExpLower`/`ExpWindow` depends on `ReturnTail`.  The two
  halves of the round are independent; the open item "the tail bound is what is
  missing for the exponential theorem" is therefore answered by *bypassing* it.

* **Natural division.**  `2 ^ (m / T) ≤ K λ m` uses `Nat` division: only the
  branchings completed in the first `T·(m/T)` steps are counted, and the bound
  is trivial (`= 1`) for `m < T`.

* **Multiplicity.**  Nothing in the argument is special to *two* returning
  words: `RequestProject.ExpMulti` runs it with `k` of them and concludes
  `k ^ (m/T) ≤ K λ m`.  At `λ = 3/2`, `15` words of length `12`
  (`ExpSharp.fifteen_pow_le_K`) give `15^(1/12) ≈ 1.2532` per step.  The
  multiplicity `15` is what a greedy search reached; it is not claimed maximal,
  and the two `3/2` statements (`ExpLower.two_pow_le_K` and
  `ExpSharp.fifteen_pow_le_K`) are kept side by side because neither dominates
  the other for every single `m` (the divisions are `m/5` and `m/12`).
* **The rates are not optimal.**  At `λ = 3/2` the first certificate gives
  `2^(1/5) ≈ 1.1487` per step and the sharper one `15^(1/12) ≈ 1.2532`; on the
  window the certificate gives `2^(1/8) ≈ 1.0905`.  The
  measured growth is `(2/λ)^m`, i.e. `≈1.333` at `3/2`.  No claim of sharpness is
  made, and the true counts (`2, 2, 4, 6, 8, 10, 12, 18, 24, 28, …` at `3/2`)
  comfortably exceed the certified bound.

* **The interval `J`.**  The doubling interval is `[1/4, 3/4]` at `3/2` and
  `[1/5, 4/5]` uniformly on the window.  Both are closed, contain `1/2`, and lie
  in `(0,1)`; both are *wider* than the window `(g, r)` of the game.  This is
  legitimate — the argument only needs an interval inside `(0,1)` containing the
  starting point `1/2` — but it means `J` is not the game's window and should not
  be read as one.

* **The parameter window is covered exactly.**  `two_pow_le_K_window` assumes
  `1000/667 ≤ λ ≤ 8/5`, with both endpoints included: `chained` requires the last
  parameter cell to reach `8/5`, and `exists_cell` covers the closed interval.
  The search did **not** find certificates with `T ≤ 8` beyond `8/5` (near
  `λ = 1.61` the required word length rises to about `10` and the number of cells
  by an order of magnitude), so the window stops there rather than at `φ`.

* **What the certificate is checked against.**  `iok` runs a one-sided interval
  enclosure — the lower end of the image depends only on the cell's lower end and
  the upper end only on its upper end, for both branch maps — over *exact
  rationals*, simultaneously for all `λ` in the parameter cell.  Its soundness is
  the Lean lemma `rapp_mem_of_iok`; the numeric data itself is checked by
  `decide +kernel`, so the search programs in `scripts/` are not trusted.

* **The window bound was not upgraded to higher multiplicity.**  The same
  search over the parameter window with `k = 3` succeeds (word lengths `8`–`10`,
  about `5600` cells) and would give `3^(1/10) ≈ 1.1161`; it is not shipped,
  because the kernel check would dominate the build for a small gain.  What is
  shipped for the window is the multiplicity-two certificate.
* **`maxHeartbeats` in the generated files.**  `ExpWindowData.lean` raises
  `maxHeartbeats` to `1000000` because elaborating 1333 rational cells exceeds
  the default budget.  This affects elaboration time only; no `set_option`
  weakens any check, and no `native_decide` is used anywhere.  For the same
  reason the cells of `ExpSharpData.lean` are shipped in groups of `100` and the
  kernel checks one group at a time: a single reduction over all `503` cells
  does not go through.
