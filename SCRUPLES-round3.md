# SCRUPLES — round 3

Every place where the Lean statement is not a literal transcription of the
commission, with the reason.

## T8

1. **"Maximum exactly 3 / exactly 4."**  Formalised as
   `IsGreatest (Set.range (N lam)) 3` (resp. `4`): the value is attained (by an
   explicit run) and dominates every `N lam n`.  This is the round-1 form of
   the golden-ratio statement, unchanged.

2. **"20 (resp. 412) reachable configurations."**  For tribonacci this is the
   literal statement `reach.card = 20` together with closure under the three
   moves (`reach_closed`) and the fact that every run lands in `reach`
   (`absRun_mem_reach`); so `reach` is exactly the reachable set.  For
   supergolden the 412 configurations are the entries of the list `reachD`, and
   what is *certified* about that list is what the argument consumes: closure
   under the moves, `card ≤ 4`, and the depth constraints — all inside the
   single boolean `checkOK`.  That `reachD` has no repetitions, and that every
   entry is genuinely reachable, are not asserted.

3. **Orbit points.**  `p : Fin 7 → ℝ` (resp. `Fin 43 → ℝ`) is defined by
   explicit coordinates over `ℤ[λ]` with denominator `2`; injectivity
   (`p_injective`, via `p_strictMono` in the supergolden case) is proved from
   the rational brackets on `λ`.  That these are *all* the points of the orbit
   of `1/2` is delivered by the closure lemma `step_image` plus
   `run_eq`/`card_run_eq`: every reachable configuration is an image under `p`.

4. **`d(k)`.**  `d lam k` is the round-1 definition `sInf {n | k ≤ N lam n}`;
   the theorems `d_one`, …, `d_four` are equalities of natural numbers.

## T9

1. **The class.**  `𝓑₀₁` is formalised through a coefficient function
   `c : ℕ → ℤ` with `c 0 = 1` and `c i ∈ {−1,0,1}`; both finite and infinite
   sequences are covered, since a finite sequence is one that is eventually
   `0`.  The value is the `tsum` `gval c x`, which converges on the window.

2. **`g′`.**  The main theorem `transversality` is stated for the termwise
   derivative series `gder`.  `hasDerivAt_gval` proves that on `(−4/5, 4/5)`
   this series *is* the derivative, and `transversality_deriv` restates the
   conclusion for `deriv (gval c)`; the two forms are therefore equivalent on
   the window.

3. **The window and the constant.**  `x ∈ [1/2, 667/1000]` and `δ = 1/1000`
   exactly as commissioned.  The truncation depth is `Dep = 48` and the cell
   endpoints are integers over the common denominator `Qn = 1024000000`; all
   checker arithmetic is on `ℕ` with an offset for signs, which is the exact
   rational arithmetic the commission asked for, cleared of denominators.

4. **The certificate.**  27 cells, each closed by `decide +kernel`.  The cell
   list is a Lean definition (`cells`); `cells_chain`/`cells_lastEnd` prove
   that the cells tile the window, so nothing about the decomposition is taken
   on trust from the generating script.

## T10

1. **Ordered and unordered pairs.**  The note counts unordered pairs
   `{ε, ε'}`.  `sum_volume_close_le` and `lintegral_pairCount_le` count ordered
   pairs `(ε, ε')` with `ε ≠ ε'`, and carry a constant exactly twice the note's;
   `sum_volume_close_le_unord` sums over one representative of each unordered
   pair (`unordPairs`, the ordered pair carrying `false` at the first
   disagreement) and carries the note's own constant
   `4λ₀/(δ(λ₀−1)(2−λ₀))`.  The per-pair bound `volume_close_le` is insensitive
   to the distinction and matches the note.

2. **The window.**  The note's `I = [1/x₁, 1/x₀]` is instantiated at the window
   certified by T9: `I = [1000/667, 2]` (`Iwin`), `λ₀ = 1000/667` (`lam0`),
   `δ = 1/1000`.  The statements are therefore about the concrete certified
   window, not about an abstract transversality hypothesis.

3. **"For every ρ > 0."**  Proved for every `ρ ≥ 0`.  When `ρ` is so large that
   the claimed bound exceeds the length of `I`, the bound is trivial and the
   proof says so; the transversality argument is used only in the regime
   `ρ/((λ₀−1)λ₀^{m−k}) ≤ δ`.

4. **No change of variables.**  The note passes from `x` to `λ` with a
   Jacobian.  The Lean proof instead bounds the *diameter* of the small-value
   set (`sub_le_of_transversal`) and uses that `x ↦ 1/x` distorts distances on
   `I` by at most the factor `4`; `volume_le_of_width` then converts a diameter
   bound into a measure bound.  The resulting constant is the note's.

5. **The pair count.**  The note's exact count `2^{k−1}4^{m−k}` of unordered
   pairs with first difference at `k` is replaced by the *upper bound*
   `2^m · 2^{m−k}` on the number of ordered such pairs (`fiber_card_le`),
   proved by an injection `(ε, ε') ↦ (ε, ε'|_{>k})`.  The bound is the exact
   count, but only the inequality is certified — which is all the estimate
   needs.

6. **The endpoint family.**  `Phi m e l` is `Φ_ε(λ)` with the negative powers
   cleared: `λ^m/2 − (λ−1)∑_{j=1}^m ε_j λ^{m−j}`.  Branch words of length `m`
   are `Fin m → Bool`, read on the indices `1, …, m` by `wext`.

7. **What is *not* claimed.**  The pair-counting estimate is a statement about
   the difference class only; nothing here concerns the survival constraint of
   the game, and item (iii) of the note's programme (the kind-constrained
   first-moment lower bound) is untouched.
