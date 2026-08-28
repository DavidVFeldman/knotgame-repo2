# SCRUPLES — round 11

Every place where a round-11 Lean statement is not a literal transcription of
the paper, and every convention that had to be fixed.  Conventions inherited
from earlier rounds (the window open at both ends, survival by strict
inequalities, `g + r = 1`, "`N_λ` unbounded" written `∀ k, ∃ n, k ≤ N λ n`,
`K λ m` for the number of surviving branch words of length `m`, itineraries
indexed from `0`) are unchanged and are not repeated.  Each item also appears
in the docstring of the file it belongs to.

## 1. `lem:overlap` — the exact-overlap criterion (`Overlap.lean`)

* **One argument replaces the paper's two.**  The paper separates even and odd
  indices for `1/√2` and reduces modulo `2` for `2/3`.  The Lean proof runs a
  single divisibility argument for both: a non-zero `{0,±1}` polynomial has
  leading coefficient `±1`, hence is primitive; if it vanishes at `u`, Gauss's
  lemma makes an integer multiple of the minimal polynomial of `u` divide it in
  `ℤ[X]`; the leading coefficient of that divisor must then divide `±1`, which
  `2X² − 1` and `3X − 2` fail.  Same statement, different proof; flagged here
  because the paper's computations do not appear.
* **The class.**  `PMOne p` says every coefficient of `p` lies in `{0, 1, −1}`.
  The statements are for `p ≠ 0`; the zero polynomial vanishes everywhere and
  is excluded, as in the paper.
* **The positive half is stated as an identity, not as minimality.**
  `inv_phi_root` and `inv_rho_root` say `1/φ` and `1/ρ` *are* roots of
  `x² + x − 1` and `x³ + x² − 1`.  No claim is made that these are the minimal
  polynomials (they are, but nothing here needs it).
* **The consequence** the paper draws in Remark 12 — that at `λ = 3/2` and
  `λ = √2` distinct branch words of a common length separate a knot — is
  proved for words of *equal length* only (`branchIter_injective`); the paper's
  informal reading covers no more.

## 2. `cor:decide` — decidability at a Pisot parameter (`PisotDecide.lean`)

* **"Eventually periodic / decidable" is rendered as three separate clauses:**
  the reachable configurations form a finite set (`reachable_finite`), `N_λ` is
  *eventually constant* (`N_eventually_constant`), and its supremum is attained
  at a finite level (`sup_N_isGreatest`).  Eventual constancy is stronger than
  the paper's "eventually periodic", and follows because `N_λ` is monotone
  (round 1's `N_mono`) and bounded.
* **No algorithm is exhibited.**  "Computable by a finite search" is formalised
  as "the supremum is attained at some finite level `n₀`", which is what makes
  a search terminate; no `Decidable` instance and no executable procedure is
  produced, and none is claimed.  This is the one gap between the paper's
  wording and the Lean statement, and it is deliberate: the search itself is
  over real configurations and is not executable in Lean without the exact
  arithmetic model that `PlasticIndex.lean` builds by hand for one parameter.
* `reachable lam` is the set of `run lam w` over all finite words, i.e.
  configurations reachable **from the empty configuration**, which is the
  paper's meaning.

## 3. `prop:circle` — the circle normal form (`CircleForm.lean`)

* **The circle is its fundamental domain.**  `ℝ/ℤ` is represented by `[0,1)`
  through `Int.fract`; `rot θ x = fract (x + θ)` and
  `Dop λ y = fract (λ (fract y − g/2))`.
* **`Dop` is a total extension of the paper's partial `D`.**  On the surviving
  arc `(g/2, 1 − g/2)` it agrees with the paper's operator (`Dop_eq`); off that
  arc it is defined but meaningless.  This is what lets the three identities be
  equations between honest total functions.  Each identity is stated *for a
  knot that survives the move in question*, so the extension is never used.
* **The seam.**  The marked point is `0`; `card_marked` says the marked points
  (knots together with the seam) number one more than the knots, using that a
  knot is never at `0`.  The paper's phrasing "the number of knots is one less
  than the number of marked points" is the same statement read backwards.

## 4. `prop:immortal32` — immortal births (`Immortal.lean`)

* **Nothing is special to `λ = 3/2`.**  The proposition is proved for every
  `λ > 1` (`N_unbounded_of_immortal`) and then specialised
  (`N_unbounded_of_immortal_three_halves`).  The paper states it at `3/2` only.
* **Immortality is "survives every finite block".**  `ImmortalBirth λ v t` says
  the letter at `t` is `M` and, for every `n`, the knot born there survives the
  next `n` letters.  The paper's "the orbit meets no deleted interval" is the
  same condition read one move at a time.
* **The control alphabet.**  A control sequence is `ℕ → Move`, with `M` the
  birth move, under round 8's coding `L, M, R ↦ 0, 1, 2`; the paper writes
  elements of `{0,1,2}^ℕ` with digit `1` for the birth.
* The proof is the paper's: immortal knots are simultaneously alive and
  distinct (`lem:distinct`), which is exactly what the suffix decomposition
  `card_run` counts.

## 5. `prop:square`, `prop:squaresurv` — the binary square at `√2`
(`Square.lean`)

* **Indexing.**  `eps k` is the paper's `ε_{k+1}` and `orbit lam eps x n` is the
  paper's `x_n`, as everywhere else in this development.
* **A hypothesis the paper does not state.**  The unconditional identity is
  `two_mul_beta` : `2β_n = ε_{n+1} + α_{n+1}`.  The paper's `α_{n+1} = {2β_n}`
  and `ε_{n+1} = ⌊2β_n⌋` follow from it **exactly when `α_{n+1} < 1`**, i.e.
  unless the digits are `1` at every index of that parity class from `n+2` on
  (`alpha_eq_one_iff`).  In that degenerate case the fractional part is `0`,
  which is not `α_{n+1}`, so the hypothesis is necessary and not an artefact of
  the formalisation.  `alpha_lt_one` supplies it from a single vanishing digit.
* **`pos_eq` carries the hypothesis of `prop:itinerary`:** the orbit stays in
  `[0,1]`.  That is the same hypothesis the round-8 lemma `itinerary_tsum`
  needs, and the paper's derivation uses it silently.
* **The survival table is proved in two layers.**  `spares_zero_iff` /
  `spares_one_iff` hold for every `λ > 1`; the five region tables need
  `g < r/2`, i.e. `λ < 3/2`, and carry the relevant inequalities as
  hypotheses.  At `λ = √2` they hold.  `squaresurv` is then the paper's own
  phrasing in the coordinates `s_n`, `β_n`, and `no_spare_of_exceptional` is
  its "unless" direction verbatim.

## 6. `prop:kinddim` — the kind set at `λ = 3/2` (`KindDim.lean`)

* **Only half of the proposition is proved.**  Certified: `K_{3/2}` is Lebesgue
  null (`volume_K`) and `dimH K ≤ log 2 / log 3` (`dimH_K_le`).  **Not**
  certified, and **abandoned**: the matching lower bound, and the box dimension
  (upper or lower).  See `ABANDONED.md` §1.  The paper's "dimension exactly
  `log 2 / log 3`" is therefore *not* a theorem of this tree, and no statement
  in the tree may be read as one.
* **Cylinders are closed**, `[cval w, cval w + 3^{-|w|}]`.  This only makes `K`
  larger, so both certified statements are the stronger reading.
* **No self-similarity is used or asserted**; `E (n+1) ⊆ E n` is proved from the
  tree structure.
* The cylinder count `2^n` is round 8's `card_kindWords_three_halves` and is
  reused, not re-derived.

## 7. `prop:lowerbound`, `cor:recursive` — the record-length bounds
(`RecordLower.lean`)

* **An attainability hypothesis is added, and it is necessary.**  `d λ k` is
  `sInf {n | k ≤ N λ n}`, which is `0` when no run ever attains `k` knots.  So
  `d_λ(k) ≥ 2k − 1` is false as literally stated — take `λ ≥ 2`, where
  `N λ n = 1` for all `n ≥ 1`, and `k = 3`.  Both statements therefore carry
  `∃ n, k ≤ N λ n`, which is the paper's standing assumption that `d_λ(k)` is
  the length of an actual record run.
* **No truncated subtraction.**  `prop:lowerbound` is written
  `2 * k ≤ d λ k + 1`, and `cor:recursive` `d λ k + 2 ≤ d λ (k+1)`.
* **`cor:recursive` needs `k ≥ 1`.**  At `k = 0` the paper's inequality reads
  `d λ 1 ≥ 2`, which is false whenever a birth is possible at all (`d λ 1 = 1`).
* **The proof of `cor:recursive` is the paper's, in the counting form.**  The
  paper argues with birth times `t_1 < … < t_{k+1}`; the Lean proof instead
  chops the last two letters off a record word and shows this costs at most one
  surviving birth (`births_le_births_take_add_one`), which is the same fact
  about the spacing of births, phrased so that round 2's counting lemma applies
  directly.

## 8. The sharper rate at `λ = 3/2` (`ExpSharpest*.lean`)

* **What improves is the rate, not every value.**  `49 ^ ⌊m/16⌋ ≤ K_{3/2}(m)`
  (`fortynine_pow_le_K`).  Because the exponent is natural-number division, the
  new bound is *not* uniformly stronger than round 10's `26 ^ ⌊m/14⌋`: for
  small `m` the coarser division can favour either.  Both bounds are kept, and
  the comparison of *rates* is itself certified, in integer form
  (`sharpest_rate` : `26^16 < 49^14`, `sharpest_rate_vs_round7` :
  `15^16 < 49^12`) and in real form (`sharpest_rate_real`).
* **No sharpness.**  `49` is the largest multiplicity the search reached at
  length `16` (it fails at `50`), but that is a property of the search, not a
  certified maximum; the measured growth `≈ 4/3` is certified nowhere.
* **The certificate is checked in 41 groups of at most 50 cells**, spread over
  nine check files, because the kernel's working set for a single reduction
  over all 2 008 cells does not fit in memory; the data itself is split over
  nine files because one literal of that size does not elaborate.
* **The search is untrusted.**  `scripts/gen_expsharpest.py` (with
  `scripts/expcert_dfs.py`) merely writes the data; every cell is re-checked by
  the kernel over exact rationals with `decide +kernel`.
* **File naming.**  The `ExpSharpest*` docstrings describe themselves as a
  continuation of round 10's target T31, which is what they are; they are
  delivered in round 11.

## 9. Standing conventions, restated once

* All new material is in new files; the only inherited file edited is
  `RequestProject/All.lean`, and only to add imports.
* Every public theorem of the `KnotGame` namespace is inside the semantic axiom
  audit run by `lake build`; see `AXIOM-AUDIT-round11.md`.
* Nothing in `scripts/` is trusted; nothing in `experiments/` is built.
