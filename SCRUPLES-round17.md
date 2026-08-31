# SCRUPLES — round 17 (T47, T48, T49)

Every convention, deviation and narrowing of this round, stated plainly.

## 1. T47

* **The statement is the commission's, letter for letter**, with the Greek
  `θ` written `th` (Greek identifiers are avoided in this file):

  ```
  no_contracting_weight (h : 1 < lam) (h2 : lam < 2)
      (w : ℝ → ℝ) (th : ℝ) (hth : th < 1)
      (hw : ∀ x ∈ Ioo (0:ℝ) 1, 1 ≤ w x) :
      ¬ (∀ x ∈ Ioo (0:ℝ) 1, ∀ m : Move, survives lam m x → w (act lam m x) ≤ th * w x)
  ```

* **The hypothesis `1 ≤ w x` is what makes the statement false rather than
  merely useless**, as the commission asked to be recorded. Drop it and take
  `w = fun _ => 0`, or any weight with `inf w = 0` on the orbit: the
  contraction condition is then satisfiable and no contradiction is available.
  What the proof uses is only that `w` is bounded below by a positive constant
  on `(0,1)`; `1` is that constant, and any other positive constant would do
  after rescaling.

* **No sign hypothesis on `th`.** The commission's statement has only
  `th < 1`, and negative `th` is handled separately (one step already forces
  `w` negative at a point where it must be at least `1`). The `0 ≤ th` branch
  is the iteration.

* **The orbit is built by the chosen move `nextMove x = if x < r lam then R
  else L`,** not by an arbitrary choice function; no choice principle is used
  to construct it. `orbit lam x` is a plain recursion on `ℕ`. This is a
  strengthening of what the argument needs — a *specific* infinite legal orbit
  is exhibited — and it is deliberate.

* **`lam < 2` is used, and is necessary for the route taken**: it is exactly
  `g lam < r lam` (`g_lt_r`), i.e. the two moves `R` and `L` between them cover
  `(0,1)`. Nothing is claimed for `lam ≥ 2`.

* **What is NOT claimed.** The paper's remark that the *collective* condition
  on configurations collapses to this pointwise one (because single-knot
  configurations are reachable) is a paper remark; it is not formalised here
  and no statement in the module mentions configurations.

## 2. T48

* **The equation is the content**, as the commission allowed: `P_id` is the
  identity `Contraction.P lam id = fun y => r lam * y + (1 - r lam)/2`, which
  holds for every real `lam` with no hypothesis at all (it is `ring` after
  unfolding). The hypothesis `1 < lam` appears only where positivity of
  `r lam` is needed, namely in `dist_P_id` and `not_lipschitzWith_P_id`.

* **Two sharpness forms are given.** `dist_P_id` states
  `dist (P lam id y) (P lam id z) = r lam * dist y z` — an equality, so it
  simultaneously re-proves the upper bound and rules out any better one.
  `not_lipschitzWith_P_id` spells out the consequence for `LipschitzWith K`
  with `(K : ℝ) < r lam`, matching the shape of
  `Contraction.lipschitz_contraction`.

* **`id` versus `fun y => y`.** The statement uses `id`; the identity is
  `Function.id`, and `Contraction.P lam id` elaborates without coercion. The
  seminorm the paper contracts is the Lipschitz seminorm, and the identity has
  seminorm `1`, so `r lam` is attained; this is what "best possible" means
  here, and no claim is made about the operator norm on any other space.

* **Paper edit made due.** The appendix's "sharpness remains unformalised"
  should now come out; the handoff section records this.

## 3. T49

* **`1 < lam` is dropped from `not_denseFrom_half_of_finite`.** The commission
  anticipated this: the bridge used is
  `BackwardClosure.denseFrom_half_imp_kindDense`, the direction of round 15's
  equivalence that carries no hypothesis on `lam`. The `iff`
  (`denseFrom_half_iff_kindDense`) is therefore not used at all. Both
  Pisot-level corollaries take `IsPisot lam`, which contains `1 < lam` anyway.

* **`Orb` and the endpoint set of `KindDense` are literally the same data.**
  `mem_orb_iff` is `Iff.rfl`: both are stated through `survivesWord` and
  `posAfter` from `1/2`. So no bridging lemma with content was needed between
  `Orb` and `KindDense`, and neither definition was duplicated or edited. A
  bridge *is* needed between `KindDense` and `DenseFrom` (branch words and
  `rapp`), and it is the inherited one named above.

* **Finiteness is measured with `Set.Finite.toFinset`**, so the pigeonhole is
  a `Finset.card` argument. No use is made of `Set.ncard`, and no relation is
  asserted between this argument and round 16's explicit cardinality bound
  (`PisotSeparation.orb_ncard_le_of_conj_le`), which is neither imported nor
  needed: `orb_finite` alone is the input.

* **What is NOT claimed.** That the density criterion fails says nothing about
  whether `N lam` is bounded at a Pisot parameter — that is
  `PisotDecide.N_le_card_orb`, an inherited and independent result. The
  failure of a sufficient condition for unboundedness is not evidence for
  boundedness, and the module asserts no such thing. Nothing here bears on
  non-Pisot parameters, and nothing bears on Question 50.

## 4. Conventions common to the round

* One module, `RequestProject/Closures17.lean`, namespace
  `KnotGame.Closures17`, holding all three items. Names are qualified by that
  namespace, so `orbit`, `nextMove` and `P_id` do not collide with anything in
  `KnotGame` or in Mathlib.
* `Ioo` is `Set.Ioo` (the file opens `Set`). Intervals are open, matching the
  strict inequalities the game uses throughout.
* No `sorry`, no `admit`, no added `axiom`, no `@[implemented_by]`, no
  `decide` and no `native_decide` in the round's source. No parameter-specific
  numerical claim is made anywhere in the round, so no arithmetic done by hand
  needs flagging.
* Only `RequestProject.Closures17` was built (its dependencies were built as
  part of that target). The union was not built and no tree-wide audit was
  run.
