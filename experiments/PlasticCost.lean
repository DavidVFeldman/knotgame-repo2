import Mathlib
/-!
# Synthetic cost measurement for Work Order 6 (Proposition 3.4)

This file is *not* part of the `RequestProject` library (it lies outside the
`RequestProject.+` glob of `lakefile.toml`) and is never built by `lake build`.
It exists only to measure, empirically, how the cost of a kernel-checked
(`decide`) closure computation grows with the size of the state space, so that
`PLASTIC-REPORT.md` can quote real numbers rather than guesses.

The model is deliberately a *proxy*, not the plastic-number automaton itself:

* the orbit is modelled by `Fin k` (as a range of naturals `0, …, k-1`);
* a configuration is modelled by an unordered pair of distinct orbit points,
  so there are `k (k-1) / 2` configurations;
* each of the three moves is modelled by an affine map `x ↦ (2x + m) % k`;
* the check is that the image of every configuration under every move is again
  a configuration (or has collapsed to a single point).

The real Proposition 3.4 instance has `k = 153` orbit points and `25 525`
configurations, and the same shape of membership test.  Compile a single
instance with

```
lake env lean -DweakLeanTactics=false experiments/PlasticCost.lean
```

after setting `kSize` below, and time it with `/usr/bin/time`.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PlasticCost

/-- The `k (k-1) / 2` modelled configurations: ordered pairs `(i, j)` with
`i < j < k`. -/
def pairs (k : ℕ) : List (ℕ × ℕ) :=
  (List.range k).flatMap fun i =>
    (List.range k).filterMap fun j => if i < j then some (i, j) else none

/-- The image of a configuration under the `m`-th modelled move, normalised so
that the smaller coordinate comes first. -/
def mv (k m : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  let a := (p.1 * 2 + m) % k
  let b := (p.2 * 2 + m) % k
  if a ≤ b then (a, b) else (b, a)

/-- The closure predicate: every image is again a configuration, unless the two
knots have collided. -/
def closed (k : ℕ) : Bool :=
  (pairs k).all fun p =>
    [0, 1, 2].all fun m =>
      let q := mv k m p
      (q.1 == q.2) || (pairs k).contains q

/-- The size of the modelled state space, for the record. -/
def size (k : ℕ) : ℕ := (pairs k).length

end PlasticCost

/-- Change this constant and re-run to measure a different instance. -/
abbrev kSize : ℕ := 5

#eval (kSize, PlasticCost.size kSize, PlasticCost.closed kSize)

example : PlasticCost.closed kSize = true := by decide

/-
## Measurements (this machine, `lake env lean experiments/PlasticCost.lean`,
`maxHeartbeats 0`, wall clock including a ~9 s `import Mathlib` baseline)

| `kSize` | configurations | wall clock | net of baseline |
|---------|----------------|------------|-----------------|
|   5     |     10         |    10 s    |     ~1 s        |
|  10     |     45         |    12 s    |     ~3 s        |
|  20     |    190         |    27 s    |    ~18 s        |
|  40     |    780         |   335 s    |   ~326 s        |
|  60     |   1770         |  > 1200 s  |  (timed out)    |

Proposition 3.4 needs 25 525 configurations, i.e. 33x the largest instance that
completed here, with a cost that is growing at least quadratically and closer to
cubically in the number of configurations.
-/
