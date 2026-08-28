import Mathlib

/-!
# Second cost experiment for Work Order 6: term size, not reduction steps

Not part of the `RequestProject` library and never built by `lake build`.

Here the state space is phrased the way Work Order 6 suggests — `Finset` over an
orbit type — with the derived `DecidableEq`/`Fintype` instances, and the closure
question is made as small as possible: only the `k + 1` configurations `∅` and
the singletons, and only one move.  Even so, `decide` fails by exhausting the
stack once `k` is moderately large, because of the size of the terms the
elaborator and kernel build while unfolding the instances.

Measured wall clock (`lake env lean experiments/PlasticFinsetCost.lean`,
including a ~9 s `import Mathlib` baseline):

| `k` | result                                     |
|-----|--------------------------------------------|
|   5 | succeeds, 10 s                             |
|  10 | succeeds, 32 s                             |
|  20 | **stack overflow, process aborted, 43 s**  |

Proposition 3.4 needs `k = 153` and 25 525 configurations.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PlasticFinsetCost

def stepF (k : ℕ) [NeZero k] (T : Finset (Fin k)) : Finset (Fin k) :=
  T.image (fun i => i + 1)

def reachF (k : ℕ) [NeZero k] : Finset (Finset (Fin k)) :=
  insert (∅ : Finset (Fin k)) (Finset.univ.image (fun i : Fin k => ({i} : Finset (Fin k))))

/-- Raise the two literals to `10` (slow) or `20` (stack overflow) to reproduce. -/
example : ∀ T ∈ reachF 5, stepF 5 T ∈ reachF 5 := by decide

end PlasticFinsetCost
