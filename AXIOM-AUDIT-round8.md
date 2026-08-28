# AXIOM AUDIT — round 8

## 1. The tree-wide audit

`RequestProject/AxiomAudit.lean` walks every theorem in the environment reachable
from `RequestProject.All` and fails the build if any of them depends on an
axiom outside the permitted list.  On the final round-8 tree the build reports

```
info: RequestProject/AxiomAudit.lean:20:0: axiom audit passed: 1198 theorems,
      axioms confined to [propext, Classical.choice, Quot.sound]
Build completed successfully (8087 jobs).
```

Counts through the round:

| Stage | theorems audited |
| --- | --- |
| inherited tree (end of round 7) | 1084 |
| + `Ternary`, `Mahler`, `PeriodicYield`, `KindTree`, `WindowSharp` | 1162 |
| + `Translation` | 1181 |
| + `DensityQuant` (final) | 1198 |

## 2. Source-level checks

* No `sorry` and no `admit` anywhere in `RequestProject/`.
* No `axiom` declaration was added; the only axioms in the transitive closure
  are Lean's/Mathlib's `propext`, `Classical.choice`, `Quot.sound`.
* No `native_decide`.  Every finite check in round 8 (`KindTree`,
  `WindowSharp`) is a kernel reduction: `decide`, `norm_num`, or `rfl` over
  exact rationals and finite lists.

Reproduce with

```
rg -n "sorry|admit|native_decide|^axiom " RequestProject/
lake build
```

## 3. Per-target `#print axioms`

Every round-8 headline statement, checked individually against
`import RequestProject.All`.  All twenty-three print the same list.

| Target | Constant | Axioms |
| --- | --- | --- |
| T22a | `KnotGame.Ternary.survives_iff_digit_ne` | `[propext, Classical.choice, Quot.sound]` |
| T22a | `KnotGame.Ternary.act_eq_ternary` | `[propext, Classical.choice, Quot.sound]` |
| T22a | `KnotGame.Ternary.step_ternary` | `[propext, Classical.choice, Quot.sound]` |
| T22a | `KnotGame.Ternary.exists_unique_fatal` | `[propext, Classical.choice, Quot.sound]` |
| T22a | `KnotGame.Ternary.dyadic_posAfter` | `[propext, Classical.choice, Quot.sound]` |
| `prop:itinerary` | `KnotGame.Ternary.itinerary_tsum` | `[propext, Classical.choice, Quot.sound]` |
| T22b | `KnotGame.Ternary.base32_tsum` | `[propext, Classical.choice, Quot.sound]` |
| T22b | `KnotGame.Ternary.digit_eq_eps_add` | `[propext, Classical.choice, Quot.sound]` |
| T22b | `KnotGame.Ternary.digit_eq_eps_add_strict` | `[propext, Classical.choice, Quot.sound]` |
| T22c | `KnotGame.Ternary.mahler_recursion` | `[propext, Classical.choice, Quot.sound]` |
| T22c | `KnotGame.Ternary.mahler_of_survives` | `[propext, Classical.choice, Quot.sound]` |
| T22d | `KnotGame.Ternary.unbounded_iff_mahler` | `[propext, Classical.choice, Quot.sound]` |
| T23 | `KnotGame.infinitelyManyKnots_of_kindWord` | `[propext, Classical.choice, Quot.sound]` |
| T23 | `KnotGame.N_unbounded_of_kindWord` | `[propext, Classical.choice, Quot.sound]` |
| T24a | `KnotGame.KindTree.card_kindWords_three_halves` | `[propext, Classical.choice, Quot.sound]` |
| T24b | `KnotGame.KindTree.card_kindWords_phi_add_three` | `[propext, Classical.choice, Quot.sound]` |
| T25 | `KnotGame.Transversality.witness_at_3339` | `[propext, Classical.choice, Quot.sound]` |
| T25 | `KnotGame.Transversality.witness_at_3343` | `[propext, Classical.choice, Quot.sound]` |
| T25 | `KnotGame.Transversality.transversality_fails_beyond_window` | `[propext, Classical.choice, Quot.sound]` |
| T25 | `KnotGame.Transversality.window_not_extendable` | `[propext, Classical.choice, Quot.sound]` |
| T25 | `KnotGame.Transversality.deriv_witness_at_3339` | `[propext, Classical.choice, Quot.sound]` |
| T26 | `KnotGame.d_le_pow` | `[propext, Classical.choice, Quot.sound]` |
| T26 | `KnotGame.N_unbounded_of_kindDenseQuant` | `[propext, Classical.choice, Quot.sound]` |

Reproduce by putting the `#print axioms` lines in a scratch file that imports
`RequestProject.All` and running `lake env lean` on it.

## 4. What the audit does *not* certify

It is a check on the *axioms*, not on the *statements*.  In particular it says
nothing about whether a hypothesis is ever satisfied.  Round 8 has three
statements that are conditional on hypotheses certified for no `λ`:

* `KnotGame.KindWord` (T23),
* `KnotGame.KindDense` (inherited) and `KnotGame.KindDenseQuant` (T26).

Their status is recorded in `SCRUPLES-round8.md` §6.
