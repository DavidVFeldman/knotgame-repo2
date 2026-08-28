# AXIOM AUDIT — round 4

Two independent checks, as in rounds 2 and 3.

## 1. The semantic audit run by the build

`RequestProject/AxiomAudit.lean` walks every constant of the environment in the
`KnotGame` namespace, computes its axiom set with the machinery behind
`#print axioms`, and fails the build if any axiom outside
`propext, Classical.choice, Quot.sound` occurs — in particular if `sorryAx`
does.  With round 4 in place `lake build` reports

```
axiom audit passed: 636 theorems, axioms confined to [propext, Classical.choice, Quot.sound]
```

(round 3 reported 524; the 112 further theorems are round 4's.)

## 2. Per-target `#print axioms`

```
'KnotGame.Branching.no_jump_low'                        [propext, Classical.choice, Quot.sound]
'KnotGame.Branching.no_jump_high'                       [propext, Classical.choice, Quot.sound]
'KnotGame.Branching.sharp_two_cycle'                    [propext, Classical.choice, Quot.sound]
'KnotGame.Branching.good_child'                         [propext, Classical.choice, Quot.sound]
'KnotGame.Branching.bounded_return_low'                 [propext, Classical.choice, Quot.sound]
'KnotGame.Branching.bounded_return_high'                [propext, Classical.choice, Quot.sound]
'KnotGame.Branching.continuum_of_survival_itineraries'  [propext, Classical.choice, Quot.sound]
'KnotGame.Branching.theta_injective'                    [propext, Classical.choice, Quot.sound]
'KnotGame.Branching.theta_surviving'                    [propext, Classical.choice, Quot.sound]
'KnotGame.Branching.K_ge'                               [propext, Classical.choice, Quot.sound]
'KnotGame.Branching.K_eq_card_bSurvives'                [propext, Classical.choice, Quot.sound]
'KnotGame.CommonWindow.common_window'                   [propext, Classical.choice, Quot.sound]
```

## 3. Constraints of the commission

* No `sorry`, no `admit`, no new `axiom`, no `@[implemented_by]`.
* No `native_decide`.  Round 4 adds no finite computation at all: it is algebra
  over an ordered field plus induction on `ℕ`.  The rational inequalities of the
  anchor window are closed by `norm_num`, which is kernel-checked arithmetic.
* `Classical.choice` enters through Mathlib's real numbers and through the
  classical decidability of real comparisons such as `x ∈ Window λ`.  Nothing in
  round 4 uses choice to *produce* an object that is then claimed to be
  explicit: `theta`, `spine`, `visit` and `devWord` are given by explicit
  recursions (`visit` through `sInf` of a set of naturals, whose non-emptiness
  is proved, not assumed).
