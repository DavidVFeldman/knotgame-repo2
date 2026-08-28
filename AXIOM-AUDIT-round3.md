# AXIOM AUDIT — round 3

Two independent checks, as in round 2.

## 1. The semantic audit run by the build

`RequestProject/AxiomAudit.lean` walks every constant of the environment in the
`KnotGame` namespace, computes its axiom set with the machinery behind
`#print axioms`, and fails the build if any axiom outside
`propext, Classical.choice, Quot.sound` occurs — in particular if `sorryAx`
does.  With round 3 in place `lake build` reports

```
axiom audit passed: 524 theorems, axioms confined to [propext, Classical.choice, Quot.sound]
```

(round 2 reported 480; the 44 further theorems are T10's.)

## 2. Per-target `#print axioms`

```
'KnotGame.Tribonacci.sup_N_lam'                   [propext, Classical.choice, Quot.sound]
'KnotGame.Tribonacci.d_one'                       [propext, Classical.choice, Quot.sound]
'KnotGame.Tribonacci.d_two'                       [propext, Classical.choice, Quot.sound]
'KnotGame.Tribonacci.d_three'                     [propext, Classical.choice, Quot.sound]
'KnotGame.Tribonacci.reach_card_eq'               [propext, Classical.choice, Quot.sound]
'KnotGame.Supergolden.sup_N_lam'                  [propext, Classical.choice, Quot.sound]
'KnotGame.Supergolden.d_one'                      [propext, Classical.choice, Quot.sound]
'KnotGame.Supergolden.d_two'                      [propext, Classical.choice, Quot.sound]
'KnotGame.Supergolden.d_three'                    [propext, Classical.choice, Quot.sound]
'KnotGame.Supergolden.d_four'                     [propext, Classical.choice, Quot.sound]
'KnotGame.Supergolden.checkOK_true'               [propext, Classical.choice, Quot.sound]
'KnotGame.Transversality.transversality'          [propext, Classical.choice, Quot.sound]
'KnotGame.Transversality.transversality_deriv'    [propext, Classical.choice, Quot.sound]
'KnotGame.Transversality.Phi_sub_abs'             [propext, Classical.choice, Quot.sound]
'KnotGame.Transversality.volume_close_le'         [propext, Classical.choice, Quot.sound]
'KnotGame.Transversality.sum_volume_close_le'     [propext, Classical.choice, Quot.sound]
'KnotGame.Transversality.sum_volume_close_le_unord' [propext, Classical.choice, Quot.sound]
'KnotGame.Transversality.lintegral_pairCount_le'  [propext, Classical.choice, Quot.sound]
```

## 3. Constraints of the commission

* No `sorry`, no `admit`, no new `axiom`, no `@[implemented_by]`.
* No `native_decide`: every finite verification (the tribonacci reachability,
  the supergolden `checkOK`, the 27 transversality cells) is closed by kernel
  reduction (`decide` / `decide +kernel`).
* T10 adds no finite computation at all; it is analysis and combinatorics on
  top of the T9 statement.
