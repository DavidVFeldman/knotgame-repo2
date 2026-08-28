# AXIOM AUDIT — round 7

Two independent checks, as in rounds 2–5.

## 1. The semantic audit run by the build

`RequestProject/AxiomAudit.lean` walks every constant of the environment in the
`KnotGame` namespace, computes its axiom set with the machinery behind
`#print axioms`, and fails the build if any axiom outside
`propext, Classical.choice, Quot.sound` occurs — in particular if `sorryAx`
does.  With round 7 in place `lake build` reports

```
axiom audit passed: 1084 theorems, axioms confined to [propext, Classical.choice, Quot.sound]
```

(before round 7 the audit reported 1009; the 75 further theorems are round 7's.)

## 2. Per-target `#print axioms`

```
'KnotGame.ExpCount.two_mul_kappa_le'                        [propext, Classical.choice, Quot.sound]
'KnotGame.ExpCount.two_pow_le_K_of_doubling'                [propext, Classical.choice, Quot.sound]
'KnotGame.ExpCert.rapp_mem_of_iok'                          [propext, Classical.choice, Quot.sound]
'KnotGame.ExpCert.doubling_of_cert'                         [propext, Classical.choice, Quot.sound]
'KnotGame.ExpLower.doubling_three_halves'                   [propext, Classical.choice, Quot.sound]
'KnotGame.ExpLower.two_pow_le_K'                            [propext, Classical.choice, Quot.sound]
'KnotGame.ExpWindow.doubling_window'                        [propext, Classical.choice, Quot.sound]
'KnotGame.ExpWindow.two_pow_le_K_window'                    [propext, Classical.choice, Quot.sound]
'KnotGame.ExpMulti.mul_kappa_le'                            [propext, Classical.choice, Quot.sound]
'KnotGame.ExpMulti.pow_le_K_of_mdoubling'                   [propext, Classical.choice, Quot.sound]
'KnotGame.ExpMultiCert.mdoubling_of_cert'                   [propext, Classical.choice, Quot.sound]
'KnotGame.ExpSharp.mdoubling_three_halves'                  [propext, Classical.choice, Quot.sound]
'KnotGame.ExpSharp.fifteen_pow_le_K'                        [propext, Classical.choice, Quot.sound]
'KnotGame.ReturnTail.retTime_spec'                          [propext, Classical.choice, Quot.sound]
'KnotGame.ReturnTail.lt_retTime_iff'                        [propext, Classical.choice, Quot.sound]
'KnotGame.ReturnTail.return_time_tail'                      [propext, Classical.choice, Quot.sound]
'KnotGame.ReturnTail.return_time_tail_three_halves'         [propext, Classical.choice, Quot.sound]
'KnotGame.ReturnTail.return_time_tail_prob_three_halves'    [propext, Classical.choice, Quot.sound]
```

## 3. Source-level checks

```
rg -n "sorry|admit|^axiom |native_decide|implemented_by" RequestProject/
```

returns no hit in any round-7 file (nor anywhere else in `RequestProject/`).
The finite computations of round 7 are discharged with `decide +kernel`, i.e. by
the Lean kernel on exact rationals; the only `set_option` used is
`maxHeartbeats 1000000` in the generated data files
`RequestProject/ExpWindowData.lean` and `RequestProject/ExpSharpData.lean`,
which affects the elaborator's time budget and no check.
