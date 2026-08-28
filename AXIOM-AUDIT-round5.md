# AXIOM AUDIT — round 5

Two independent checks, as in rounds 2, 3 and 4.

## 1. The semantic audit run by the build

`RequestProject/AxiomAudit.lean` walks every constant of the environment in the
`KnotGame` namespace, computes its axiom set with the machinery behind
`#print axioms`, and fails the build if any axiom outside
`propext, Classical.choice, Quot.sound` occurs — in particular if `sorryAx`
does.  With round 5 in place `lake build` reports

```
axiom audit passed: 845 theorems, axioms confined to [propext, Classical.choice, Quot.sound]
```

(round 4 reported 636; the 209 further theorems are round 5's.)

## 2. Per-target `#print axioms`

```
T14  'KnotGame.inCells_cells'                              [propext, Classical.choice, Quot.sound]
T14  'KnotGame.length_cells_le'                            [propext, Classical.choice, Quot.sound]
T14  'KnotGame.volume_survivorSet'                         [propext, Classical.choice, Quot.sound]
T14  'KnotGame.exists_long_cell'                           [propext, Classical.choice, Quot.sound]
T15  'KnotGame.knotAt_cons'                                [propext, Classical.choice, Quot.sound]
T15  'KnotGame.mem_run_iff'                                [propext, Classical.choice, Quot.sound]
T15  'KnotGame.card_run_ge_of_ages'                        [propext, Classical.choice, Quot.sound]
T16  'KnotGame.annihilation_unique'                        [propext, Classical.choice, Quot.sound]
T16  'KnotGame.posAfter_inj'                               [propext, Classical.choice, Quot.sound]
T17  'KnotGame.infinitelyManyKnots_iff_annihilations'      [propext, Classical.choice, Quot.sound]
T17  'KnotGame.boundedAgeWitnesses_of_infinitelyManyKnots' [propext, Classical.choice, Quot.sound]
T17  'KnotGame.infinitelyManyKnots_of_boundedAgeWitnesses' [propext, Classical.choice, Quot.sound]
T17  'KnotGame.N_unbounded_of_infinitelyManyKnots'         [propext, Classical.choice, Quot.sound]
T18  'KnotGame.infinitelyManyKnots_of_kindDense'           [propext, Classical.choice, Quot.sound]
T18  'KnotGame.N_unbounded_of_kindDense'                   [propext, Classical.choice, Quot.sound]
T19a 'KnotGame.deficit_law'                                [propext, Classical.choice, Quot.sound]
T19a 'KnotGame.step_extremes'                              [propext, Classical.choice, Quot.sound]
T19b 'KnotGame.actsAs_M_R_iff'                             [propext, Classical.choice, Quot.sound]
T19b 'KnotGame.actsAs_M_L_iff'                             [propext, Classical.choice, Quot.sound]
T19b 'KnotGame.actsAs_M_R_converse_fails'                  [propext, Classical.choice, Quot.sound]
T19b 'KnotGame.step_M_eq_of_actsAs'                        [propext, Classical.choice, Quot.sound]
T20  'KnotGame.followsItin_partition'                      [propext, Classical.choice, Quot.sound]
T20  'KnotGame.followsItin_eq_Ioo'                         [propext, Classical.choice, Quot.sound]
T20  'KnotGame.candidate_count'                            [propext]
T20  'KnotGame.candidate_total_length'                     [propext, Classical.choice, Quot.sound]
T20  'KnotGame.candidates_partition_survivorSet'           [propext, Classical.choice, Quot.sound]
T21  'KnotGame.run_eq_image_runZ'                          [propext, Classical.choice, Quot.sound]
T21  'KnotGame.card_run_eq_card_runZ'                      [propext, Classical.choice, Quot.sound]
T21  'KnotGame.run_subset_run_iff'                         [propext, Classical.choice, Quot.sound]
T21  'KnotGame.card_run_record5'                           [propext, Classical.choice, Quot.sound]
T21  'KnotGame.card_run_record7'                           [propext, Classical.choice, Quot.sound]
T21  'KnotGame.d_le_nineteen'                              [propext, Classical.choice, Quot.sound]
T21  'KnotGame.d_le_twentythree'                           [propext, Classical.choice, Quot.sound]
T21  'KnotGame.d_le_fiftytwo'                              [propext, Classical.choice, Quot.sound]
T21  'KnotGame.record_subset_two_three'                    [propext, Classical.choice, Quot.sound]
T21  'KnotGame.record_subset_three_five'                   [propext, Classical.choice, Quot.sound]
T21  'KnotGame.record_subset_four_six'                     [propext, Classical.choice, Quot.sound]
T21  'KnotGame.record_subset_five_seven'                   [propext, Classical.choice, Quot.sound]
+    'KnotGame.N_eight_le_three'                           [propext, Classical.choice, Quot.sound]
+    'KnotGame.d_two_eq_three'                             [propext, Classical.choice, Quot.sound]
+    'KnotGame.d_three_eq_five'                            [propext, Classical.choice, Quot.sound]
+    'KnotGame.d_four_eq_nine'                             [propext, Classical.choice, Quot.sound]
```

The rows marked `+` are the exact record depths of `RecordDepths.lean`, which
the commission did not ask for; they are listed because they are new results of
round 5.  `candidate_count` depends on `propext` alone because it is a pure
kernel computation on integers.

## 3. Constraints of the commission

* No `sorry`, no `admit`, no new `axiom`, no `@[implemented_by]`.
* No `native_decide`.  Round 5's finite computations — the six live candidate
  cells and their total length (T20), the record configurations, their
  cardinalities and the containments between them (T21), and the exhaustion of
  all `3^n` words of length `n ≤ 8` (`RecordDepths.lean`) — are all closed by
  kernel reduction (`decide`, `decide +kernel`) on exact integer arithmetic.
* The searches that *found* the record words and the beam-search word for
  `k = 7` are outside Lean (`scripts/game32_bfs.py`, `scripts/game32_records.py`,
  `scripts/game32_beam.py`).  Nothing in the Lean tree depends on them: each word
  they produce is re-run inside the kernel, and every claim about it is checked
  there.

## 4. How to reproduce

```
lake build          # builds the library and runs the semantic audit
```

and, for the per-target list above, `#print axioms KnotGame.<name>` after
`import RequestProject.All`.
