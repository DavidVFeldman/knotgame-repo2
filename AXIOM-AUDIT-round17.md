# AXIOM AUDIT — round 17

`#print axioms` for every declaration of `RequestProject/Closures17.lean`, the
only module authored this round. The audit was run in a scratch file kept
outside `RequestProject/` (so that the directory glob does not compile it) and
removed afterwards; it imported `RequestProject.Closures17` only. No tree-wide
audit was run.

Scratch file:

```
import RequestProject.Closures17
#print axioms KnotGame.Closures17.g_lt_r
#print axioms KnotGame.Closures17.survives_nextMove
#print axioms KnotGame.Closures17.orbit_mem_Ioo
#print axioms KnotGame.Closures17.no_contracting_weight
#print axioms KnotGame.Closures17.P_id
#print axioms KnotGame.Closures17.dist_P_id
#print axioms KnotGame.Closures17.not_lipschitzWith_P_id
#print axioms KnotGame.Closures17.mem_orb_iff
#print axioms KnotGame.Closures17.not_kindDense_of_orb_finite
#print axioms KnotGame.Closures17.not_denseFrom_half_of_finite
#print axioms KnotGame.Closures17.not_kindDense_of_isPisot
#print axioms KnotGame.Closures17.not_denseFrom_half_of_isPisot
```

Transcript:

```
'KnotGame.Closures17.g_lt_r' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Closures17.survives_nextMove' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Closures17.orbit_mem_Ioo' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Closures17.no_contracting_weight' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Closures17.P_id' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Closures17.dist_P_id' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Closures17.not_lipschitzWith_P_id' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Closures17.mem_orb_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Closures17.not_kindDense_of_orb_finite' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Closures17.not_denseFrom_half_of_finite' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Closures17.not_kindDense_of_isPisot' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Closures17.not_denseFrom_half_of_isPisot' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every declaration reports the three standard axioms and nothing else. The
module's source contains no `sorry`, no `admit`, no added `axiom`, no
`@[implemented_by]`, no `decide` and no `native_decide`.

Build record: `lake build RequestProject.Closures17` succeeds, in about nine
seconds of elaboration for the module itself, with no warnings arising from it.
(The one warning printed during the run, an unused variable at
`RequestProject/CountingOperator.lean:121`, is inherited and pre-existing; no
inherited module was edited this round.)
