# AXIOM AUDIT — round 14

`#print axioms` on round 14's own theorems only, as the operating rules
require (no tree-wide audit).  Every target reports

```
[propext, Classical.choice, Quot.sound]
```

## T39.5 — `RequestProject/BranchBridge.lean`

```
'KnotGame.BranchBridge.branchLegal_iff_BLegal' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.BranchBridge.branchSurvivesWord_iff_bSurvives' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.BranchBridge.rapp_eq_branchIter' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.BranchBridge.branchIter_append' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.BranchBridge.branchSurvivesWord_append' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.BranchBridge.branchWords_eq_SW' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.BranchBridge.bcount_eq_Kx' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## T40 — `RequestProject/Contraction.lean`

```
'KnotGame.Contraction.P_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Contraction.P_eq_smul_T' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Contraction.lipschitz_contraction' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Contraction.lipschitz_contraction_iterate' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Contraction.tendsto_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Contraction.tendstoUniformlyOn_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Contraction.const_eq_integral_of_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## T41 — `RequestProject/EquiMean.lean`

```
'KnotGame.EquiMean.adjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.EquiMean.endpoint_propagator' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.EquiMean.iterate_P_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.EquiMean.equidistribution_in_mean' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## T42 — `RequestProject/BackwardClosure.lean`

```
'KnotGame.BackwardClosure.survivesWord_map_toMove' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.BackwardClosure.posAfter_map_toMove' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.BackwardClosure.denseFrom_half_imp_kindDense' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.BackwardClosure.N_unbounded_of_denseFrom_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.BackwardClosure.endpoints_subset_of_legal' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.BackwardClosure.denseFrom_of_image' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.BackwardClosure.mem_D_of_image_mem_D' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.BackwardClosure.compl_D_forward_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.BackwardClosure.N_unbounded_of_orbit_point_denseFrom' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Notes

* Each of the four modules was built on its own
  (`lake build RequestProject.<Module>`); no bare `lake build` and no tree-wide
  audit was run.
* No module in this round takes more than about ten seconds to elaborate.
* Round 14 adds no finite computation: it is analysis (a Banach-style geometric
  estimate and Lebesgue integration on `(0,1)`) plus induction on lists and on
  `ℕ`.  No `decide`, no `native_decide`.
