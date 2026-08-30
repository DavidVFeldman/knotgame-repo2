# AXIOM AUDIT — round 15

`#print axioms` on round 15's own theorems only, as the operating rules require
(no tree-wide audit).  Every target reports

```
[propext, Classical.choice, Quot.sound]
```

No `sorry`, no `admit`, no added `axiom`, no `@[implemented_by]`, no
`native_decide` anywhere in the round's sources.

**How this transcript was produced.**  The round's four modules were built one
at a time — `RequestProject.Contraction`, `RequestProject.InvariantMeasure`,
`RequestProject.EquiMean`, `RequestProject.BackwardClosure`, all four
successful — and the `#print axioms` commands below were then elaborated in a
single scratch file against those built modules, outside the `RequestProject`
directory so that nothing is left for the directory glob to compile.  No
tree-wide build and no tree-wide audit was run: `RequestProject.All` imports
everything, so building it would be a whole-tree build, and the union is CI's
job.

## T43 — `RequestProject/Contraction.lean`

```
'KnotGame.Contraction.integrable_of_lipBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Contraction.integrable_iterate' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Contraction.integral_iterate_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Contraction.const_eq_integral_of_iterate_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Contraction.const_eq_integral_of_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Contraction.integral_eq_of_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Contraction.tendsto_integral_of_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## T44 — `RequestProject/BackwardClosure.lean`

```
'KnotGame.BackwardClosure.branchLegal_branch' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.BackwardClosure.rapp_branchWordOf' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.BackwardClosure.branchSurvivesWord_branchWordOf' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.BackwardClosure.kindDense_imp_denseFrom_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.BackwardClosure.denseFrom_half_iff_kindDense' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## T45 — `RequestProject/InvariantMeasure.lean`

```
'KnotGame.InvariantMeasure.isProbabilityMeasure_nu' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.InvariantMeasure.nu_compl_Icc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.InvariantMeasure.integral_nu' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.InvariantMeasure.invariantOn_nu' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.InvariantMeasure.const_eq_integral_nu' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.InvariantMeasure.tendsto_integral_nu' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.InvariantMeasure.equidistribution_in_mean_nu' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Import closure

`RequestProject/InvariantMeasure.lean` is imported by `RequestProject/All.lean`
and `InvariantMeasure` is in the CI module list of `.github/workflows/ci.yml`,
so round 15 does not repeat round 14's escape from the closure.
