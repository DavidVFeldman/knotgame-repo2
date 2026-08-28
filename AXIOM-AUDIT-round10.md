# AXIOM AUDIT — round 10

## 1. The tree-wide audit

`RequestProject/AxiomAudit.lean` (inherited, unchanged) walks every theorem in
the environment reachable from `RequestProject.All` and fails the build if any
of them depends on an axiom outside the permitted list.  On the final round-10
tree the build reports

```
info: RequestProject/AxiomAudit.lean:20:0: axiom audit passed: 1290 theorems,
      axioms confined to [propext, Classical.choice, Quot.sound]
Build completed successfully (8106 jobs).
```

Counts:

| Stage | theorems audited |
| --- | --- |
| inherited tree (end of round 8) | 1198 |
| final round-10 tree (T30 + T31 + T32 added) | 1290 |

## 2. Source-level checks

* No `sorry` and no `admit` anywhere in `RequestProject/`.
* No `axiom` declaration was added, and no `@[implemented_by]`; the only axioms
  in the transitive closure are Lean's/Mathlib's `propext`, `Classical.choice`,
  `Quot.sound`.
* No `native_decide`.  Every finite check of round 10 is a *kernel* reduction:
  `decide +kernel` over exact rationals and finite lists (T31's 15 groups, T32's
  36 groups and the chaining check), or `norm_num`.

Reproduce with

```
rg -n "sorry|admit|native_decide|^axiom " RequestProject/
lake build
```

## 3. Per-target `#print axioms`

Verbatim output of `#print axioms` on the round-10 headline results:

```
'KnotGame.NoRecurrence.no_recurrence' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.NoRecurrence.no_recurrence_knotAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.NoRecurrence.knot_positions_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.NoRecurrence.no_identity_block' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.NoRecurrence.no_identity_block_config' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.ExpSharper.mdoubling_three_halves' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.ExpSharper.twentysix_pow_le_K' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.ExpSharper.sharper_rate_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.ExpAbove.vdoubling_above' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.ExpAbove.two_pow_le_K_above' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.ExpAbove.two_pow_le_K_sqrt_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.ExpAbove.golden_lt_window' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.ExpAbove.sqrt_three_mem_window' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.ExpAbove.K_unbounded_above' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 4. Kernel costs of the round-10 certificates

Measured on the machine the round was built on, for the record and for anyone
who wants to push further (see `CENSUS-round10.md` §3 and §4.2 for the ceilings
these numbers imply):

| Item | Data | Elaboration | Kernel checks |
| --- | --- | --- | --- |
| T31 `ExpSharperData` + `ExpSharper` | 747 cells × 26 words × 14 letters ≈ 272 k letters | 159 s | 790 s (15 groups) |
| T32 `ExpAboveData0…11` + `ExpAboveChecks` | 180 parameter cells, 17 141 point cells, 246 225 letters | ≈ 300 s (12 files, in parallel) | 1 108 s (36 groups) |
| `RequestProject.AxiomAudit` | whole tree | — | 209 s |

The T32 data had to be split across twelve files: as one 18 213-line file its
elaboration alone exceeded 17 minutes and 8.6 GB.
