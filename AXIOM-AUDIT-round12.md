# AXIOM AUDIT — round 12 (`KindDimLower.lean`)

Round 12 was interrupted and never wrote an audit.  This one was produced in
round 13, against the file exactly as it stands in the tree
(`RequestProject/KindDimLower.lean`, 658 lines, namespace
`KnotGame.KindLower`), which is in the import closure of `All.lean` and builds.

Scope: **round 12's own results only**.  Per the round-13 operating rules no
tree-wide audit was run; the results of earlier rounds are covered by their own
audit documents.

## 1. Source-level checks

Over `RequestProject/KindDimLower.lean`:

* no `sorry`, no `admit`;
* no `axiom` declaration;
* no `@[implemented_by]`;
* no `native_decide` (and no `decide` on a non-trivial proposition — the file
  is analytic and uses none);
* no `unsafe`, no `partial`, no `opaque`;
* the only `Classical` use is via `open scoped Classical` and Mathlib's own
  classical machinery, which is what `Classical.choice` in the reports below
  records.

## 2. `#print axioms`, verbatim

```
'KnotGame.KindLower.G_mem_K' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.KindLower.kindMeasure_K' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.KindLower.kindMeasure_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.KindLower.kindMeasure_le_of_ediam' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.KindLower.le_dimH_K' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.KindLower.dimH_K_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every report is confined to `propext`, `Classical.choice`, `Quot.sound`.  These
are the three axioms of Lean's classical foundation and are the same set the
continuous-integration audit accepts tree-wide.

## 3. What the audit does *not* cover

* `kindMeasure` is a definition, not a theorem; its content is audited only
  through the theorems above.
* The identification of `KindDim.K` with the kind set of the paper is round
  11's business, not round 12's, and is audited in `AXIOM-AUDIT-round11.md`.
* The box dimension is not in this file; see `AXIOM-AUDIT-round13.md`.
