# AXIOM AUDIT — round 13 (T36, T38, T39)

Scope: **the three modules round 13 authored**, per the operating rule that
forbids a tree-wide audit.  Earlier rounds' results rest on their own audit
documents; nothing in them was re-checked, and nothing in them was changed.

Modules audited: `RequestProject/KindBox.lean` (T36),
`RequestProject/CountingOperator.lean` (T38),
`RequestProject/Trapezoid.lean` (T39).  All three build against the pinned
toolchain and are imported by `RequestProject/All.lean`.

## 1. Source-level checks

Over the three files:

* no `sorry`, no `admit`;
* no `axiom` declaration;
* no `@[implemented_by]`;
* no `native_decide` — and in fact no `decide` at all: all three files are
  analytic, with no kernel computation;
* no `unsafe`, no `partial`, no `opaque`;
* classical reasoning enters only through Mathlib and `open scoped Classical`,
  which is what `Classical.choice` in the reports below records.

## 2. `#print axioms`, verbatim

### T36 — `KindBox.lean`

```
'KnotGame.KindBox.coverNum_K_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.KindBox.le_coverNum_K' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.KindBox.tendsto_boxQuot' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.KindBox.upperBoxDim_K' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.KindBox.lowerBoxDim_K' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.KindBox.boxDim_K' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### T38 — `CountingOperator.lean`

```
'KnotGame.CountingOperator.T_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.CountingOperator.bcount_eq_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.CountingOperator.integral_bcount' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.CountingOperator.integral_kcount' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.CountingOperator.integral_kcount_three_halves' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### T39 — `Trapezoid.lean`

```
'KnotGame.Trapezoid.bval_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Trapezoid.evenPart_mem_Icc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Trapezoid.oddPart_mem_Icc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Trapezoid.unifSum_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Trapezoid.unifSum_eq_withDensity' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Trapezoid.convDens_sqrt_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Trapezoid.trapezoid_law' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Trapezoid.isProbabilityMeasure_trapDens' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Trapezoid.trapezoid_of_split' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every report is confined to `propext`, `Classical.choice`, `Quot.sound`, the
three axioms of Lean's classical foundation, which is the set the tree-wide
continuous-integration audit accepts.

## 3. What the audit does and does not certify

* It certifies that the statements listed above are theorems of Lean's
  classical foundation, with no extra assumption and no unproved step.
* It does **not** certify that they are the paper's statements; that is the
  business of `SCRUPLES-round13.md`, and in two places the wording differs
  from the commission deliberately:
  * T38's kind-word integral is `(3/λ)^m`, not the commissioned `(2/λ)^m`;
    the `(2/λ)^m` identity is proved for the branch count instead.  See the
    scruples §2 and the census §3.
  * T39's `trapezoid_of_split` carries an explicit hypothesis — the joint law
    of the two parts is the product of the two uniforms — which is the one
    step of `prop:trapezoid` this round did not formalise.  `trapezoid_law`
    itself, the convolution identity, is unconditional.
* Round 11's `ExpSharpest*` files remain outside the import closure and
  outside every audit; the strongest audited growth rate at `λ = 3/2` is still
  `ExpSharper`'s `26 ^ ⌊m/14⌋` (`AXIOM-AUDIT-round10.md`).  Round 13 did not
  touch them.
