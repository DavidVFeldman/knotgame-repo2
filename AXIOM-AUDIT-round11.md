# AXIOM AUDIT — round 11 (written in round 13; see §0)

## 0. Why this document is late, and what it can and cannot say

Round 11 delivered its census (`CENSUS-round11.md`) and its scruples
(`SCRUPLES-round11.md`) but no axiom audit: the session ended before one was
written, and `SCRUPLES-round11.md` §9 nonetheless refers to
"`AXIOM-AUDIT-round11.md`" as though it existed.  This document supplies it,
reconstructed in round 13 from the round-11 census and from the identifiers
actually present in the tree.  Two consequences of the delay must be stated
plainly.

* **It is not the audit round 11 would have produced.**  It is an audit of the
  round-11 material *as it stands in the round-13 tree*.  Nothing in that
  material has been edited since (the round-11 files are untouched by rounds 12
  and 13), so the two coincide for everything inside the import closure — but
  the claim being made here is about the present tree, not about a build that
  no one recorded.
* **`ExpSharpest` is not audited, and its result is not certified.**  Round 11's
  seventh item, the multiplicity-49 certificate giving the rate
  `49^(1/16) ≈ 1.27537`, lives in `RequestProject/ExpSharpest.lean` and its
  `ExpSharpestData*` / `ExpSharpestChecks*` companions, which are **outside the
  import closure of `All.lean`** because their kernel checks exceed the memory
  of the CI runner (`UNBUILT.md`).  They have never completed a build, so no
  `#print axioms` can be run on them and none is reported below.  The strongest
  **audited** growth rate at `λ = 3/2` remains `ExpSharper`'s `26 ^ ⌊m/14⌋`
  (`AXIOM-AUDIT-round10.md`).  `CENSUS-round11.md` §0 marks that row "done";
  read together with this audit and `UNBUILT.md`, "done" there means "written
  and self-consistent", not "checked end to end".

## 1. Source-level checks

Over the round-11 sources (`Overlap.lean`, `PisotDecide.lean`,
`CircleForm.lean`, `Immortal.lean`, `Square.lean`, `KindDim.lean`,
`RecordLower.lean`), and over the whole of `RequestProject/`:

* no `sorry`, no `admit`;
* no `axiom` declaration, no `@[implemented_by]`;
* no `native_decide`; every finite check is a kernel reduction (`decide`,
  `decide +kernel`) or `norm_num`.

Reproduce with

```
rg -n "sorry|admit|native_decide|^axiom " RequestProject/
```

## 2. Per-target `#print axioms`

Verbatim output on the round-11 headline results that are inside the import
closure (Lean 4.28.0, Mathlib as pinned by `lake-manifest.json`):

```
'KnotGame.Overlap.not_pm_root_inv_sqrt_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Overlap.not_pm_root_two_thirds' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Overlap.inv_phi_root' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Overlap.inv_rho_root' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Overlap.branchIter_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.reachable_finite' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.N_eventually_constant' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.sup_N_isGreatest' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.CircleForm.circle_L' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.CircleForm.circle_R' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.CircleForm.circle_M' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.CircleForm.card_marked' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Immortal.N_unbounded_of_immortal' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Immortal.N_unbounded_of_immortal_three_halves' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Square.square_normal_form' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Square.squaresurv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Square.no_spare_of_exceptional' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.KindDim.volume_K' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.KindDim.dimH_K_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.d_ge_two_mul_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.d_succ_ge_add_two' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Note the namespaces: `PisotDecide.lean` and `RecordLower.lean` put their
theorems directly in `KnotGame`, not in a file-named sub-namespace.  (The same
mismatch between a file name and the namespace it opens is what broke
`KindBox.lean`; see `SCRUPLES-round13.md` §1.)

## 3. What this audit does not cover

| Round-11 item | Covered here? |
| --- | --- |
| `lem:overlap` (`Overlap.lean`) | yes |
| `cor:decide` (`PisotDecide.lean`) | yes |
| `prop:circle` (`CircleForm.lean`) | yes |
| `prop:immortal32` (`Immortal.lean`) | yes |
| `prop:square`, `prop:squaresurv` (`Square.lean`) | yes |
| `prop:kinddim`, upper half (`KindDim.lean`) | yes |
| `prop:lowerbound`, `cor:recursive` (`RecordLower.lean`) | yes |
| the multiplicity-49 rate (`ExpSharpest*`) | **no** — outside the import closure, never built; see §0 and `UNBUILT.md` |
