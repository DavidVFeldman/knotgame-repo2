# AXIOM AUDIT — round 9

## 1. The tree-wide audit

`RequestProject/AxiomAudit.lean` walks every theorem in the environment
reachable from `RequestProject.All` and fails the build if any of them depends
on an axiom outside the permitted list.  On the final round-9 tree the build
reports

```
info: RequestProject/AxiomAudit.lean:20:0: axiom audit passed: 1435 theorems,
      axioms confined to [propext, Classical.choice, Quot.sound]
Build completed successfully (8097 jobs).
```

Counts across the round:

| Stage | theorems audited |
| --- | --- |
| inherited tree (end of round 8) | 1198 |
| + `Immortal`, `RecordGaps`, `Lucas`, `FourierFloor`, `FourierReflect`, `FourierEnclosure`, `FourierGeneral`, `PlasticFourier` | 1359 |
| + `SupergoldenFourier`, `TribonacciFourier` (final) | 1435 |

The ten new modules are reached by the audit because they are imported by
`RequestProject/All.lean`; those imports are the only edits made to an
inherited file this round.

## 2. Source-level checks

* No `sorry` and no `admit` anywhere in `RequestProject/`.
* No `axiom` declaration was added; the only axioms in the transitive closure
  are Lean's/Mathlib's `propext`, `Classical.choice`, `Quot.sound`.
* No `native_decide`, and no `@[implemented_by]`.  Every finite check in
  round 9 is a kernel reduction: `decide`, `norm_num` or `rfl` over exact
  rationals and finite lists.  This covers the record-gap computations of
  `RecordGaps.lean`, the twelve factor enclosures of `FourierEnclosure.lean`
  and the half-integer exclusions of `PlasticFourier.lean` — in particular the
  numerical enclosure of T29b uses no floating point and no external
  certificate, and neither do the finite half-integer checks of
  `SupergoldenFourier.lean` and `TribonacciFourier.lean`.

Reproduce with

```
rg -n "sorry|admit|native_decide|^axiom " RequestProject/
lake build
```

(The three surviving matches are prose inside docstrings, not code.)

## 3. Per-target `#print axioms`

Every round-9 headline statement, checked individually against
`import RequestProject.All`.  All thirty-two print the same list.

| Target | Constant | Axioms |
| --- | --- | --- |
| T27 | `KnotGame.Ternary.unbounded_of_infinite_immortal` | `[propext, Classical.choice, Quot.sound]` |
| T27 | `KnotGame.Ternary.unbounded_of_infinite_immortal_fin` | `[propext, Classical.choice, Quot.sound]` |
| T28 | `KnotGame.half_mem_records` | `[propext, Classical.choice, Quot.sound]` |
| T28 | `KnotGame.minGap_record2` | `[propext, Classical.choice, Quot.sound]` |
| T28 | `KnotGame.minGap_record3` | `[propext, Classical.choice, Quot.sound]` |
| T28 | `KnotGame.minGap_record4` | `[propext, Classical.choice, Quot.sound]` |
| T28 | `KnotGame.minGap_record5` | `[propext, Classical.choice, Quot.sound]` |
| T28 | `KnotGame.minGap_record6` | `[propext, Classical.choice, Quot.sound]` |
| T28 | `KnotGame.minGap_record7` | `[propext, Classical.choice, Quot.sound]` |
| T29a(i) | `KnotGame.Fourier.xi_scaling` | `[propext, Classical.choice, Quot.sound]` |
| T29a(i) | `KnotGame.Fourier.cosProd_xi` | `[propext, Classical.choice, Quot.sound]` |
| T29a(ii) | `KnotGame.Fourier.goldenRatio_pow_add_goldenConj_pow` | `[propext, Classical.choice, Quot.sound]` |
| T29a(ii) | `KnotGame.Fourier.abs_goldenRatio_pow_sub_lucas` | `[propext, Classical.choice, Quot.sound]` |
| T29a(ii) | `KnotGame.Fourier.abs_goldenRatio_pow_sub_round_le` | `[propext, Classical.choice, Quot.sound]` |
| T29a(iii) | `KnotGame.Fourier.multipliable_goldenFac` | `[propext, Classical.choice, Quot.sound]` |
| T29a(iii) | `KnotGame.Fourier.goldenFourierFloor_pos` | `[propext, Classical.choice, Quot.sound]` |
| T29a(iv) | `KnotGame.Fourier.tendsto_cosProd_xi_golden` | `[propext, Classical.choice, Quot.sound]` |
| addendum | `KnotGame.Fourier.goldenFourierFloor_eq_sq` | `[propext, Classical.choice, Quot.sound]` |
| T29b | `KnotGame.Fourier.tprod_neg_enclosure` | `[propext, Classical.choice, Quot.sound]` |
| T29b | `KnotGame.Fourier.goldenFourierFloor_enclosure` | `[propext, Classical.choice, Quot.sound]` |
| T29c | `KnotGame.Fourier.perr_sq_le` | `[propext, Classical.choice, Quot.sound]` |
| T29c | `KnotGame.Fourier.multipliable_plasticFac` | `[propext, Classical.choice, Quot.sound]` |
| T29c | `KnotGame.Fourier.plasticFourierFloor_pos` | `[propext, Classical.choice, Quot.sound]` |
| T29c | `KnotGame.Fourier.tendsto_cosProd_xi_plastic` | `[propext, Classical.choice, Quot.sound]` |
| T29c | `KnotGame.Fourier.sgErr_sq_le` | `[propext, Classical.choice, Quot.sound]` |
| T29c | `KnotGame.Fourier.multipliable_supergoldenFac` | `[propext, Classical.choice, Quot.sound]` |
| T29c | `KnotGame.Fourier.supergoldenFourierFloor_pos` | `[propext, Classical.choice, Quot.sound]` |
| T29c | `KnotGame.Fourier.tendsto_cosProd_xi_supergolden` | `[propext, Classical.choice, Quot.sound]` |
| T29c | `KnotGame.Fourier.triErr_sq_le` | `[propext, Classical.choice, Quot.sound]` |
| T29c | `KnotGame.Fourier.multipliable_tribonacciFac` | `[propext, Classical.choice, Quot.sound]` |
| T29c | `KnotGame.Fourier.tribonacciFourierFloor_pos` | `[propext, Classical.choice, Quot.sound]` |
| T29c | `KnotGame.Fourier.tendsto_cosProd_xi_tribonacci` | `[propext, Classical.choice, Quot.sound]` |

Reproduce by putting the `#print axioms` lines in a scratch file that imports
`RequestProject.All` and running `lake env lean` on it.

## 4. What the audit does *not* certify

It is a check on the *axioms*, not on the *statements*.  In particular:

* It says nothing about whether a hypothesis is ever satisfied.  Round 9 adds
  `KnotGame.Ternary.MahlerImmortal` to the list of conditions certified for no
  parameter, alongside the inherited `KnotGame.KindWord`, `KnotGame.KindDense`
  and `KnotGame.KindDenseQuant`.  Exhibiting a control with infinitely many
  immortal births is exactly the open problem the paper describes.
* It says nothing about *modelling*.  The Bernoulli convolution itself is not
  constructed: `cosProd` is *defined* to be the cosine product, which is the
  classical closed form of `|ν̂_r|`, and no statement in the tree identifies it
  with the Fourier transform of a measure.
* T29b is an *enclosure*.  `goldenFourierFloor_enclosure` bounds the product
  between `66/10⁴` and `67/10⁴`; nothing asserts the value itself, and no
  sharpness of the window is claimed.
* At the plastic, supergolden and tribonacci parameters only convergence,
  positivity and the `ξ_N` limit are proved; there is no numerical enclosure of
  any of those three floors, and the integer sequences (Perrin, `sgTrace`,
  `triTrace`) are used as definitions rather than identified with the traces
  `λ^m + α^m + ᾱ^m`.

The full list of deviations is `SCRUPLES-round9.md`.
