# Round 2 — axiom audit output

Acceptance is a *semantic* audit: `#print axioms` on every top-level target must
show at most `propext`, `Classical.choice`, `Quot.sound`.

## 1. The automatic audit, run by `lake build`

`RequestProject/AxiomAudit.lean` walks the elaborated environment, selects every
non-internal theorem whose name begins with `KnotGame`, computes its axiom set
with `Lean.collectAxioms` (the machinery behind `#print axioms`), and throws if
any axiom outside the permitted three appears.  It is part of the default build
target, so `lake build` fails if the audit fails.  It reads no source text.

Output of the last full build of this tree:

```
info: RequestProject/AxiomAudit.lean:20:0:
  axiom audit passed: 247 theorems, axioms confined to
  [propext, Classical.choice, Quot.sound]
```

(Round 1 reported 181 theorems; round 2 adds 66.)

## 2. `#print axioms` on every round-2 target, individually

```
'KnotGame.act_lt_act'                        depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.gap_law'                           depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.straddles_unique'                  depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.straddles_at_most_one'             depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.birth_head_ne_M'                   depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.births_le_ceil_half'               depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.card_le_length_succ'               depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.scheduling_bound'                  depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.N_le_of_separated'                 depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.run_subset'                        depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.near_collision'                    depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Golden.phi_pow_five_mul_delta0'    depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Golden.N_phi_le_nine'              depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Golden.card_run_phi_le_nine'       depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Plastic.chk_range'                 depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Plastic.chk_closed'                depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Plastic.chk_chain'                 depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Plastic.run_subset_OrbSet'         depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Plastic.run_sep'                   depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Plastic.N_rho_le_34'               depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.Plastic.card_run_rho_le_34'        depends on axioms: [propext, Classical.choice, Quot.sound]
```

To reproduce, put the `#print axioms` lines after `import RequestProject.All` in
a scratch file and elaborate it.

## 3. `native_decide`

Not used anywhere.  The three finite verifications of `PlasticOrbit.lean`
(`chk_range`, `chk_closed`, `chk_chain`, and the two small checks
`orbitList_length`, `half_mem_orbitList`) are closed by `decide`, i.e. by
kernel reduction, and are consequently covered by the audit above: a
`native_decide` proof would show `Lean.ofReduceBool` in these lists, and none
does.  The whole file elaborates and kernel-checks in about 30 seconds.

The checks are cheap because they are arithmetic on small integers.  Orbit
points are stored as integer coordinate triples over `ℤ[ρ]`; every comparison is
decided through the certified rational enclosure
`1324717957/10⁹ ≤ ρ ≤ 1324717958/10⁹`, scaled by `10¹⁸` so that it becomes an
integer inequality.  Nothing computes with real numbers.

## 4. `sorry`, `admit`, `axiom`

None in `RequestProject/`.  The semantic audit would catch `sorry` and `admit`
(they introduce `sorryAx`); `.github/workflows/ci.yml` additionally greps for
them.  No `axiom` declaration is introduced anywhere in the tree.
