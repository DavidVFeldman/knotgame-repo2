# AXIOM AUDIT — round 16

`#print axioms` on round 16's own theorems only, as the operating rules require
(no tree-wide audit). Every target reports

```
[propext, Classical.choice, Quot.sound]
```

No `sorry`, no `admit`, no added `axiom`, no `@[implemented_by]`, no
`native_decide`, no `decide` anywhere in the round's source.

**How this transcript was produced.** The round's single module,
`RequestProject.PisotSeparation`, was built on its own
(`lake build RequestProject.PisotSeparation`, about 20 s of elaboration on top
of the inherited `RequestProject.Pisot`), and the `#print axioms` commands below
were then elaborated in one scratch file against the built module, in a
directory outside `RequestProject/` so that nothing was left for the directory
glob to compile; the scratch directory was removed afterwards. No tree-wide
build and no tree-wide audit was run: `RequestProject.All` imports everything,
so building it is a tree build under another name, and the union is CI's job.
No inherited module was edited, so no importer needed rebuilding.

## T46 — `RequestProject/PisotSeparation.lean`

```
'KnotGame.one_le_prod_norm_embeddings' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.one_le_norm_mul_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.finite_ncard_le_of_separated' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.exists_iterC_eq_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.orb_separated_of_conj_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.orb_ncard_le_of_conj_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.exists_conj_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KnotGame.orb_separated' depends on axioms: [propext, Classical.choice, Quot.sound]
```

That is every public declaration of the module: the two number-field lemmas,
the separated-set count, the orbit representation lemma, T46(a), T46(b), the
uniform conjugate bound, and the packaged `IsPisot` statement.
