# MERGE NOTES — union of the two parallel lineages (external rounds 9 and 10/11)

Base: the commission-8 lineage (internal rounds through 11 plus an interrupted
final session). Merged in from the commission-7 lineage (the Fourier round):
FourierFloor, FourierGeneral, FourierReflect, PlasticFourier,
SupergoldenFourier, TribonacciFourier, FourierEnclosure, RecordGaps, and —
renamed to avoid a filename collision with this lineage's more general
Immortal.lean — ImmortalMahler.lean (round 9's Mahler-control forms,
`unbounded_of_infinite_immortal` and `_fin`, names distinct from the base
file's `N_unbounded_of_immortal`). No inherited file was edited except
All.lean (imports appended).

Honesty notes. (1) A bare-name scan across files shows many repeated
declaration names (`cell0…`, `p`, `lam`, …); these are expected and were
already present within each lineage, protected by per-file namespaces. No
namespace-qualified collision check has been run — that requires elaboration,
i.e. the T33 build. (2) THIS TREE HAS NOT BEEN REBUILT SINCE THE MERGE.
Building it, checking the internal namespace of ImmortalMahler.lean against
Immortal.lean, and running the tree-wide semantic audit over the union are
the first tasks of the next round; nothing merged should be considered
accepted until that passes.

## Post-delivery corrections (found by the round-12 build attempt)

The first build attempt against this tree surfaced two defects in the merge,
both now fixed at source: (1) `Lucas.lean` — imported by `FourierFloor.lean`
— had been dropped, because the merge copied a hand-picked list of files
rather than the import closure; the original round-9 file is restored (the
round-12 session independently reconstructed an equivalent one; either
satisfies the interface, and the audit re-checks whichever is present).
(2) `All.lean` had the nine merged imports appended AFTER the trailing module
docstring, which does not parse; it is rewritten with all imports first,
deduplicated, and every import verified to resolve. A textual closure check
now reports no unresolved imports; the only files outside the transitive
closure of `All.lean` are `AxiomAudit.lean` (the audit driver, standalone by
design — it inspects the environment rather than joining it) and `Main.lean`
(an executable entry point). Everything mathematical is inside the closure.
