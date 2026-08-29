# Files outside the verified closure

The files named below have been REMOVED from this repository. They remain in
the git history of the branch and in the delivery archives from the rounds
that produced them. They were removed rather than parked in a sibling
directory because `RequestProject` is a Lake library built by directory glob:
a file sitting in it is compiled by `lake build` whether or not `All.lean`
imports it, so an unbuildable file cannot be quarantined by dropping its
import. To resurrect one, restore it from history into `RequestProject/`,
add its import to `All.lean`, and add it to the module list in ci.yml.


## KindBox.lean — CLOSED IN ROUND 13, no longer unbuilt

HISTORICAL ENTRY, kept for the record. The box-dimension file for the kind set
at lambda = 3/2 was reported by an earlier session as "a complete 383-line
KindBox.lean ... covering numbers, the triadic upper bound, the Frostman lower
bound, the bracketing index, the squeeze from triadic to all scales, and both
box dimensions equal to log 2 / log 3. It has no `sorry`." CI run #4 showed
otherwise: elaboration failed at line 41 (`unknown namespace KindDimLower`)
and cascaded -- `cyl`, `dexp`, `atTop`, `Tendsto` all unknown, apparently
missing `open` statements and written against a different version of its
neighbours -- and two declarations were reported as incomplete.

The file had never been elaborated: nothing imported it, so no build and no
audit ever touched it. This is the second occurrence of that failure mode
(the first was Square.lean, fifteen errors, found the same way), and the
reason the invariant *file set = import closure* is now checked every round.

Round 13 (T36) rewrote the file from scratch against what KindDim.lean and
KindDimLower.lean actually export -- the real namespace being
`KnotGame.KindLower`, not `KindDimLower` -- redefined the bracketing index
without the nonexistent lemma, and PROVED the squeeze `tendsto_boxQuot` that
the old file had left unproved. `RequestProject/KindBox.lean` now elaborates,
is imported by `All.lean`, is listed in ci.yml, and is audited in
AXIOM-AUDIT-round13.md. Nothing about it is unbuilt any more.


## PlasticConfig / PlasticOrbitCount — excluded for hardware, NOT for doubt

The 25,525-state configuration closure at the plastic number, carrying
`N_rho_le_seven`, `d_rho_four`, `d_rho_seven` and `card_reachable_configs`.
Its kernel reduction exceeds the memory of a GitHub-hosted runner (it was
killed there after `PlasticCert` completed). It differs from the case below in
the decisive respect: these results ARE covered by a completed audit,
`AXIOM-AUDIT-round5.md`, so the paper's `N_rho = 7` stands on that audit and is
not downgraded. Retry with `heavy.yml`, which adds 32 GB of swap.


`RequestProject/ExpSharpest.lean`, `ExpSharpestData0…8`, `ExpSharpestChecks0…8`
(the multiplicity-49 certificate at lambda = 3/2, aiming at the rate
49^(1/16) ~ 1.27537) are present in the tree but are NOT part of the import
closure of `All.lean` and are NOT covered by any axiom audit.

Reason: their kernel checks do not fit the memory available to the CI runner.
The longest block that has completed is `ExpSharpestChecks1` at 1204 s; the
run was then killed (SIGTERM, exit 143) inside `ExpSharpestChecks2`. Round 11
recorded the work as done in its census, but no `AXIOM-AUDIT-round11.md` was
ever written, so the claim has never been checked end to end.

Consequently the strongest CERTIFIED growth rate at lambda = 3/2 is
`ExpSharper`'s `26 ^ floor(m/14)`, rate ~1.26203, audited in
`AXIOM-AUDIT-round10.md`. The paper states that figure.

To resurrect the sharper certificate: build on a runner with more memory (a
public repository gets 16 GB rather than 7 GB), or split `ExpSharpestChecks*`
into smaller groups, then restore the import and write the audit.
