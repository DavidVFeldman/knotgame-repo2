# Files outside the verified closure

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
