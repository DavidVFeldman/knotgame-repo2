# COMMISSION: knotgame round 13 — a small round, run the new way (T36–T39)

## OPERATING RULES — read first; they override habits from earlier rounds

The tree in this tarball is GREEN under continuous integration: it builds from
a fixed toolchain and its semantic axiom audit passes (1667 theorems, axioms
confined to propext, Classical.choice, Quot.sound). Verification of the whole
tree is no longer your job, and attempting it is what has consumed entire
sessions. Specifically:

1. FIRST COMMAND, always: `lake exe cache get`. Without it you will compile
   ~8000 Mathlib modules from source and be killed long before reaching this
   project. A progress report of the form "8125 of 8145" means you have not
   started on this project.
2. NEVER run a bare `lake build`, and never build the whole library. Build
   ONLY the modules you are authoring or repairing, one at a time:
   `lake build RequestProject.<YourModule>`.
3. NEVER run a tree-wide axiom audit. Run `#print axioms` on YOUR OWN new
   theorems only, and paste the output into your round audit document.
4. If any single module of yours takes more than ~10 minutes to elaborate,
   stop, report the module and the time, and do not retry in a loop. Kernel
   computations that large belong in a separate file that CI can be pointed at
   deliberately.
5. Do not attempt anything in `UNBUILT.md`. Those modules were removed from
   the library on purpose; the reasons are recorded there.
6. Deliver source files plus documents. Do not attempt to build the union,
   do not attempt to push, and do not treat "the tree builds" as a
   deliverable — that is checked downstream, on every commit, by CI.

Everything else is unchanged: census-first; report rather than repair; no
sorry/admit/new axiom/native_decide; SCRUPLES for every convention or
deviation. Note that the textual gate strips `--` comments, so you may
mention a forbidden token in prose, but not in code.

## T36 — repair KindBox (box dimension of the kind set at λ = 3/2)

`quarantine/KindBox.lean` in the git history (removed from the library; see
UNBUILT.md) contains a complete-looking development of the box dimension:
covering numbers, the triadic upper bound from the 2^n cylinders, the Frostman
lower bound 2^n ≤ 4·N(K,3^{-n}), the bracketing index, the squeeze from
triadic to all scales, both box dimensions equal to log 2 / log 3. It has
never elaborated. CI reports: unknown namespace `KindDimLower`; unknown
identifiers `cyl`, `ediam_cyl`, `K_subset_E`, `kindMeasure`, `dexp`, `atTop`,
`Tendsto`, `eventually_gt_atTop`; unknown constant `Nat.not_mem_of_lt_sInf`;
a failed `rewrite`; a type mismatch; and two declarations flagged incomplete.

Diagnosis before repair: the file appears to have been written against an
earlier version of its neighbours and to be missing `open` statements. Read
the CURRENT `KindDim.lean` and `KindDimLower.lean` (both build) and restate
the file against what they actually export. Deliverable: a `KindBox.lean` that
elaborates, with its own `#print axioms`, plus a line in `All.lean` importing
it. SCRUPLES must display your definition of covering number and box
dimension and argue that it agrees with the standard
lim log N(ε)/log(1/ε), including the squeeze from triadic to all scales —
the audit can certify the theorem, only prose can certify that it is the
right theorem.

## T37 — the missing paperwork (no building required)

- `AXIOM-AUDIT-round11.md`: never written. Reconstruct from the round-11
  census and the identifiers actually present.
- Census, scruples and audit for the interrupted session that produced
  `KindDimLower.lean` (`le_dimH_K`, `dimH_K_eq`, `kindMeasure`,
  `kindMeasure_K`, `kindMeasure_le`).
- `ABANDONED.md` §1 is stale: it records the Hausdorff lower bound as
  abandoned, though `KindDimLower.lean` proves it and CI has built it.
- Add a round-9 section to `GITHUB_HANDOFF_CHECKLIST` (§15.6 lists it as
  missing), and delete from §15.6 whatever this round closes.

## T38 — the counting operator (paper `prop:lebeigen`)

New, small, self-contained. Define the counting operator
(T h)(y) = (1/λ)[h(y/λ) + h((y+λ−1)/λ)] on (0,1). Prove that the constant
function 1 satisfies T 1 = (2/λ)·1 for every λ ∈ (1,2), because each branch is
a bijection from its legal domain onto (0,1), so every y has exactly one legal
preimage under each branch. Then the integral identity: ∫₀¹ K_λ(m,x) dx =
(2/λ)^m, where K_λ(m,x) is the number of kind words of length m from x.
Reuse the existing survival predicates rather than defining new ones.

## T39 (optional) — the trapezoid at λ = √2 (paper `prop:trapezoid`)

The backward measure at √2 is the distribution of (1−r)Σ εⱼ rʲ with fair bits
and r = 1/√2. Since r² = 1/2, splitting the sum over even and odd j gives two
independent uniform variables on [0,2]; hence the measure is the convolution
of uniforms on [0, 2−√2] and [0, √2−1], with the piecewise linear density
rising on [0,√2−1], constant at (2+√2)/2 on [√2−1, 2−√2], falling on
[2−√2, 1]. Formalise as much as is comfortable; a partial result with an
honest scruples note is fine.

## Deliverables

Census; sources; `#print axioms` for your own new theorems only; SCRUPLES
(T36's definitions above all); a round-13 section for the checklist. No
tree-wide build, no tree-wide audit, no push.
