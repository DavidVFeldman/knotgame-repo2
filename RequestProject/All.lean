import RequestProject.Basic
import RequestProject.Distinct
import RequestProject.Suffix
import RequestProject.Threshold
import RequestProject.Golden
import RequestProject.Littlewood
import RequestProject.Pisot
import RequestProject.Plastic
import RequestProject.Sqrt2
import RequestProject.Gaps
import RequestProject.GoldenEffective
import RequestProject.PlasticOrbit
import RequestProject.Tribonacci
import RequestProject.Supergolden
import RequestProject.Transversality
import RequestProject.PairCounting
import RequestProject.Branching
import RequestProject.BranchingContinuum
import RequestProject.BranchingCount
import RequestProject.CommonWindow
import RequestProject.SurvivorSet
import RequestProject.Backward
import RequestProject.Permanence
import RequestProject.Compactness
import RequestProject.Density
import RequestProject.Deficit
import RequestProject.Candidates
import RequestProject.CandidateInstance
import RequestProject.RunRational
import RequestProject.TwoStep
import RequestProject.RecordDepths
import RequestProject.PlasticIndex
import RequestProject.PlasticTbl
import RequestProject.PlasticCert
import RequestProject.ExpLower
import RequestProject.ExpWindow
import RequestProject.ExpSharp
import RequestProject.ReturnTail
import RequestProject.Ternary
import RequestProject.Mahler
import RequestProject.PeriodicYield
import RequestProject.KindTree
import RequestProject.WindowSharp
import RequestProject.Translation
import RequestProject.DensityQuant
import RequestProject.NoRecurrence
import RequestProject.ExpSharper
import RequestProject.ExpAbove
import RequestProject.Overlap
import RequestProject.Immortal
import RequestProject.PisotDecide
import RequestProject.CircleForm
import RequestProject.KindDim
import RequestProject.Square
import RequestProject.RecordLower
-- PlasticConfig (the 25,525-state closure at the plastic number) and its
-- dependent PlasticOrbitCount are quarantined from this closure: the kernel
-- reduction exceeds the CI runner's memory. UNLIKE the ExpSharpest case, the
-- results in them ARE covered by a completed audit (AXIOM-AUDIT-round5.md),
-- so the paper's claim N_rho = 7 stands on that audit; the exclusion here is
-- a hardware limit, not a doubt. See heavy.yml and UNBUILT.md.
--
-- ExpSharpest (and its Data*/Checks* files) is quarantined from the import
-- closure: its kernel checks exceed the memory of the CI runner, so it has
-- never completed a build and has no axiom audit. See ABANDONED.md and the
-- CI workflow. The audited sharper rate is ExpSharper's 26^(1/14).
import RequestProject.KindDimLower
-- KindBox (box dimension of the kind set) is quarantined: it DOES NOT
-- COMPILE. CI shows unknown namespace `KindDimLower`, unknown identifiers
-- `cyl`, `dexp`, `atTop`, `Tendsto`, and two declarations using `sorry`. It
-- was reported complete and sorry-free by the session that wrote it; it had
-- never been elaborated. See UNBUILT.md.
import RequestProject.Lucas
import RequestProject.FourierFloor
import RequestProject.PlasticFourier
import RequestProject.SupergoldenFourier
import RequestProject.TribonacciFourier
import RequestProject.FourierEnclosure
import RequestProject.RecordGaps
import RequestProject.ImmortalMahler
import RequestProject.FourierGeneral
import RequestProject.FourierReflect

/-!
# Knot counts in an interval deletion game

This file collects the whole development; see `CENSUS.md` for the map from the
statements of the paper to the Lean identifiers.
-/
