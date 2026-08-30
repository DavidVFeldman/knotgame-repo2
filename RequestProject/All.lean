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
-- KindBox (box dimension of the kind set) was quarantined through round 12 as
-- unbuildable; round 13 (T36) restated it against what KindDim and
-- KindDimLower actually export, replaced the bracketing index, and supplied
-- the missing squeeze from triadic to all scales. It now elaborates and is
-- back in the import closure.
import RequestProject.KindBox
-- CountingOperator (round 13, T38): the two-branch transfer operator T, the
-- eigenvalue T 1 = (2/lam) 1, and the two mean-count integrals.
import RequestProject.CountingOperator
-- Trapezoid (round 13, T39): the even/odd splitting of the backward series at
-- lambda = sqrt 2, the convolution of the two uniform laws, and the
-- trapezoidal density.
import RequestProject.Trapezoid
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
-- BranchBridge (round 14, T39.5): the three copies of the branch-word layer
-- are identified with one another.
import RequestProject.BranchBridge
-- BackwardClosure (round 14, T42): branch words as M-free move words, density
-- from 1/2 implies KindDense, and the backward closure of the density set.
import RequestProject.BackwardClosure
-- Contraction (round 14, T40): the normalised counting operator P, its
-- contraction of the Lipschitz seminorm, and uniform convergence to a constant.
import RequestProject.Contraction
-- EquiMean (round 14, T41): the adjoint S of T, the endpoint propagator, and
-- equidistribution in mean.
import RequestProject.EquiMean
-- InvariantMeasure (round 15, T45): an invariant probability measure carried by
-- the unit interval, the law of the binary digit series of a uniform real, and
-- its invariance for the normalised counting operator.
import RequestProject.InvariantMeasure

/-!
# Knot counts in an interval deletion game

This file collects the whole development; see `CENSUS.md` for the map from the
statements of the paper to the Lean identifiers.
-/
