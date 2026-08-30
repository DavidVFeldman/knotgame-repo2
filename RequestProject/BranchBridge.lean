import RequestProject.ExpCount
import RequestProject.CountingOperator
import RequestProject.Pisot

/-!
# T39.5 — bridging the three copies of the branch-word layer (round 14)

The round-14 census found the branch-word layer defined three times, in modules
with disjoint import paths:

* `Branching.BLegal` / `Branching.bSurvives` (in `BranchingCount`) and
  `ExpCount.rapp`, `ExpCount.SW`, `ExpCount.Kx` — the *counting* chain;
* `CountingOperator.branchLegal` / `branchSurvivesWord` / `branchWords` /
  `bcount` — the *operator* chain of round 13;
* `KnotGame.branchIter` in `Pisot` — the *orbit* chain.

This module is the single bridge between them.  It adds **no** new notion of
legality, survival or word action: every declaration below is an equality or an
`Iff` between definitions that already exist.

## Contents

* `branchLegal_iff_BLegal` — the two legality predicates are the same
  (they are the same formula verbatim);
* `branchSurvivesWord_iff_bSurvives` — the two word-survival predicates agree;
* `rapp_eq_branchIter` — the two word actions agree;
* `branchWords_eq_SW` and `bcount_eq_Kx` — the two counting layers agree, so
  round 13's `integral_bcount` is a statement about `ExpCount.Kx`;
* `rapp_append`, `branchSurvivesWord_append` — the append laws, available on
  the operator side of the bridge.

## Conventions (SCRUPLES)

* No definition is repeated here, and no fourth copy is introduced.  Later
  round-14 modules (`Contraction`, `EquiMean`, `BackwardClosure`) use the
  `CountingOperator` names for legality and survival and the `ExpCount` name
  `rapp` for the action of a word, which is the pairing the commission asks
  for (`integral_bcount` on one side, `rapp_append` on the other).
* `Branching.BLegal` is `noncomputable` (it mentions `r lam`) while
  `CountingOperator.branchLegal` is not; they are nevertheless the same
  proposition, and `branchLegal_iff_BLegal` is proved by `Iff.rfl` after
  unfolding.
-/

namespace KnotGame
namespace BranchBridge

open KnotGame.Branching KnotGame.CountingOperator KnotGame.ExpCount

variable {lam : ℝ}

/-! ### Legality -/

/-- The two legality predicates for a single branch are the same. -/
theorem branchLegal_iff_BLegal (lam : ℝ) (i : Fin 2) (x : ℝ) :
    branchLegal lam i x ↔ BLegal lam i x := by
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · rw [branchLegal_zero, BLegal_zero]
  · rw [branchLegal_one, BLegal_one]

/-! ### Survival along a word -/

/-- The two word-survival predicates are the same. -/
theorem branchSurvivesWord_iff_bSurvives (lam : ℝ) :
    ∀ (x : ℝ) (w : List (Fin 2)), branchSurvivesWord lam x w ↔ bSurvives lam x w
  | _, [] => Iff.rfl
  | x, (i :: w) => by
      show branchLegal lam i x ∧ branchSurvivesWord lam (f lam i x) w ↔
        BLegal lam i x ∧ bSurvives lam (f lam i x) w
      rw [branchLegal_iff_BLegal, branchSurvivesWord_iff_bSurvives lam (f lam i x) w]

/-! ### The action of a word -/

/-- The two word actions are the same. -/
theorem rapp_eq_branchIter (lam : ℝ) :
    ∀ (x : ℝ) (w : List (Fin 2)), rapp lam x w = branchIter lam w x
  | _, [] => rfl
  | x, (i :: w) => by
      rw [rapp_cons, branchIter, rapp_eq_branchIter lam (f lam i x) w]

/-! ### Appending, on the operator side -/

/-- `rapp_append` transported to the `branchIter` name of `Pisot`. -/
theorem branchIter_append (lam x : ℝ) (u v : List (Fin 2)) :
    branchIter lam (u ++ v) x = branchIter lam v (branchIter lam u x) := by
  rw [← rapp_eq_branchIter, ← rapp_eq_branchIter, ← rapp_eq_branchIter, rapp_append]

/-- Survival along a concatenation, in the `CountingOperator` vocabulary. -/
theorem branchSurvivesWord_append (lam x : ℝ) (u v : List (Fin 2)) :
    branchSurvivesWord lam x (u ++ v) ↔
      branchSurvivesWord lam x u ∧ branchSurvivesWord lam (rapp lam x u) v := by
  rw [branchSurvivesWord_iff_bSurvives, branchSurvivesWord_iff_bSurvives,
    branchSurvivesWord_iff_bSurvives, bSurvives_append]

/-! ### Counting -/

/-- The two finsets of legal words of a given length are the same. -/
theorem branchWords_eq_SW (lam x : ℝ) (m : ℕ) : branchWords lam x m = SW lam x m := by
  ext w
  rw [mem_branchWords, mem_SW, branchSurvivesWord_iff_bSurvives]

/-- Round 13's `bcount` is round 7's `Kx`.  In particular `integral_bcount`
says that the mean of `Kx lam · m` over `(0,1)` is `(2/λ)^m`. -/
theorem bcount_eq_Kx (lam x : ℝ) (m : ℕ) : bcount lam x m = (Kx lam x m : ℝ) := by
  rw [bcount_eq_card, branchWords_eq_SW, Kx]

end BranchBridge
end KnotGame
