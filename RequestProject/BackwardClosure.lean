import RequestProject.BranchBridge
import RequestProject.Density

/-!
# T42 — backward closure of the density set, and the two-letter reduction

Write `Φ_ε(x) = rapp lam x ε` for the action of a branch word `ε`
(`ExpCount.rapp`, identified with `Pisot.branchIter` by
`RequestProject.BranchBridge`).  Two things are proved here.

## The two-letter reduction (commissioned part (c))

`survives lam Move.R x` is *definitionally* `x < r lam`, which is
`branchLegal lam 0 x`, and `survives lam Move.L x` is `g lam < x`, which is
`branchLegal lam 1 x`; moreover `act lam Move.R = f lam 0` and
`act lam Move.L = f lam 1`.  So `0 ↦ R`, `1 ↦ L` (`toMove`) realises every
branch word as an `M`-free word of moves with the same survival condition and
the same endpoint (`survivesWord_map_toMove`, `posAfter_map_toMove`).

Consequently `DenseFrom lam (1/2)` — density in `(0,1)` of the endpoints of the
*branch* words legal from `1/2` — already implies `KindDense lam`
(`denseFrom_half_imp_kindDense`), and hence, through the certified
`KnotGame.N_unbounded_of_kindDense`, gives `N_λ = ∞`
(`N_unbounded_of_denseFrom_half`).  The two-letter analysis of paper §10.2 is
therefore the whole of the spreading problem, not a simplification of it.

## Backward closure (the originally commissioned part)

If `y = Φ_ε(x)` for a branch word `ε` legal from `x`, then the endpoints from
`y` at level `m` are among those from `x` at level `m + |ε|`
(`endpoints_subset_of_legal`).  Hence `y ∈ D → x ∈ D` where `D lam` is the set
of starting points with dense endpoint set (`denseFrom_of_image`,
`mem_D_of_image_mem_D`), and the complement of `D` is forward invariant
(`compl_D_forward_invariant`).

## Conventions (SCRUPLES)

* `DenseFrom lam x` uses the same shape of statement as `KnotGame.KindDense`:
  every `c < d` with `0 ≤ c`, `d ≤ 1` contains an endpoint *strictly* inside.
  With `x = 1/2` and the branch alphabet it is the hypothesis the paper's
  §10.2 discusses; nothing here certifies it for any particular `λ`.
* Words act on the left, as everywhere in this project: `rapp lam x (u ++ v)`
  applies `u` first.  Hence `ε` is a *prefix*, and the level shift is
  `m + |ε|`.
* No hypothesis on `λ` is needed for any statement in this file except the
  final `N_unbounded_of_denseFrom_half`, which inherits `1 < lam` from
  `KnotGame.N_unbounded_of_kindDense`.
-/

namespace KnotGame
namespace BackwardClosure

open KnotGame.CountingOperator KnotGame.ExpCount

variable {lam : ℝ}

/-! ### Branch words as `M`-free move words -/

/-- The move realising a branch: `0 ↦ R` (which keeps `x < r`) and `1 ↦ L`
(which keeps `g < x`). -/
def toMove : Fin 2 → Move := fun i => if i = 0 then Move.R else Move.L

@[simp] lemma toMove_zero : toMove 0 = Move.R := rfl

@[simp] lemma toMove_one : toMove 1 = Move.L := rfl

lemma survives_toMove (lam : ℝ) (i : Fin 2) (x : ℝ) :
    survives lam (toMove i) x ↔ branchLegal lam i x := by
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · rw [toMove_zero, survives_R, branchLegal_zero]
  · rw [toMove_one, survives_L, branchLegal_one]

lemma act_toMove (lam : ℝ) (i : Fin 2) (x : ℝ) : act lam (toMove i) x = f lam i x := by
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · rw [toMove_zero, act_R, f_zero]
  · rw [toMove_one, act_L, f_one]

/-- A branch word is legal from `x` exactly when the corresponding `M`-free word
of moves is survived by a knot at `x`. -/
lemma survivesWord_map_toMove (lam : ℝ) :
    ∀ (x : ℝ) (w : List (Fin 2)),
      survivesWord lam x (w.map toMove) ↔ branchSurvivesWord lam x w
  | _, [] => by simp [branchSurvivesWord]
  | x, (i :: w) => by
      rw [List.map_cons, survivesWord_cons, act_toMove, survives_toMove]
      show _ ∧ survivesWord lam (f lam i x) (w.map toMove) ↔
        branchLegal lam i x ∧ branchSurvivesWord lam (f lam i x) w
      rw [survivesWord_map_toMove lam (f lam i x) w]

/-- The endpoint of a branch word and of the move word realising it agree. -/
lemma posAfter_map_toMove (lam : ℝ) :
    ∀ (x : ℝ) (w : List (Fin 2)), posAfter lam x (w.map toMove) = rapp lam x w
  | _, [] => rfl
  | x, (i :: w) => by
      rw [List.map_cons, posAfter_cons, act_toMove, rapp_cons,
        posAfter_map_toMove lam (f lam i x) w]

/-! ### The density set -/

/-- The endpoints, at level `m`, of the branch words legal from `x`. -/
def endpoints (lam x : ℝ) (m : ℕ) : Set ℝ :=
  {y | ∃ w : List (Fin 2), w.length = m ∧ branchSurvivesWord lam x w ∧ rapp lam x w = y}

/-- **Density of the branch endpoints from `x`.**  Every nonempty open
subinterval of `(0,1)` contains `Φ_ε(x)` for some branch word `ε` legal from
`x`.  Certified for no particular `λ`. -/
def DenseFrom (lam x : ℝ) : Prop :=
  ∀ c d : ℝ, 0 ≤ c → c < d → d ≤ 1 → ∃ w : List (Fin 2),
    branchSurvivesWord lam x w ∧ c < rapp lam x w ∧ rapp lam x w < d

/-- `D lam` — the starting points whose branch endpoints are dense in `(0,1)`. -/
def D (lam : ℝ) : Set ℝ := {x | DenseFrom lam x}

lemma mem_D_iff {x : ℝ} : x ∈ D lam ↔ DenseFrom lam x := Iff.rfl

/-! ### (c) Density from `1/2` already gives `KindDense` -/

/-- **T42(c).**  Density of the *branch* endpoints from `1/2` implies the
paper's `KindDense`: the branch words are realised by `M`-free move words with
the same endpoints. -/
theorem denseFrom_half_imp_kindDense (H : DenseFrom lam (1/2)) : KindDense lam := by
  intro c d hc hcd hd
  obtain ⟨w, hw, h1, h2⟩ := H c d hc hcd hd
  refine ⟨w.map toMove, (survivesWord_map_toMove lam (1/2) w).2 hw, ?_, ?_⟩
  · rwa [posAfter_map_toMove]
  · rwa [posAfter_map_toMove]

/-- **T42(c), the conclusion.**  Density of the branch endpoints from `1/2`
alone forces the knot counts to be unbounded.  (Composition of
`denseFrom_half_imp_kindDense` with the certified
`KnotGame.N_unbounded_of_kindDense`.) -/
theorem N_unbounded_of_denseFrom_half (h : 1 < lam) (H : DenseFrom lam (1/2)) :
    ∀ K : ℕ, ∃ n : ℕ, K ≤ N lam n :=
  N_unbounded_of_kindDense h (denseFrom_half_imp_kindDense H)

/-! ### (T44) The converse: every kind word is realised by a branch word -/

/-- **The step lemma.**  A surviving move is a legal branch: for `L` and `R` the
two predicates are literally the same, and for `M` survival puts `x` in
`(0, r/2) ∪ (1 - r/2, 1)`, where `r/2 < r` and `1 - r/2 > g` make the branch
actually taken legal.  This is the only place where `1 < lam` is needed. -/
lemma branchLegal_branch (hlam : 1 < lam) {m : Move} {x : ℝ}
    (hs : survives lam m x) : branchLegal lam (branch lam m x) x := by
  have hr : 0 < r lam := KnotGame.r_pos lam hlam
  cases m with
  | L => rw [branch_L, branchLegal_one]; exact hs
  | R => rw [branch_R, branchLegal_zero]; exact hs
  | M =>
      rw [survives_M] at hs
      by_cases hx : x < r lam / 2
      · rw [branch_M, if_pos hx, branchLegal_zero]; linarith
      · rw [branch_M, if_neg hx, branchLegal_one]
        have hx2 : 1 - r lam / 2 < x := hs.resolve_left hx
        rw [g]; linarith

/-- The branch word taken by a knot at `x` along a word of moves. -/
noncomputable def branchWordOf (lam : ℝ) : ℝ → List Move → List (Fin 2)
  | _, [] => []
  | x, m :: w => branch lam m x :: branchWordOf lam (act lam m x) w

@[simp] lemma branchWordOf_nil (lam : ℝ) (x : ℝ) : branchWordOf lam x [] = [] := rfl

@[simp] lemma branchWordOf_cons (lam : ℝ) (x : ℝ) (m : Move) (w : List Move) :
    branchWordOf lam x (m :: w) = branch lam m x :: branchWordOf lam (act lam m x) w := rfl

/-- The branch word taken along a move word has the same endpoint. -/
lemma rapp_branchWordOf (lam : ℝ) :
    ∀ (x : ℝ) (w : List Move), rapp lam x (branchWordOf lam x w) = posAfter lam x w
  | _, [] => rfl
  | x, (m :: w) => by
      rw [branchWordOf_cons, rapp_cons, posAfter_cons]
      show rapp lam (act lam m x) (branchWordOf lam (act lam m x) w) = _
      exact rapp_branchWordOf lam (act lam m x) w

/-- The branch word taken along a survived move word is legal. -/
lemma branchSurvivesWord_branchWordOf (hlam : 1 < lam) :
    ∀ (x : ℝ) (w : List Move), survivesWord lam x w →
      branchSurvivesWord lam x (branchWordOf lam x w)
  | _, [], _ => trivial
  | x, (m :: w), hw => by
      rw [survivesWord_cons] at hw
      refine ⟨branchLegal_branch hlam hw.1, ?_⟩
      show branchSurvivesWord lam (act lam m x) (branchWordOf lam (act lam m x) w)
      exact branchSurvivesWord_branchWordOf hlam (act lam m x) w hw.2

/-- **T44.**  Forbidding the middle move loses no endpoint: density of the kind
endpoints from `1/2` implies density of the *branch* endpoints from `1/2`. -/
theorem kindDense_imp_denseFrom_half (hlam : 1 < lam) (H : KindDense lam) :
    DenseFrom lam (1/2) := by
  intro c d hc hcd hd
  obtain ⟨u, hu, h1, h2⟩ := H c d hc hcd hd
  refine ⟨branchWordOf lam (1/2) u, branchSurvivesWord_branchWordOf hlam (1/2) u hu, ?_, ?_⟩
  · rwa [rapp_branchWordOf]
  · rwa [rapp_branchWordOf]

/-- **T44, the biconditional.**  For `1 < lam` the two density hypotheses are
equivalent: the two-letter analysis is the whole of the spreading problem.
(The direction `DenseFrom → KindDense` needs no hypothesis on `lam`.) -/
theorem denseFrom_half_iff_kindDense (hlam : 1 < lam) :
    DenseFrom lam (1/2) ↔ KindDense lam :=
  ⟨denseFrom_half_imp_kindDense, kindDense_imp_denseFrom_half hlam⟩

/-! ### Backward closure -/

/-- **The prepending lemma for endpoint sets.**  If `ε` is legal from `x` and
`y = Φ_ε(x)`, the level-`m` endpoints from `y` are level-`(m + |ε|)` endpoints
from `x`. -/
theorem endpoints_subset_of_legal {x : ℝ} {e : List (Fin 2)}
    (he : branchSurvivesWord lam x e) (m : ℕ) :
    endpoints lam (rapp lam x e) m ⊆ endpoints lam x (m + e.length) := by
  rintro y ⟨w, hlen, hw, rfl⟩
  refine ⟨e ++ w, ?_, ?_, ?_⟩
  · rw [List.length_append, hlen, Nat.add_comm]
  · exact (BranchBridge.branchSurvivesWord_append lam x e w).2 ⟨he, hw⟩
  · rw [rapp_append]

/-- **Backward closure of `D`.**  If some legal image of `x` has dense endpoint
set, so has `x`. -/
theorem denseFrom_of_image {x : ℝ} {e : List (Fin 2)} (he : branchSurvivesWord lam x e)
    (hy : DenseFrom lam (rapp lam x e)) : DenseFrom lam x := by
  intro c d hc hcd hd
  obtain ⟨w, hw, h1, h2⟩ := hy c d hc hcd hd
  refine ⟨e ++ w, (BranchBridge.branchSurvivesWord_append lam x e w).2 ⟨he, hw⟩, ?_, ?_⟩
  · rwa [rapp_append]
  · rwa [rapp_append]

lemma mem_D_of_image_mem_D {x : ℝ} {e : List (Fin 2)} (he : branchSurvivesWord lam x e)
    (hy : rapp lam x e ∈ D lam) : x ∈ D lam :=
  denseFrom_of_image he hy

/-- **The complement of `D` is forward invariant.**  Every legal image of a
point without dense endpoint set again has no dense endpoint set. -/
theorem compl_D_forward_invariant {x : ℝ} {e : List (Fin 2)}
    (he : branchSurvivesWord lam x e) (hx : x ∈ (D lam)ᶜ) : rapp lam x e ∈ (D lam)ᶜ :=
  fun hy => hx (mem_D_of_image_mem_D he hy)

/-- The structural handle of the open problem, in the form the paper uses it:
to prove `N_λ = ∞` it suffices to find **one** point of the forward branch orbit
of `1/2` whose own endpoints are dense. -/
theorem N_unbounded_of_orbit_point_denseFrom (h : 1 < lam) {e : List (Fin 2)}
    (he : branchSurvivesWord lam (1/2) e) (hy : DenseFrom lam (rapp lam (1/2) e)) :
    ∀ K : ℕ, ∃ n : ℕ, K ≤ N lam n :=
  N_unbounded_of_denseFrom_half h (denseFrom_of_image he hy)

end BackwardClosure
end KnotGame
