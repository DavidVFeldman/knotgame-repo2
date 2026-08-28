import RequestProject.SurvivorSet

/-!
# T16 — one annihilation per backward step (paper Lemma `lem:oneperstep`)

Read backwards, each knot moves by one of the two inverse branches
`y ↦ r y` and `y ↦ r y + (1 - r)`.  At a move `L` or `R` a single branch is
used; at a move `M` the branch is decided by the side of `1/2` the knot is on.
The two branches are injective with disjoint images — `[0, r)` and `[1-r, 1]`
at `L` and `R`, `[0, r/2)` and `(1 - r/2, 1]` at `M` — so every composite of
inverse branches is injective, and at most one point is carried to `1/2` at any
backward step.

Forward, this is the statement that `x ↦ posAfter lam x v` is injective on the
set of points surviving `v` (`posAfter_inj`), whence `annihilation_unique`.
-/

namespace KnotGame

variable {lam : ℝ}

/-- The inverse branch of a move, as used when a run is read backwards. -/
noncomputable def invBranch (lam : ℝ) : Move → ℝ → ℝ
  | Move.L, y => r lam * y + (1 - r lam)
  | Move.R, y => r lam * y
  | Move.M, y => if y < 1/2 then r lam * y else r lam * y + (1 - r lam)

@[simp] lemma invBranch_L (y : ℝ) : invBranch lam Move.L y = r lam * y + (1 - r lam) := rfl
@[simp] lemma invBranch_R (y : ℝ) : invBranch lam Move.R y = r lam * y := rfl
lemma invBranch_M (y : ℝ) :
    invBranch lam Move.M y = if y < 1/2 then r lam * y else r lam * y + (1 - r lam) := rfl

/-- The lower inverse branch at `M` lands in `[0, r/2)`. -/
lemma invBranch_M_of_lt (h : 1 < lam) {y : ℝ} (hy : 0 ≤ y) (hy2 : y < 1/2) :
    0 ≤ invBranch lam Move.M y ∧ invBranch lam Move.M y < r lam / 2 := by
  have hr0 : 0 < r lam := r_pos lam h
  rw [invBranch_M, if_pos hy2]
  constructor
  · positivity
  · nlinarith

/-- The upper inverse branch at `M` lands in `(1 - r/2, 1]`. -/
lemma invBranch_M_of_ge (h : 1 < lam) {y : ℝ} (hy : 1/2 ≤ y) (hy1 : y ≤ 1) :
    1 - r lam / 2 ≤ invBranch lam Move.M y ∧ invBranch lam Move.M y ≤ 1 := by
  have hr0 : 0 < r lam := r_pos lam h
  rw [invBranch_M, if_neg (by linarith)]
  constructor <;> nlinarith

/-- The inverse branch at `R` lands in `[0, r)`. -/
lemma invBranch_R_mem (h : 1 < lam) {y : ℝ} (hy : 0 ≤ y) (hy1 : y < 1) :
    0 ≤ invBranch lam Move.R y ∧ invBranch lam Move.R y < r lam := by
  have hr0 : 0 < r lam := r_pos lam h
  refine ⟨by simp only [invBranch_R]; positivity, ?_⟩
  simpa using by nlinarith

/-- The inverse branch at `L` lands in `[1-r, 1]`. -/
lemma invBranch_L_mem (h : 1 < lam) {y : ℝ} (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    1 - r lam ≤ invBranch lam Move.L y ∧ invBranch lam Move.L y ≤ 1 := by
  have hr0 : 0 < r lam := r_pos lam h
  constructor <;> (simp only [invBranch_L]; nlinarith)

/-- **T16, the branch step.**  Each inverse branch is injective. -/
theorem invBranch_injective (h : 1 < lam) (m : Move) : Function.Injective (invBranch lam m) := by
  have hr0 : 0 < r lam := r_pos lam h
  have hr1 : r lam < 1 := r_lt_one lam h
  intro x y hxy
  cases m
  · simp only [invBranch_L] at hxy
    have : r lam * x = r lam * y := by linarith
    exact mul_left_cancel₀ (ne_of_gt hr0) this
  · simp only [invBranch_M] at hxy
    by_cases hx : x < 1/2 <;> by_cases hy : y < 1/2
    · rw [if_pos hx, if_pos hy] at hxy
      exact mul_left_cancel₀ (ne_of_gt hr0) hxy
    · rw [if_pos hx, if_neg hy] at hxy
      push_neg at hy
      nlinarith
    · rw [if_neg hx, if_pos hy] at hxy
      push_neg at hx
      nlinarith
    · rw [if_neg hx, if_neg hy] at hxy
      have : r lam * x = r lam * y := by linarith
      exact mul_left_cancel₀ (ne_of_gt hr0) this
  · simp only [invBranch_R] at hxy
    exact mul_left_cancel₀ (ne_of_gt hr0) hxy

/-- The inverse branch undoes the move on a knot that survives it. -/
theorem invBranch_act (h : 1 < lam) (m : Move) {x : ℝ} (hx : survives lam m x) :
    invBranch lam m (act lam m x) = x := by
  have hr0 : 0 < r lam := r_pos lam h
  have hlr : lam * r lam = 1 := lam_mul_r h
  have hlam : (0:ℝ) < lam := lt_trans zero_lt_one h
  cases m
  · simp only [act_L, invBranch_L]
    have : r lam * (lam * x) = x := by
      rw [← mul_assoc, mul_comm (r lam) lam, hlr, one_mul]
    nlinarith [this]
  · rcases hx with hx | hx
    · rw [act_M_of_lt lam x hx, invBranch_M, if_pos (by nlinarith)]
      rw [← mul_assoc, mul_comm (r lam) lam, hlr, one_mul]
    · have hnlt : ¬ x < r lam / 2 := by
        have := half_lt_one_sub_half h
        push_neg; linarith
      rw [act_M_of_gt lam x hnlt, invBranch_M, if_neg (by nlinarith)]
      have : r lam * (lam * x) = x := by
        rw [← mul_assoc, mul_comm (r lam) lam, hlr, one_mul]
      nlinarith [this]
  · simp only [act_R, invBranch_R]
    rw [← mul_assoc, mul_comm (r lam) lam, hlr, one_mul]

/-- **T16, forward reading.**  Every composite of inverse branches is
injective: two points that survive the word `v` and are carried to the same
place by it are equal. -/
theorem posAfter_inj (h : 1 < lam) : ∀ (v : List Move) {x y : ℝ},
    survivesWord lam x v → survivesWord lam y v → posAfter lam x v = posAfter lam y v → x = y
  | [], x, y, _, _, hxy => by simpa using hxy
  | m :: v, x, y, hx, hy, hxy => by
      rw [survivesWord_cons] at hx hy
      rw [posAfter_cons, posAfter_cons] at hxy
      exact act_injOn h m hx.1 hy.1 (posAfter_inj h v hx.2 hy.2 hxy)

/-- **T16** (paper Lemma `lem:oneperstep`).  At each backward step at most one
point is annihilated: at most one point surviving `v` is carried to `1/2`. -/
theorem annihilation_unique (h : 1 < lam) (v : List Move) {x y : ℝ}
    (hx : survivesWord lam x v) (hy : survivesWord lam y v)
    (hx2 : posAfter lam x v = 1/2) (hy2 : posAfter lam y v = 1/2) : x = y :=
  posAfter_inj h v hx hy (by rw [hx2, hy2])

end KnotGame
