import RequestProject.Basic

/-!
# Lemma 1.1: distinctness (Work Order 2)

Two knots surviving the same move have distinct images; no surviving knot is
carried to `1/2` by `M`; hence the number of knots after a move is the number of
survivors, together with one more when the move is `M`.

The straddling case is the only one with content: from `x < r/2` and
`y > 1 - r/2` one gets `y - x > g` and then `lam*(y-x) - (lam-1) > 0`.
-/

namespace KnotGame

variable {lam : ℝ}

lemma lam_mul_r (h : 1 < lam) : lam * r lam = 1 := by
  have h0 : lam ≠ 0 := ne_of_gt (lt_trans zero_lt_one h)
  rw [r, mul_inv_cancel₀ h0]

lemma lam_mul_g (h : 1 < lam) : lam * g lam = lam - 1 := by
  have := lam_mul_r h
  simp only [g, mul_sub, mul_one, this]

/-- The straddling estimate: if `x` is below and `y` above the interval deleted
by `M`, then `f₁ y - f₀ x > 0`. -/
lemma straddle (h : 1 < lam) {x y : ℝ} (hx : x < r lam / 2)
    (hy : 1 - r lam / 2 < y) : lam * x < lam * y - (lam - 1) := by
  have hgap : g lam < y - x := by
    simp only [g]; linarith
  have hlam : (0:ℝ) < lam := lt_trans zero_lt_one h
  have : lam * g lam < lam * (y - x) := mul_lt_mul_of_pos_left hgap hlam
  rw [lam_mul_g h] at this
  linarith [this]

/-- **Lemma 1.1, first part.** Two knots surviving the same move have distinct
images. -/
theorem act_injOn (h : 1 < lam) (m : Move) {x y : ℝ}
    (hx : survives lam m x) (hy : survives lam m y)
    (hxy : act lam m x = act lam m y) : x = y := by
  have hlam : (0:ℝ) < lam := lt_trans zero_lt_one h
  cases m
  · -- L
    rw [act_L, act_L] at hxy
    have : lam * x = lam * y := by linarith
    exact mul_left_cancel₀ (ne_of_gt hlam) this
  · -- M
    simp only [survives_M] at hx hy
    by_cases hx' : x < r lam / 2 <;> by_cases hy' : y < r lam / 2
    · rw [act_M_of_lt lam x hx', act_M_of_lt lam y hy'] at hxy
      exact mul_left_cancel₀ (ne_of_gt hlam) hxy
    · rw [act_M_of_lt lam x hx', act_M_of_gt lam y hy'] at hxy
      have hy2 : 1 - r lam / 2 < y := hy.resolve_left hy'
      exact absurd hxy (ne_of_lt (straddle h hx' hy2))
    · rw [act_M_of_gt lam x hx', act_M_of_lt lam y hy'] at hxy
      have hx2 : 1 - r lam / 2 < x := hx.resolve_left hx'
      exact absurd hxy.symm (ne_of_lt (straddle h hy' hx2))
    · rw [act_M_of_gt lam x hx', act_M_of_gt lam y hy'] at hxy
      have : lam * x = lam * y := by linarith
      exact mul_left_cancel₀ (ne_of_gt hlam) this
  · -- R
    rw [act_R, act_R] at hxy
    exact mul_left_cancel₀ (ne_of_gt hlam) hxy

/-- **Lemma 1.1, second part.** No surviving knot is carried to `1/2` by `M`. -/
theorem act_M_ne_half (h : 1 < lam) {x : ℝ} (hx : survives lam Move.M x) :
    act lam Move.M x ≠ 1 / 2 := by
  have hlam : (0:ℝ) < lam := lt_trans zero_lt_one h
  simp only [survives_M] at hx
  by_cases hx' : x < r lam / 2
  · rw [act_M_of_lt lam x hx']
    have : lam * x < lam * (r lam / 2) := mul_lt_mul_of_pos_left hx' hlam
    rw [show lam * (r lam / 2) = (lam * r lam) / 2 by ring, lam_mul_r h] at this
    exact ne_of_lt this
  · have hx2 : 1 - r lam / 2 < x := hx.resolve_left hx'
    rw [act_M_of_gt lam x hx']
    have : lam * (1 - r lam / 2) < lam * x := mul_lt_mul_of_pos_left hx2 hlam
    rw [show lam * (1 - r lam / 2) = lam - (lam * r lam) / 2 by ring, lam_mul_r h] at this
    have : (1:ℝ)/2 < lam * x - (lam - 1) := by linarith
    exact ne_of_gt this

@[simp] lemma mem_survivors {m : Move} {S : Finset ℝ} {x : ℝ} :
    x ∈ survivors lam m S ↔ x ∈ S ∧ survives lam m x := Finset.mem_filter

/-- The images of the survivors form a set of the same cardinality. -/
lemma card_image_survivors (h : 1 < lam) (m : Move) (S : Finset ℝ) :
    ((survivors lam m S).image (act lam m)).card = (survivors lam m S).card := by
  apply Finset.card_image_of_injOn
  intro x hx y hy hxy
  simp only [Finset.coe_filter, survivors, Set.mem_setOf_eq] at hx hy
  exact act_injOn h m hx.2 hy.2 hxy

/-- `1/2` is not the image of a survivor of `M`. -/
lemma half_not_mem_image (h : 1 < lam) (S : Finset ℝ) :
    (1:ℝ)/2 ∉ (survivors lam Move.M S).image (act lam Move.M) := by
  simp only [Finset.mem_image, mem_survivors, not_exists]
  rintro x ⟨⟨-, hx⟩, hxa⟩
  exact act_M_ne_half h hx hxa

/-- **Lemma 1.1, third part.** The number of knots after a move is the number of
survivors, together with one more when the move is `M`. -/
theorem card_step (h : 1 < lam) (m : Move) (S : Finset ℝ) :
    (step lam m S).card = (survivors lam m S).card + (if m = Move.M then 1 else 0) := by
  cases m
  · simp [step_L, card_image_survivors h]
  · rw [step_M]
    rw [Finset.union_comm, Finset.card_union_of_disjoint, card_image_survivors h]
    · simp [Finset.card_singleton]; ring
    · simp only [Finset.disjoint_singleton_left]
      exact half_not_mem_image h S
  · simp [step_R, card_image_survivors h]

end KnotGame
