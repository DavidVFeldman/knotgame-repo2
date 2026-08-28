import RequestProject.Suffix

/-!
# Proposition 4.1: the threshold at `lam = 2` (Work Order 4)

Every move multiplies one of `x` and `1 - x` by `lam`; a knot survives only if
`min x (1-x) < r`; hence `N n = 1` for all `n ≥ 1` if and only if `2 ≤ lam`.
-/

namespace KnotGame

variable {lam : ℝ}

/-- `f₀` multiplies `x` by `lam`. -/
lemma f_zero_eq (x : ℝ) : f lam 0 x = lam * x := f_zero lam x

/-- `f₁` multiplies `1 - x` by `lam`. -/
lemma one_sub_f_one (x : ℝ) : 1 - f lam 1 x = lam * (1 - x) := by
  simp only [f_one]; ring

/-- Every move multiplies one of `x` and `1 - x` by `lam`. -/
lemma act_mul (m : Move) (x : ℝ) :
    act lam m x = lam * x ∨ 1 - act lam m x = lam * (1 - x) := by
  unfold act
  rcases Fin.exists_fin_two.mp ⟨branch lam m x, rfl⟩ with h | h
  · exact Or.inl (by rw [h]; exact f_zero lam x)
  · exact Or.inr (by rw [h]; exact one_sub_f_one x)

/-- A knot survives a move only if `min x (1-x) < r`. -/
theorem survives_imp_min_lt_r (h : 1 < lam) {m : Move} {x : ℝ}
    (hx : survives lam m x) : min x (1 - x) < r lam := by
  have h0 : 0 < r lam := r_pos lam h
  cases m
  · have : g lam < x := hx
    have : 1 - x < r lam := by simp only [g] at this; linarith
    exact lt_of_le_of_lt (min_le_right _ _) this
  · rcases hx with hx | hx
    · exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    · exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  · exact lt_of_le_of_lt (min_le_left _ _) hx

/-- For `2 ≤ lam` the newborn knot at `1/2` is destroyed by whichever move
follows its birth. -/
lemma half_not_survives (h : 1 < lam) (h2 : 2 ≤ lam) (m : Move) :
    ¬ survives lam m (1/2) := by
  have h0 : 0 < lam := lt_trans zero_lt_one h
  have hr : r lam * lam = 1 := by rw [mul_comm]; exact lam_mul_r h
  have hr2 : r lam ≤ 1/2 := by nlinarith
  have hrpos : 0 < r lam := r_pos lam h
  cases m
  · simp only [survives_L, g, not_lt]; linarith
  · simp only [survives_M, not_or, not_lt]
    constructor <;> linarith
  · simp only [survives_R, not_lt]; linarith

lemma survivesWord_half_cons (h : 1 < lam) (h2 : 2 ≤ lam) (m : Move) (w : List Move) :
    ¬ survivesWord lam (1/2) (m :: w) := by
  rw [survivesWord_cons]
  exact fun hh => half_not_survives h h2 m hh.1

/-- For `2 ≤ lam` no two knots ever coexist. -/
lemma births_le_one (h : 1 < lam) (h2 : 2 ≤ lam) (w : List Move) : births lam w ≤ 1 := by
  induction w with
  | nil => simp
  | cons m w ih =>
      rw [births_cons]
      cases w with
      | nil => simp only [births_nil]; split <;> simp
      | cons m' w' =>
          rw [if_neg (by
            rintro ⟨-, hs⟩
            exact survivesWord_half_cons h h2 m' w' hs)]
          simpa using ih

/-- The run `L…LM` of length `n ≥ 1` produces one knot. -/
lemma one_le_N (h : 1 < lam) {n : ℕ} (hn : 1 ≤ n) : 1 ≤ N lam n := by
  have hlen : (List.replicate (n-1) Move.L ++ [Move.M]).length = n := by
    simp [List.length_append]
    omega
  have h1 : (1:ℕ) ≤ births lam (List.replicate (n-1) Move.L ++ [Move.M]) := by
    refine le_trans ?_ (births_le_append _ _)
    simp [births_cons]
  calc (1:ℕ) ≤ births lam (List.replicate (n-1) Move.L ++ [Move.M]) := h1
    _ ≤ N lam (List.replicate (n-1) Move.L ++ [Move.M]).length := births_le_N h _
    _ = N lam n := by rw [hlen]

/-- The run `MRM` produces two knots when `lam < 2`. -/
lemma births_MRM (h : 1 < lam) (h2 : lam < 2) :
    births lam [Move.M, Move.R, Move.M] = 2 := by
  have h0 : 0 < lam := lt_trans zero_lt_one h
  have hr : lam * r lam = 1 := lam_mul_r h
  have hrhalf : (1:ℝ)/2 < r lam := by nlinarith
  have hsum : 2 < lam + r lam := by nlinarith [sq_nonneg (lam - 1)]
  have hR : survives lam Move.R (1/2) := by simpa using hrhalf
  have hactR : act lam Move.R (1/2) = lam / 2 := by rw [act_R]; ring
  have hM : survives lam Move.M (lam / 2) := by
    simp only [survives_M]
    exact Or.inr (by linarith)
  have hs : survivesWord lam (1/2) [Move.R, Move.M] := by
    refine ⟨hR, ?_⟩
    rw [hactR]
    exact ⟨hM, trivial⟩
  simp only [births_cons, births_nil, survivesWord_nil, hs, and_true, if_pos,
    reduceCtorEq, false_and, if_false, add_zero, zero_add]

/-- **Proposition 4.1.** `N lam n = 1` for every `n ≥ 1` if and only if
`2 ≤ lam`, that is, if and only if the deleted interval occupies at least half
the strip. -/
theorem N_eq_one_iff (h : 1 < lam) :
    (∀ n : ℕ, 1 ≤ n → N lam n = 1) ↔ 2 ≤ lam := by
  constructor
  · intro hN
    by_contra hlt
    push_neg at hlt
    have h2 : (2:ℕ) ≤ N lam 3 := by
      have := births_le_N h [Move.M, Move.R, Move.M]
      rw [births_MRM h hlt] at this
      simpa using this
    rw [hN 3 (by norm_num)] at h2
    omega
  · intro h2 n hn
    refine le_antisymm ?_ (one_le_N h hn)
    apply Finset.sup_le
    intro v _
    rw [card_run h]
    exact births_le_one h h2 _

end KnotGame
