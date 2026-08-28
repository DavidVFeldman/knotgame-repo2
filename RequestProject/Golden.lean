import RequestProject.Threshold

/-!
# Theorem 3.3: the golden ratio (Work Order 5)

For `lam = φ = (1+√5)/2` the orbit of `1/2` consists of the five points

  `p₀ = 1 - φ/2`, `p₁ = (φ-1)/2`, `p₂ = 1/2`, `p₃ = (3-φ)/2`, `p₄ = φ/2`,

and `p₁ = r/2`, `p₃ = 1 - r/2` are exactly the endpoints of the interval deleted
by `M` — the boundary equalities which, because survival is strict, are the
reason the count does not grow.

The bound `sup N = 2` is obtained from an inductive invariant: a twelve element
set of configurations containing `∅`, closed under all three moves, each member
of which has at most two elements.
-/

namespace KnotGame
namespace Golden

open Real

/-- The golden ratio. -/
noncomputable abbrev phi : ℝ := Real.goldenRatio

lemma phi_sq : phi ^ 2 = phi + 1 := Real.goldenRatio_sq

lemma one_lt_phi : 1 < phi := Real.one_lt_goldenRatio

lemma phi_lt_two : phi < 2 := by nlinarith [phi_sq, one_lt_phi]

lemma phi_gt : (1.6:ℝ) < phi := by nlinarith [phi_sq, one_lt_phi]

lemma phi_lt : phi < 1.62 := by nlinarith [phi_sq, one_lt_phi]

lemma r_phi : r phi = phi - 1 := by
  have : phi * (phi - 1) = 1 := by nlinarith [phi_sq]
  simpa [r] using inv_eq_of_mul_eq_one_right this

lemma g_phi : g phi = 2 - phi := by
  rw [g, r_phi]; ring

/-- The five orbit points. -/
noncomputable def p : Fin 5 → ℝ :=
  ![1 - phi/2, (phi-1)/2, 1/2, (3-phi)/2, phi/2]

@[simp] lemma p0 : p 0 = 1 - phi/2 := rfl
@[simp] lemma p1 : p 1 = (phi-1)/2 := rfl
@[simp] lemma p2 : p 2 = 1/2 := rfl
@[simp] lemma p3 : p 3 = (3-phi)/2 := rfl
@[simp] lemma p4 : p 4 = phi/2 := rfl

/-- The boundary equality `p₁ = r/2`. -/
lemma p1_eq : p 1 = r phi / 2 := by rw [p1, r_phi]

/-- The boundary equality `p₃ = 1 - r/2`. -/
lemma p3_eq : p 3 = 1 - r phi / 2 := by rw [p3, r_phi]; ring

lemma p_injective : Function.Injective p := by
  have h1 := phi_gt
  have h2 := phi_lt
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [p] at hij ⊢ <;> linarith

/-- Which of the five points survive which move (Appendix B). -/
def absSurv : Move → Fin 5 → Bool
  | .L => ![false, false, true, true, true]
  | .M => ![true, false, false, false, true]
  | .R => ![true, true, true, false, false]

/-- Where the surviving points go (Appendix B).  The value at a non-surviving
point is irrelevant. -/
def absAct : Move → Fin 5 → Fin 5
  | .L => ![0, 0, 0, 2, 3]
  | .M => ![1, 1, 1, 1, 3]
  | .R => ![1, 2, 4, 4, 4]

lemma survives_p (m : Move) (i : Fin 5) : survives phi m (p i) ↔ absSurv m i := by
  have h1 := phi_gt
  have h2 := phi_lt
  fin_cases m <;> fin_cases i <;> simp [absSurv, p, r_phi, g_phi] <;>
    first
      | linarith
      | (left; linarith)
      | (right; linarith)
      | (constructor <;> linarith)

lemma act_p (m : Move) (i : Fin 5) (hi : absSurv m i) :
    act phi m (p i) = p (absAct m i) := by
  have h1 := phi_gt
  have h2 := phi_lt
  have hsq := phi_sq
  fin_cases m <;> fin_cases i <;> simp [absSurv, absAct, p, act_L, act_R] at hi ⊢ <;>
    first
      | nlinarith
      | (rw [act_M_of_lt phi _ (by simp [r_phi]; linarith)]; nlinarith)
      | (rw [act_M_of_gt phi _ (by simp [r_phi]; linarith)]; nlinarith)

/-- The automaton on subsets of the orbit. -/
def absStep (m : Move) (T : Finset (Fin 5)) : Finset (Fin 5) :=
  (T.filter (fun i => absSurv m i)).image (absAct m) ∪ (if m = Move.M then {2} else ∅)

/-- One move of the game is the image under `p` of one move of the automaton. -/
lemma step_image (m : Move) (T : Finset (Fin 5)) :
    step phi m (T.image p) = (absStep m T).image p := by
  ext y
  simp only [mem_step, absStep, Finset.mem_image, Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro (⟨x, ⟨i, hi, rfl⟩, hs, rfl⟩ | ⟨hm, rfl⟩)
    · refine ⟨absAct m i, Or.inl ⟨i, ⟨hi, (survives_p m i).mp hs⟩, rfl⟩, ?_⟩
      exact (act_p m i ((survives_p m i).mp hs)).symm
    · refine ⟨2, Or.inr ?_, p2⟩
      simp [hm]
  · rintro ⟨j, (⟨i, ⟨hi, hs⟩, rfl⟩ | hj), rfl⟩
    · refine Or.inl ⟨p i, ⟨i, hi, rfl⟩, (survives_p m i).mpr hs, (act_p m i hs)⟩
    · by_cases hm : m = Move.M
      · rw [if_pos hm, Finset.mem_singleton] at hj
        subst hj
        exact Or.inr ⟨hm, p2⟩
      · rw [if_neg hm] at hj
        exact absurd hj (Finset.notMem_empty _)

noncomputable def absRunFrom (T : Finset (Fin 5)) (w : List Move) : Finset (Fin 5) :=
  w.foldl (fun T m => absStep m T) T

noncomputable def absRun (w : List Move) : Finset (Fin 5) := absRunFrom ∅ w

lemma runFrom_eq (T : Finset (Fin 5)) (w : List Move) :
    runFrom phi (T.image p) w = (absRunFrom T w).image p := by
  induction w generalizing T with
  | nil => rfl
  | cons m w ih =>
      rw [runFrom_cons, step_image, ih]
      rfl

lemma run_eq (w : List Move) : run phi w = (absRun w).image p := by
  have : ((∅ : Finset (Fin 5)).image p) = ∅ := by simp
  rw [run, ← this, runFrom_eq, absRun]

/-- The twelve reachable configurations. -/
def reach : Finset (Finset (Fin 5)) :=
  {∅, {0}, {1}, {2}, {3}, {4}, {2,3}, {1,2}, {0,2}, {2,4}, {1,4}, {0,3}}

lemma reach_closed : ∀ T ∈ reach, ∀ m : Move, absStep m T ∈ reach := by
  decide

lemma reach_card : ∀ T ∈ reach, T.card ≤ 2 := by
  decide

lemma empty_mem_reach : (∅ : Finset (Fin 5)) ∈ reach := by decide

lemma absRunFrom_mem_reach (w : List Move) :
    ∀ T ∈ reach, absRunFrom T w ∈ reach := by
  induction w with
  | nil => intro T hT; exact hT
  | cons m w ih =>
      intro T hT
      exact ih _ (reach_closed T hT m)

lemma absRun_mem_reach (w : List Move) : absRun w ∈ reach :=
  absRunFrom_mem_reach w ∅ empty_mem_reach

theorem card_run_le_two (w : List Move) : (run phi w).card ≤ 2 := by
  rw [run_eq]
  exact le_trans (Finset.card_image_le) (reach_card _ (absRun_mem_reach w))

/-- Every configuration reachable at the golden ratio has at most two knots. -/
theorem N_phi_le_two (n : ℕ) : N phi n ≤ 2 := by
  apply Finset.sup_le
  intro v _
  exact card_run_le_two _

theorem N_phi_three : N phi 3 = 2 := by
  refine le_antisymm (N_phi_le_two 3) ?_
  have := births_le_N one_lt_phi [Move.M, Move.R, Move.M]
  rw [births_MRM one_lt_phi phi_lt_two] at this
  simpa using this

/-- **Theorem 3.3.** For the golden ratio the maximum knot count is `2`,
attained by the run `MRM`. -/
theorem sup_N_phi : IsGreatest (Set.range (N phi)) 2 := by
  constructor
  · exact ⟨3, N_phi_three⟩
  · rintro y ⟨n, rfl⟩
    exact N_phi_le_two n

end Golden
end KnotGame
