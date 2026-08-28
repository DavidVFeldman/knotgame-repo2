import RequestProject.Golden

/-!
# The tribonacci parameter (round 3, Target T8)

The tribonacci number `lam` is the real root of `x³ = x² + x + 1`
(`lam ≈ 1.8392867552`).  It is a Pisot number, so Theorem 3.1 already gives that
the orbit of `1/2` is finite; this file computes that orbit exactly and runs the
round-1 golden-ratio argument at the new parameter:

* the orbit of `1/2` has **7** points, listed in increasing order in `p`;
* the transition tables `absSurv`, `absAct` describe the game on those points;
* exactly **20** configurations are reachable (`reach`), all of card `≤ 3`;
* the maximum is attained: `sup N = 3`, by the run `MLRMRLM`;
* the first attainment depths are `d 1 = 1`, `d 2 = 3`, `d 3 = 7`.

As at the golden ratio, two of the orbit points are boundary points of the
interval deleted by `M`: `p 2 = r/2` and `p 4 = 1 - r/2`.  Since survival is
strict, they are destroyed by `M`, and that is what keeps the count bounded.

Points are written over `ℤ[lam]` with denominator `2`, exactly as in
`PlasticOrbit`; here the orbit is small enough that the whole verification is a
`decide` on `Finset (Fin 7)`.
-/

namespace KnotGame
namespace Tribonacci

set_option maxRecDepth 100000

open Polynomial

/-! ### The tribonacci number -/

private lemma exists_root : ∃ x : ℝ, x ∈ Set.Ioo (1:ℝ) 2 ∧ x ^ 3 - x ^ 2 - x - 1 = 0 := by
  have hcont : ContinuousOn (fun x : ℝ => x ^ 3 - x ^ 2 - x - 1) (Set.Icc 1 2) :=
    (Continuous.continuousOn (by continuity))
  have h0 : (0:ℝ) ∈ Set.Ioo ((1:ℝ) ^ 3 - 1 ^ 2 - 1 - 1) ((2:ℝ) ^ 3 - 2 ^ 2 - 2 - 1) := by
    constructor <;> norm_num
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Ioo (by norm_num : (1:ℝ) ≤ 2) hcont h0
  exact ⟨x, hx, hfx⟩

/-- The **tribonacci number**: the real root of `x³ = x² + x + 1`. -/
noncomputable def lam : ℝ := Classical.choose exists_root

lemma lam_mem : lam ∈ Set.Ioo (1:ℝ) 2 := (Classical.choose_spec exists_root).1

lemma lam_cubic : lam ^ 3 - lam ^ 2 - lam - 1 = 0 := (Classical.choose_spec exists_root).2

lemma one_lt_lam : 1 < lam := lam_mem.1

lemma lam_lt_two : lam < 2 := lam_mem.2

lemma lam_cube : lam ^ 3 = lam ^ 2 + lam + 1 := by linarith [lam_cubic]

lemma lam_gt : (1.8392 : ℝ) < lam := by
  nlinarith [lam_cubic, lam_mem.1, lam_mem.2, sq_nonneg (lam - 1.8392), sq_nonneg (lam + 1.8392)]

lemma lam_lt : lam < 1.8393 := by
  nlinarith [lam_cubic, lam_mem.1, lam_mem.2, sq_nonneg (lam - 1.8393), sq_nonneg (lam + 1.8393)]

lemma r_tri : r lam = lam ^ 2 - lam - 1 := by
  have h : lam * (lam ^ 2 - lam - 1) = 1 := by linear_combination lam_cubic
  simpa [r] using inv_eq_of_mul_eq_one_right h

lemma g_tri : g lam = 2 + lam - lam ^ 2 := by
  rw [g, r_tri]; ring

/-! ### The seven orbit points -/

/-- The seven points of the orbit of `1/2`, in increasing order.  In
coordinates over `ℤ[lam]` with denominator `2`:
`(2,-1,0), (0,2,-1), (-1,-1,1), (1,0,0), (3,1,-1), (2,-2,1), (0,1,0)`. -/
noncomputable def p : Fin 7 → ℝ :=
  ![(2 - lam)/2, (2*lam - lam^2)/2, (lam^2 - lam - 1)/2, 1/2,
    (3 + lam - lam^2)/2, (2 - 2*lam + lam^2)/2, lam/2]

@[simp] lemma p0 : p 0 = (2 - lam)/2 := rfl
@[simp] lemma p1 : p 1 = (2*lam - lam^2)/2 := rfl
@[simp] lemma p2 : p 2 = (lam^2 - lam - 1)/2 := rfl
@[simp] lemma p3 : p 3 = 1/2 := rfl
@[simp] lemma p4 : p 4 = (3 + lam - lam^2)/2 := rfl
@[simp] lemma p5 : p 5 = (2 - 2*lam + lam^2)/2 := rfl
@[simp] lemma p6 : p 6 = lam/2 := rfl

/-- The boundary equality `p 2 = r/2`. -/
lemma p2_eq : p 2 = r lam / 2 := by rw [p2, r_tri]

/-- The boundary equality `p 4 = 1 - r/2`. -/
lemma p4_eq : p 4 = 1 - r lam / 2 := by rw [p4, r_tri]; ring

lemma p_injective : Function.Injective p := by
  have h1 := lam_gt
  have h2 := lam_lt
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [p] at hij ⊢ <;> nlinarith

/-- Which of the seven points survive which move. -/
def absSurv : Move → Fin 7 → Bool
  | .L => ![false, false, false, true, true, true, true]
  | .M => ![true, true, false, false, false, true, true]
  | .R => ![true, true, true, true, false, false, false]

/-- Where the surviving points go.  The value at a non-surviving point is
irrelevant. -/
def absAct : Move → Fin 7 → Fin 7
  | .L => ![0, 0, 0, 0, 3, 4, 5]
  | .M => ![1, 2, 0, 0, 0, 4, 5]
  | .R => ![1, 2, 3, 6, 0, 0, 0]

lemma survives_p (m : Move) (i : Fin 7) : survives lam m (p i) ↔ absSurv m i := by
  have h1 := lam_gt
  have h2 := lam_lt
  fin_cases m <;> fin_cases i <;> simp [absSurv, p, r_tri, g_tri] <;>
    first
      | nlinarith
      | (left; nlinarith)
      | (right; nlinarith)
      | (constructor <;> nlinarith)

lemma act_p (m : Move) (i : Fin 7) (hi : absSurv m i) :
    act lam m (p i) = p (absAct m i) := by
  have h1 := lam_gt
  have h2 := lam_lt
  have hc := lam_cube
  fin_cases m <;> fin_cases i <;>
    simp [absSurv, absAct, p, act_L, act_R] at hi ⊢ <;>
    first
      | ring1
      | linear_combination hc/2
      | linear_combination -hc/2
      | (rw [act_M_of_lt lam _ (by rw [r_tri]; nlinarith)];
         first | ring1 | linear_combination hc/2 | linear_combination -hc/2)
      | (rw [act_M_of_gt lam _ (by rw [r_tri]; push_neg; nlinarith)];
         first | ring1 | linear_combination hc/2)

/-! ### The automaton on subsets of the orbit -/

/-- The automaton on subsets of the orbit. -/
def absStep (m : Move) (T : Finset (Fin 7)) : Finset (Fin 7) :=
  (T.filter (fun i => absSurv m i)).image (absAct m) ∪ (if m = Move.M then {3} else ∅)

/-- One move of the game is the image under `p` of one move of the automaton. -/
lemma step_image (m : Move) (T : Finset (Fin 7)) :
    step lam m (T.image p) = (absStep m T).image p := by
  ext y
  simp only [mem_step, absStep, Finset.mem_image, Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro (⟨x, ⟨i, hi, rfl⟩, hs, rfl⟩ | ⟨hm, rfl⟩)
    · refine ⟨absAct m i, Or.inl ⟨i, ⟨hi, (survives_p m i).mp hs⟩, rfl⟩, ?_⟩
      exact (act_p m i ((survives_p m i).mp hs)).symm
    · refine ⟨3, Or.inr ?_, p3⟩
      simp [hm]
  · rintro ⟨j, (⟨i, ⟨hi, hs⟩, rfl⟩ | hj), rfl⟩
    · exact Or.inl ⟨p i, ⟨i, hi, rfl⟩, (survives_p m i).mpr hs, (act_p m i hs)⟩
    · by_cases hm : m = Move.M
      · rw [if_pos hm, Finset.mem_singleton] at hj
        subst hj
        exact Or.inr ⟨hm, p3⟩
      · rw [if_neg hm] at hj
        exact absurd hj (Finset.notMem_empty _)

noncomputable def absRunFrom (T : Finset (Fin 7)) (w : List Move) : Finset (Fin 7) :=
  w.foldl (fun T m => absStep m T) T

noncomputable def absRun (w : List Move) : Finset (Fin 7) := absRunFrom ∅ w

lemma runFrom_eq (T : Finset (Fin 7)) (w : List Move) :
    runFrom lam (T.image p) w = (absRunFrom T w).image p := by
  induction w generalizing T with
  | nil => rfl
  | cons m w ih =>
      rw [runFrom_cons, step_image, ih]
      rfl

lemma run_eq (w : List Move) : run lam w = (absRun w).image p := by
  have : ((∅ : Finset (Fin 7)).image p) = ∅ := by simp
  rw [run, ← this, runFrom_eq, absRun]

lemma card_run_eq (w : List Move) : (run lam w).card = (absRun w).card := by
  rw [run_eq, Finset.card_image_of_injective _ p_injective]

/-! ### The twenty reachable configurations -/

/-- The twenty reachable configurations. -/
def reach : Finset (Finset (Fin 7)) :=
  {∅, {0}, {1}, {2}, {3}, {4}, {5}, {6},
   {0,3}, {0,4}, {0,5}, {1,3}, {1,6}, {2,3}, {2,6}, {3,4}, {3,5}, {3,6},
   {1,3,4}, {2,3,5}}

theorem reach_card_eq : reach.card = 20 := by decide

lemma reach_closed : ∀ T ∈ reach, ∀ m : Move, absStep m T ∈ reach := by decide

lemma reach_card : ∀ T ∈ reach, T.card ≤ 3 := by decide

lemma empty_mem_reach : (∅ : Finset (Fin 7)) ∈ reach := by decide

lemma absRunFrom_mem_reach (w : List Move) : ∀ T ∈ reach, absRunFrom T w ∈ reach := by
  induction w with
  | nil => intro T hT; exact hT
  | cons m w ih => intro T hT; exact ih _ (reach_closed T hT m)

lemma absRun_mem_reach (w : List Move) : absRun w ∈ reach :=
  absRunFrom_mem_reach w ∅ empty_mem_reach

/-- Every configuration reachable at the tribonacci parameter has at most three
knots. -/
theorem card_run_le_three (w : List Move) : (run lam w).card ≤ 3 := by
  rw [card_run_eq]
  exact reach_card _ (absRun_mem_reach w)

theorem N_le_three (n : ℕ) : N lam n ≤ 3 := by
  apply Finset.sup_le
  intro v _
  exact card_run_le_three _

/-! ### Lower bounds from explicit runs -/

lemma le_N_of_word {n : ℕ} (v : Fin n → Move) : (absRun (List.ofFn v)).card ≤ N lam n := by
  have h : (run lam (List.ofFn v)).card = (absRun (List.ofFn v)).card := card_run_eq _
  rw [← h]
  exact Finset.le_sup (f := fun u : Fin n → Move => (run lam (List.ofFn u)).card)
    (Finset.mem_univ v)

/-- The run `M` gives one knot. -/
theorem one_le_N_one : 1 ≤ N lam 1 := by
  have h := le_N_of_word (n := 1) ![Move.M]
  have hc : (absRun (List.ofFn ![Move.M])).card = 1 := by decide
  omega

/-- The run `MLM` gives two knots. -/
theorem two_le_N_three : 2 ≤ N lam 3 := by
  have h := le_N_of_word (n := 3) ![Move.M, Move.L, Move.M]
  have hc : (absRun (List.ofFn ![Move.M, Move.L, Move.M])).card = 2 := by decide
  omega

/-- The run `MLRMRLM` gives three knots. -/
theorem three_le_N_seven : 3 ≤ N lam 7 := by
  have h := le_N_of_word (n := 7)
    ![Move.M, Move.L, Move.R, Move.M, Move.R, Move.L, Move.M]
  have hc : (absRun (List.ofFn
      ![Move.M, Move.L, Move.R, Move.M, Move.R, Move.L, Move.M])).card = 3 := by decide
  omega

/-- **T8 (tribonacci, exact maximum).**  The largest number of simultaneous
knots at the tribonacci parameter is `3`. -/
theorem sup_N_lam : IsGreatest (Set.range (N lam)) 3 := by
  constructor
  · exact ⟨7, le_antisymm (N_le_three 7) three_le_N_seven⟩
  · rintro y ⟨n, rfl⟩
    exact N_le_three n

/-! ### The layered reachability and the depths `d k` -/

/-- The configurations reachable in exactly `n` moves. -/
def layer : ℕ → Finset (Finset (Fin 7))
  | 0 => {∅}
  | n + 1 => (layer n).biUnion
      (fun T => {absStep Move.L T, absStep Move.M T, absStep Move.R T})

lemma absRunFrom_mem_layer (w : List Move) :
    ∀ (n : ℕ) (T : Finset (Fin 7)), T ∈ layer n → absRunFrom T w ∈ layer (n + w.length) := by
  induction w with
  | nil => intro n T hT; simpa using hT
  | cons m w ih =>
      intro n T hT
      have hstep : absStep m T ∈ layer (n + 1) := by
        refine Finset.mem_biUnion.mpr ⟨T, hT, ?_⟩
        cases m <;> simp
      have := ih (n + 1) _ hstep
      simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

lemma absRun_mem_layer (w : List Move) : absRun w ∈ layer w.length := by
  have := absRunFrom_mem_layer w 0 ∅ (by simp [layer])
  simpa [absRun] using this

lemma N_le_of_layer {n k : ℕ} (h : ∀ T ∈ layer n, T.card ≤ k) : N lam n ≤ k := by
  apply Finset.sup_le
  intro v _
  rw [card_run_eq]
  refine h _ ?_
  have := absRun_mem_layer (List.ofFn v)
  simpa using this

theorem N_one_le_one : N lam 1 ≤ 1 := N_le_of_layer (by decide)

theorem N_two_le_one : N lam 2 ≤ 1 := N_le_of_layer (by decide)

theorem N_six_le_two : N lam 6 ≤ 2 := N_le_of_layer (by decide)

lemma N_mono' {a b : ℕ} (hab : a ≤ b) : N lam a ≤ N lam b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact le_trans ih (N_mono one_lt_lam n)

theorem N_zero_le_zero : N lam 0 ≤ 0 := N_le_of_layer (by decide)

/-- `d 1 = 1`: one knot first appears after one move. -/
theorem d_one : d lam 1 = 1 := by
  have hmem : (1:ℕ) ∈ {n | 1 ≤ N lam n} := one_le_N_one
  refine le_antisymm (Nat.sInf_le hmem) ?_
  refine le_csInf ⟨1, hmem⟩ ?_
  intro n hn
  by_contra hlt
  push_neg at hlt
  interval_cases n
  · have := N_zero_le_zero
    simp only [Set.mem_setOf_eq] at hn
    omega

/-- `d 2 = 3`: two simultaneous knots first appear after three moves. -/
theorem d_two : d lam 2 = 3 := by
  have hmem : (3:ℕ) ∈ {n | 2 ≤ N lam n} := two_le_N_three
  refine le_antisymm (Nat.sInf_le hmem) ?_
  refine le_csInf ⟨3, hmem⟩ ?_
  intro n hn
  by_contra hlt
  push_neg at hlt
  interval_cases n
  · simp only [Set.mem_setOf_eq] at hn
    have h0 : N lam 0 ≤ 0 := N_le_of_layer (by decide)
    omega
  · have := N_one_le_one; simp only [Set.mem_setOf_eq] at hn; omega
  · have := N_two_le_one; simp only [Set.mem_setOf_eq] at hn; omega

/-- `d 3 = 7`: three simultaneous knots first appear after seven moves. -/
theorem d_three : d lam 3 = 7 := by
  have hmem : (7:ℕ) ∈ {n | 3 ≤ N lam n} := three_le_N_seven
  refine le_antisymm (Nat.sInf_le hmem) ?_
  refine le_csInf ⟨7, hmem⟩ ?_
  intro n hn
  by_contra hlt
  push_neg at hlt
  have hmono : N lam n ≤ N lam 6 := N_mono' (by omega)
  have := N_six_le_two
  simp only [Set.mem_setOf_eq] at hn
  omega

end Tribonacci
end KnotGame
