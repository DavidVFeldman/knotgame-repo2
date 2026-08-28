import RequestProject.Golden

/-!
# The supergolden parameter (round 3, Target T8)

The supergolden ratio `lam` is the real root of `x³ = x² + 1`
(`lam ≈ 1.4655712319`).  It is a Pisot number, so Theorem 3.1 already gives
that the orbit of `1/2` is finite; this file computes that orbit exactly and
runs the round-1 golden-ratio argument at the new parameter:

* the orbit of `1/2` has **43** points, listed in increasing order in `p`;
* the transition tables `absSurv`, `absAct` describe the game on those points;
* exactly **412** configurations are reachable, all of card `≤ 4`;
* the maximum is attained: `sup N = 4`;
* the first attainment depths are `d 1 = 1`, `d 2 = 3`, `d 3 = 5`, `d 4 = 11`.

Points are written over `ℤ[lam]` with denominator `2`, exactly as in
`Tribonacci` and `PlasticOrbit`.  The orbit here is far larger, so the
configuration data are handled differently: the 412 reachable
configurations are stored **with their exact first-attainment depth** in
`reachD`, and a single boolean check `checkOK`, discharged by kernel reduction,
verifies at once that

* the list is closed under the three moves (the depth of a successor is at most
  one more than the depth of its predecessor, and in particular is finite),
* every configuration has at most four knots, and
* a configuration with `k` knots has depth at least `d k` (`1, 3, 5, 11`).

Everything about the game then follows from that one check.  Storing the
depths, rather than iterating a layer construction inside Lean, is what keeps
the kernel computation to a single pass over the list.
-/

namespace KnotGame
namespace Supergolden

set_option maxRecDepth 10000000
set_option maxHeartbeats 4000000

open Finset

/-! ### The supergolden number -/

private lemma exists_root : ∃ x : ℝ, x ∈ Set.Ioo (1:ℝ) 2 ∧ x ^ 3 - x ^ 2 - 1 = 0 := by
  have hcont : ContinuousOn (fun x : ℝ => x ^ 3 - x ^ 2 - 1) (Set.Icc 1 2) :=
    (Continuous.continuousOn (by continuity))
  have h0 : (0:ℝ) ∈ Set.Ioo ((1:ℝ) ^ 3 - 1 ^ 2 - 1) ((2:ℝ) ^ 3 - 2 ^ 2 - 1) := by
    constructor <;> norm_num
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Ioo (by norm_num : (1:ℝ) ≤ 2) hcont h0
  exact ⟨x, hx, hfx⟩

/-- The **supergolden ratio**: the real root of `x³ = x² + 1`. -/
noncomputable def lam : ℝ := Classical.choose exists_root

lemma lam_mem : lam ∈ Set.Ioo (1:ℝ) 2 := (Classical.choose_spec exists_root).1

lemma lam_cubic : lam ^ 3 - lam ^ 2 - 1 = 0 := (Classical.choose_spec exists_root).2

lemma one_lt_lam : 1 < lam := lam_mem.1

lemma lam_lt_two : lam < 2 := lam_mem.2

lemma lam_cube : lam ^ 3 = lam ^ 2 + 1 := by linarith [lam_cubic]

lemma lam_gt : (1.4655712 : ℝ) < lam := by
  nlinarith [lam_cubic, lam_mem.1, lam_mem.2, sq_nonneg (lam - 1.4655712),
    sq_nonneg (lam + 1.4655712)]

lemma lam_lt : lam < 1.4655713 := by
  nlinarith [lam_cubic, lam_mem.1, lam_mem.2, sq_nonneg (lam - 1.4655713),
    sq_nonneg (lam + 1.4655713)]

lemma lam_sq_gt : (2.1478989 : ℝ) < lam ^ 2 := by nlinarith [lam_gt, lam_mem.1]

lemma lam_sq_lt : lam ^ 2 < 2.1478994 := by nlinarith [lam_lt, lam_mem.1]

lemma r_sg : r lam = lam ^ 2 - lam := by
  have h : lam * (lam ^ 2 - lam) = 1 := by linear_combination lam_cubic
  simpa [r] using inv_eq_of_mul_eq_one_right h

lemma g_sg : g lam = 1 + lam - lam ^ 2 := by
  rw [g, r_sg]; ring

/-! ### The 43 orbit points -/

/-- The 43 points of the orbit of `1/2`, in increasing order, as elements
`(A + B·lam + C·lam²)/2` of `ℤ[lam]` with denominator `2`. -/
noncomputable def p : Fin 43 → ℝ :=
  ![(3 - 2*lam)/2,
    (3*lam - 2*lam^2)/2,
    (-2 + lam^2)/2,
    (3 + lam - 2*lam^2)/2,
    (1 - 2*lam + lam^2)/2,
    (-2 + 3*lam - lam^2)/2,
    (4 - 4*lam + lam^2)/2,
    (1 + lam - lam^2)/2,
    (-1 - 2*lam + 2*lam^2)/2,
    (4 - lam - lam^2)/2,
    (1 + 4*lam - 3*lam^2)/2,
    (-1 + lam)/2,
    (2 - lam)/2,
    (-1 + 4*lam - 2*lam^2)/2,
    (-3 + lam + lam^2)/2,
    (-lam + lam^2)/2,
    (3 - 3*lam + lam^2)/2,
    (2*lam - lam^2)/2,
    (-2 - lam + 2*lam^2)/2,
    (3 - lam^2)/2,
    (1 - 3*lam + 2*lam^2)/2,
    (1)/2,
    (1 + 3*lam - 2*lam^2)/2,
    (-1 + lam^2)/2,
    (4 + lam - 2*lam^2)/2,
    (2 - 2*lam + lam^2)/2,
    (-1 + 3*lam - lam^2)/2,
    (2 + lam - lam^2)/2,
    (5 - lam - lam^2)/2,
    (3 - 4*lam + 2*lam^2)/2,
    (lam)/2,
    (3 - lam)/2,
    (1 - 4*lam + 3*lam^2)/2,
    (-2 + lam + lam^2)/2,
    (3 + 2*lam - 2*lam^2)/2,
    (1 - lam + lam^2)/2,
    (-2 + 4*lam - lam^2)/2,
    (4 - 3*lam + lam^2)/2,
    (1 + 2*lam - lam^2)/2,
    (-1 - lam + 2*lam^2)/2,
    (4 - lam^2)/2,
    (2 - 3*lam + 2*lam^2)/2,
    (-1 + 2*lam)/2]

lemma p_strictMono : StrictMono p := by
  have h1 := lam_gt
  have h2 := lam_lt
  have h3 := lam_sq_gt
  have h4 := lam_sq_lt
  refine Fin.strictMono_iff_lt_succ.mpr ?_
  intro i
  fin_cases i <;> simp [p] <;> linarith

lemma p_injective : Function.Injective p := p_strictMono.injective

/-- Which of the orbit points survive which move. -/
def absSurv : Move → Fin 43 → Bool
  | .L => ![false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true]
  | .M => ![true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true]
  | .R => ![true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

/-- Where the surviving points go.  The value at a non-surviving point is
irrelevant. -/
def absAct : Move → Fin 43 → Fin 43
  | .L => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 4, 6, 7, 9, 12, 15, 16, 17, 19, 20, 21, 22, 24, 25, 27, 28, 29, 30, 31, 32, 34, 35, 37, 38, 40, 41]
  | .M => ![1, 2, 4, 5, 7, 8, 10, 11, 12, 13, 14, 15, 17, 18, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22, 24, 25, 27, 28, 29, 30, 31, 32, 34, 35, 37, 38, 40, 41]
  | .R => ![1, 2, 4, 5, 7, 8, 10, 11, 12, 13, 14, 15, 17, 18, 20, 21, 22, 23, 25, 26, 27, 30, 33, 35, 36, 38, 39, 42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

lemma survives_p (m : Move) (i : Fin 43) : survives lam m (p i) ↔ absSurv m i := by
  have h1 := lam_gt
  have h2 := lam_lt
  have h3 := lam_sq_gt
  have h4 := lam_sq_lt
  fin_cases m <;> fin_cases i <;> simp [absSurv, p, r_sg, g_sg] <;>
    first
      | linarith
      | (left; linarith)
      | (right; linarith)
      | (constructor <;> linarith)

lemma act_p (m : Move) (i : Fin 43) (hi : absSurv m i) :
    act lam m (p i) = p (absAct m i) := by
  have h1 := lam_gt
  have h2 := lam_lt
  have h3 := lam_sq_gt
  have h4 := lam_sq_lt
  have hc := lam_cube
  fin_cases m <;> fin_cases i <;>
    simp [absSurv, absAct, p, act_L, act_R] at hi ⊢ <;>
    first
      | ring1
      | linear_combination hc/2
      | linear_combination -hc/2
      | linear_combination hc
      | linear_combination -hc
      | linear_combination 3*hc/2
      | linear_combination -3*hc/2
      | linear_combination 2*hc
      | linear_combination -2*hc
      | (rw [act_M_of_lt lam _ (by rw [r_sg]; linarith)];
         first
           | ring1
           | linear_combination hc/2
           | linear_combination -hc/2
           | linear_combination hc
           | linear_combination -hc
           | linear_combination 3*hc/2
           | linear_combination -3*hc/2)
      | (rw [act_M_of_gt lam _ (by rw [r_sg]; push_neg; linarith)];
         first
           | ring1
           | linear_combination hc/2
           | linear_combination -hc/2
           | linear_combination hc
           | linear_combination -hc
           | linear_combination 3*hc/2)

/-! ### The automaton on subsets of the orbit -/

/-- The automaton on subsets of the orbit. -/
def absStep (m : Move) (T : Finset (Fin 43)) : Finset (Fin 43) :=
  (T.filter (fun i => absSurv m i)).image (absAct m) ∪ (if m = Move.M then {21} else ∅)

/-- One move of the game is the image under `p` of one move of the automaton. -/
lemma step_image (m : Move) (T : Finset (Fin 43)) :
    step lam m (T.image p) = (absStep m T).image p := by
  ext y
  simp only [mem_step, absStep, Finset.mem_image, Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro (⟨x, ⟨i, hi, rfl⟩, hs, rfl⟩ | ⟨hm, rfl⟩)
    · refine ⟨absAct m i, Or.inl ⟨i, ⟨hi, (survives_p m i).mp hs⟩, rfl⟩, ?_⟩
      exact (act_p m i ((survives_p m i).mp hs)).symm
    · refine ⟨21, Or.inr ?_, rfl⟩
      simp [hm]
  · rintro ⟨j, (⟨i, ⟨hi, hs⟩, rfl⟩ | hj), rfl⟩
    · exact Or.inl ⟨p i, ⟨i, hi, rfl⟩, (survives_p m i).mpr hs, (act_p m i hs)⟩
    · by_cases hm : m = Move.M
      · rw [if_pos hm, Finset.mem_singleton] at hj
        subst hj
        exact Or.inr ⟨hm, rfl⟩
      · rw [if_neg hm] at hj
        exact absurd hj (Finset.notMem_empty _)

noncomputable def absRunFrom (T : Finset (Fin 43)) (w : List Move) : Finset (Fin 43) :=
  w.foldl (fun T m => absStep m T) T

noncomputable def absRun (w : List Move) : Finset (Fin 43) := absRunFrom ∅ w

lemma runFrom_eq (T : Finset (Fin 43)) (w : List Move) :
    runFrom lam (T.image p) w = (absRunFrom T w).image p := by
  induction w generalizing T with
  | nil => rfl
  | cons m w ih =>
      rw [runFrom_cons, step_image, ih]
      rfl

lemma run_eq (w : List Move) : run lam w = (absRun w).image p := by
  have : ((∅ : Finset (Fin 43)).image p) = ∅ := by simp
  rw [run, ← this, runFrom_eq, absRun]

lemma card_run_eq (w : List Move) : (run lam w).card = (absRun w).card := by
  rw [run_eq, Finset.card_image_of_injective _ p_injective]

/-! ### The 412 reachable configurations, with their depths -/

/-- The reachable configurations, each tagged with the exact number of moves
after which it first occurs. -/
def reachD : List (Finset (Fin 43) × ℕ) :=
  [(∅, 0),
   ({21}, 1),
   ({12}, 2),
   ({30}, 2),
   ({17}, 3),
   ({17,21}, 3),
   ({25}, 3),
   ({21,25}, 3),
   ({4}, 4),
   ({4,12}, 4),
   ({19}, 4),
   ({12,19}, 4),
   ({23}, 4),
   ({23,30}, 4),
   ({38}, 4),
   ({30,38}, 4),
   ({7}, 5),
   ({16}, 5),
   ({7,17}, 5),
   ({7,21}, 5),
   ({7,17,21}, 5),
   ({16,25}, 5),
   ({26}, 5),
   ({17,26}, 5),
   ({35}, 5),
   ({21,35}, 5),
   ({25,35}, 5),
   ({21,25,35}, 5),
   ({3}, 6),
   ({11}, 6),
   ({3,19}, 6),
   ({20}, 6),
   ({4,20}, 6),
   ({11,21}, 6),
   ({22}, 6),
   ({11,23}, 6),
   ({11,30}, 6),
   ({11,23,30}, 6),
   ({31}, 6),
   ({12,31}, 6),
   ({19,31}, 6),
   ({12,19,31}, 6),
   ({21,31}, 6),
   ({22,38}, 6),
   ({39}, 6),
   ({23,39}, 6),
   ({5}, 7),
   ({9}, 7),
   ({15}, 7),
   ({5,21}, 7),
   ({15,21}, 7),
   ({15,21,25}, 7),
   ({5,26}, 7),
   ({27}, 7),
   ({7,27}, 7),
   ({12,27}, 7),
   ({21,27}, 7),
   ({17,21,27}, 7),
   ({15,30}, 7),
   ({33}, 7),
   ({15,35}, 7),
   ({37}, 7),
   ({16,37}, 7),
   ({21,37}, 7),
   ({0}, 8),
   ({8}, 8),
   ({0,12}, 8),
   ({13}, 8),
   ({0,12,19}, 8),
   ({8,21}, 8),
   ({12,21}, 8),
   ({4,12,21}, 8),
   ({13,21}, 8),
   ({0,25}, 8),
   ({29}, 8),
   ({21,29}, 8),
   ({8,30}, 8),
   ({21,30}, 8),
   ({0,31}, 8),
   ({34}, 8),
   ({3,34}, 8),
   ({12,34}, 8),
   ({21,34}, 8),
   ({21,30,38}, 8),
   ({8,39}, 8),
   ({42}, 8),
   ({11,42}, 8),
   ({17,42}, 8),
   ({30,42}, 8),
   ({23,30,42}, 8),
   ({1}, 9),
   ({1,17}, 9),
   ({18}, 9),
   ({1,21}, 9),
   ({1,17,21}, 9),
   ({18,21}, 9),
   ({24}, 9),
   ({12,24}, 9),
   ({21,24}, 9),
   ({12,25}, 9),
   ({12,21,25}, 9),
   ({1,17,26}, 9),
   ({1,21,27}, 9),
   ({12,30}, 9),
   ({17,30}, 9),
   ({7,17,30}, 9),
   ({18,30}, 9),
   ({5,21,30}, 9),
   ({17,21,30}, 9),
   ({12,25,35}, 9),
   ({12,21,37}, 9),
   ({1,38}, 9),
   ({41}, 9),
   ({4,41}, 9),
   ({21,41}, 9),
   ({15,21,41}, 9),
   ({25,41}, 9),
   ({16,25,41}, 9),
   ({21,25,41}, 9),
   ({2}, 10),
   ({6}, 10),
   ({6,12}, 10),
   ({12,17}, 10),
   ({2,21}, 10),
   ({2,23}, 10),
   ({4,25}, 10),
   ({6,25}, 10),
   ({4,12,25}, 10),
   ({8,21,25}, 10),
   ({11,21,25}, 10),
   ({17,21,25}, 10),
   ({2,30}, 10),
   ({2,23,30}, 10),
   ({25,30}, 10),
   ({17,21,31}, 10),
   ({17,21,34}, 10),
   ({2,21,35}, 10),
   ({36}, 10),
   ({17,36}, 10),
   ({30,36}, 10),
   ({17,38}, 10),
   ({17,30,38}, 10),
   ({2,23,39}, 10),
   ({40}, 10),
   ({12,40}, 10),
   ({0,12,40}, 10),
   ({19,40}, 10),
   ({3,19,40}, 10),
   ({12,19,40}, 10),
   ({21,40}, 10),
   ({7,21,40}, 10),
   ({2,30,42}, 10),
   ({10}, 11),
   ({10,17}, 11),
   ({4,12,19}, 11),
   ({4,21}, 11),
   ({10,21}, 11),
   ({10,17,21}, 11),
   ({17,23}, 11),
   ({19,25}, 11),
   ({4,21,25}, 11),
   ({4,12,27}, 11),
   ({4,30}, 11),
   ({4,12,30}, 11),
   ({4,21,31}, 11),
   ({32}, 11),
   ({4,32}, 11),
   ({21,32}, 11),
   ({25,32}, 11),
   ({21,25,32}, 11),
   ({4,35}, 11),
   ({4,25,35}, 11),
   ({4,21,37}, 11),
   ({7,38}, 11),
   ({10,38}, 11),
   ({12,38}, 11),
   ({7,17,38}, 11),
   ({21,38}, 11),
   ({5,21,38}, 11),
   ({11,21,38}, 11),
   ({17,21,38}, 11),
   ({1,17,21,38}, 11),
   ({12,30,38}, 11),
   ({15,30,38}, 11),
   ({23,30,38}, 11),
   ({4,21,25,41}, 11),
   ({14}, 12),
   ({4,16}, 12),
   ({7,19}, 12),
   ({14,21}, 12),
   ({14,23}, 12),
   ({7,21,25}, 12),
   ({7,17,21,25}, 12),
   ({7,17,26}, 12),
   ({7,21,27}, 12),
   ({28}, 12),
   ({12,28}, 12),
   ({19,28}, 12),
   ({12,19,28}, 12),
   ({21,28}, 12),
   ({7,21,28}, 12),
   ({7,30}, 12),
   ({14,30}, 12),
   ({14,23,30}, 12),
   ({7,21,31}, 12),
   ({7,21,34}, 12),
   ({12,35}, 12),
   ({4,12,35}, 12),
   ({8,21,35}, 12),
   ({11,21,35}, 12),
   ({14,21,35}, 12),
   ({15,21,35}, 12),
   ({17,21,35}, 12),
   ({23,35}, 12),
   ({0,25,35}, 12),
   ({16,25,35}, 12),
   ({17,21,25,35}, 12),
   ({26,38}, 12),
   ({7,30,38}, 12),
   ({7,17,42}, 12),
   ({20,21}, 13),
   ({7,22}, 13),
   ({12,22}, 13),
   ({21,22}, 13),
   ({11,21,22}, 13),
   ({17,21,22}, 13),
   ({20,21,25}, 13),
   ({11,26}, 13),
   ({11,21,27}, 13),
   ({20,30}, 13),
   ({11,21,30}, 13),
   ({0,12,31}, 13),
   ({4,12,31}, 13),
   ({16,31}, 13),
   ({3,19,31}, 13),
   ({4,12,19,31}, 13),
   ({1,21,31}, 13),
   ({12,21,31}, 13),
   ({15,21,31}, 13),
   ({7,17,21,31}, 13),
   ({20,21,31}, 13),
   ({20,35}, 13),
   ({11,21,25,35}, 13),
   ({11,30,38}, 13),
   ({11,23,30,38}, 13),
   ({11,23,39}, 13),
   ({11,21,41}, 13),
   ({11,30,42}, 13),
   ({9,12}, 14),
   ({12,15}, 14),
   ({4,12,15}, 14),
   ({9,12,19}, 14),
   ({9,25}, 14),
   ({3,27}, 14),
   ({0,12,27}, 14),
   ({9,12,27}, 14),
   ({2,21,27}, 14),
   ({5,21,27}, 14),
   ({1,17,21,27}, 14),
   ({7,17,21,27}, 14),
   ({27,30}, 14),
   ({9,31}, 14),
   ({11,33}, 14),
   ({17,33}, 14),
   ({30,33}, 14),
   ({15,30,33}, 14),
   ({23,30,33}, 14),
   ({15,21,25,35}, 14),
   ({15,21,37}, 14),
   ({27,30,38}, 14),
   ({15,39}, 14),
   ({15,21,40}, 14),
   ({15,21,25,41}, 14),
   ({15,30,42}, 14),
   ({13,17}, 15),
   ({13,17,21}, 15),
   ({13,17,26}, 15),
   ({13,21,27}, 15),
   ({4,29}, 15),
   ({15,21,29}, 15),
   ({25,29}, 15),
   ({0,25,29}, 15),
   ({16,25,29}, 15),
   ({21,25,29}, 15),
   ({0,12,19,31}, 15),
   ({0,12,34}, 15),
   ({0,37}, 15),
   ({0,12,38}, 15),
   ({13,38}, 15),
   ({0,12,19,40}, 15),
   ({0,25,41}, 15),
   ({5,42}, 15),
   ({1,17,42}, 15),
   ({13,17,42}, 15),
   ({4,30,42}, 15),
   ({8,30,42}, 15),
   ({2,23,30,42}, 15),
   ({11,23,30,42}, 15),
   ({18,23}, 16),
   ({0,12,24}, 16),
   ({19,24}, 16),
   ({3,19,24}, 16),
   ({12,19,24}, 16),
   ({1,21,24}, 16),
   ({7,21,24}, 16),
   ({1,17,21,30}, 16),
   ({18,23,30}, 16),
   ({1,21,34}, 16),
   ({1,17,21,35}, 16),
   ({18,21,35}, 16),
   ({18,23,39}, 16),
   ({1,21,40}, 16),
   ({2,21,41}, 16),
   ({8,21,41}, 16),
   ({18,21,41}, 16),
   ({7,21,25,41}, 16),
   ({12,21,25,41}, 16),
   ({18,30,42}, 16),
   ({6,16}, 17),
   ({6,16,25}, 17),
   ({2,21,25}, 17),
   ({2,21,30}, 17),
   ({6,12,31}, 17),
   ({2,21,31}, 17),
   ({1,17,36}, 17),
   ({26,36}, 17),
   ({5,26,36}, 17),
   ({17,26,36}, 17),
   ({2,30,36}, 17),
   ({11,30,36}, 17),
   ({6,16,37}, 17),
   ({2,21,38}, 17),
   ({6,12,40}, 17),
   ({4,21,40}, 17),
   ({11,21,40}, 17),
   ({12,21,40}, 17),
   ({17,21,40}, 17),
   ({6,25,41}, 17),
   ({10,22}, 18),
   ({4,21,27}, 18),
   ({10,17,21,27}, 18),
   ({20,32}, 18),
   ({4,20,32}, 18),
   ({2,21,32}, 18),
   ({8,21,32}, 18),
   ({4,21,25,32}, 18),
   ({15,21,25,32}, 18),
   ({10,21,34}, 18),
   ({4,21,35}, 18),
   ({4,12,38}, 18),
   ({7,21,38}, 18),
   ({15,21,38}, 18),
   ({10,17,21,38}, 18),
   ({10,22,38}, 18),
   ({4,30,38}, 18),
   ({10,21,40}, 18),
   ({9,28}, 19),
   ({0,12,19,28}, 19),
   ({4,21,28}, 19),
   ({12,21,28}, 19),
   ({14,21,30}, 19),
   ({14,33}, 19),
   ({0,12,35}, 19),
   ({7,17,21,35}, 19),
   ({7,21,25,35}, 19),
   ({14,21,38}, 19),
   ({7,30,42}, 19),
   ({14,23,30,42}, 19),
   ({7,21,22}, 20),
   ({13,21,22}, 20),
   ({1,17,21,22}, 20),
   ({20,21,29}, 20),
   ({11,21,31}, 20),
   ({1,17,21,31}, 20),
   ({20,21,35}, 20),
   ({11,21,25,41}, 20),
   ({20,21,25,41}, 20),
   ({9,12,24}, 21),
   ({15,21,27}, 21),
   ({9,12,31}, 21),
   ({11,30,33}, 21),
   ({18,30,33}, 21),
   ({2,23,30,33}, 21),
   ({9,12,19,40}, 21),
   ({0,12,21}, 22),
   ({13,17,21,27}, 22),
   ({6,25,29}, 22),
   ({4,21,25,29}, 22),
   ({15,21,25,29}, 22),
   ({13,17,36}, 22),
   ({13,17,21,38}, 22),
   ({21,30,42}, 22),
   ({0,12,19,24}, 23),
   ({10,21,24}, 23),
   ({1,17,30}, 23),
   ({18,21,32}, 23),
   ({12,25,41}, 23),
   ({18,23,30,42}, 23),
   ({6,12,28}, 24),
   ({1,17,26,36}, 24),
   ({14,30,36}, 24),
   ({6,16,25,41}, 24),
   ({10,17,21,22}, 25),
   ({20,21,25,32}, 25),
   ({9,12,19,28}, 26),
   ({14,23,30,33}, 26),
   ({13,17,21,22}, 27),
   ({20,21,25,29}, 27),
   ({9,12,19,24}, 28),
   ({18,23,30,33}, 28),
   ({6,16,25,29}, 29),
   ({13,17,26,36}, 29)]

/-- Lookup in the tagged list; `99` means "absent". -/
def lookupD : List (Finset (Fin 43) × ℕ) → Finset (Fin 43) → ℕ
  | [], _ => 99
  | (S, d) :: rest, T => if S = T then d else lookupD rest T

/-- The single boolean check that carries the whole analysis. -/
def checkOK : Bool :=
  reachD.all (fun q =>
    (q.1.card ≤ 4)
    && (lookupD reachD (absStep Move.L q.1) ≤ q.2 + 1)
    && (lookupD reachD (absStep Move.M q.1) ≤ q.2 + 1)
    && (lookupD reachD (absStep Move.R q.1) ≤ q.2 + 1)
    && (lookupD reachD (absStep Move.L q.1) ≤ 29)
    && (lookupD reachD (absStep Move.M q.1) ≤ 29)
    && (lookupD reachD (absStep Move.R q.1) ≤ 29)
    && ((q.1.card ≤ 0) || (1 ≤ q.2))
    && ((q.1.card ≤ 1) || (3 ≤ q.2))
    && ((q.1.card ≤ 2) || (5 ≤ q.2))
    && ((q.1.card ≤ 3) || (11 ≤ q.2)))

theorem checkOK_true : checkOK = true := by decide +kernel

lemma lookupD_empty : lookupD reachD ∅ = 0 := by decide +kernel

/-! ### Consequences of the check -/

lemma lookupD_mem : ∀ (L : List (Finset (Fin 43) × ℕ)) (T : Finset (Fin 43)),
    lookupD L T ≠ 99 → (T, lookupD L T) ∈ L := by
  intro L
  induction L with
  | nil => intro T h; exact absurd rfl h
  | cons q rest ih =>
      intro T h
      obtain ⟨S, d⟩ := q
      by_cases hs : S = T
      · subst hs
        simp only [lookupD] at h ⊢
        exact List.mem_cons_self ..
      · simp only [lookupD, if_neg hs] at h ⊢
        exact List.mem_cons_of_mem _ (ih T h)

/-- The conjuncts of `checkOK`, for one entry of the list. -/
lemma check_entry {T : Finset (Fin 43)} {d : ℕ} (h : (T, d) ∈ reachD) :
    T.card ≤ 4 ∧ (∀ m : Move, lookupD reachD (absStep m T) ≤ d + 1)
      ∧ (∀ m : Move, lookupD reachD (absStep m T) ≤ 29)
      ∧ (T.card ≤ 0 ∨ 1 ≤ d) ∧ (T.card ≤ 1 ∨ 3 ≤ d)
      ∧ (T.card ≤ 2 ∨ 5 ≤ d) ∧ (T.card ≤ 3 ∨ 11 ≤ d) := by
  have hall := List.all_eq_true.mp checkOK_true (T, d) h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hall
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := hall
  refine ⟨h1, ?_, ?_, h8, h9, h10, h11⟩
  · intro m; cases m
    · exact h2
    · exact h3
    · exact h4
  · intro m; cases m
    · exact h5
    · exact h6
    · exact h7

/-- The invariant carried along a run: the state is in the list, and its depth
tag is at most the number of moves made. -/
lemma absRunFrom_le (w : List Move) :
    ∀ (T : Finset (Fin 43)) (k : ℕ), lookupD reachD T ≤ k → k ≤ 29 →
      lookupD reachD (absRunFrom T w) ≤ k + w.length ∧
        lookupD reachD (absRunFrom T w) ≤ 29 := by
  induction w with
  | nil => intro T k h hk; exact ⟨by simpa using h, le_trans h hk⟩
  | cons m w ih =>
      intro T k h hk
      have hne : lookupD reachD T ≠ 99 := by omega
      have hmem := lookupD_mem reachD T hne
      obtain ⟨-, hstep, hcap, -⟩ := check_entry hmem
      have h1 : lookupD reachD (absStep m T) ≤ k + 1 :=
        le_trans (hstep m) (by omega)
      have h2 : lookupD reachD (absStep m T) ≤ 29 := hcap m
      have := ih (absStep m T) (min (k+1) 29) (le_min h1 h2) (min_le_right _ _)
      have hfold : absRunFrom T (m :: w) = absRunFrom (absStep m T) w := rfl
      rw [hfold]
      constructor
      · refine le_trans this.1 ?_
        simp only [List.length_cons]
        omega
      · exact this.2

lemma absRun_le (w : List Move) :
    lookupD reachD (absRun w) ≤ w.length ∧ lookupD reachD (absRun w) ≤ 29 := by
  have := absRunFrom_le w ∅ 0 (by rw [lookupD_empty]) (by omega)
  simpa [absRun] using this

lemma absRun_entry (w : List Move) :
    (absRun w, lookupD reachD (absRun w)) ∈ reachD := by
  have h := (absRun_le w).2
  exact lookupD_mem reachD _ (by omega)

/-! ### The maximum and the depths -/

theorem card_run_le_four (w : List Move) : (run lam w).card ≤ 4 := by
  rw [card_run_eq]
  exact (check_entry (absRun_entry w)).1

theorem N_le_four (k : ℕ) : N lam k ≤ 4 := by
  apply Finset.sup_le
  intro v _
  exact card_run_le_four _

/-- If a run is short, its configuration is small. -/
lemma card_run_le_of_length (w : List Move) (c b : ℕ)
    (hsel : ∀ (T : Finset (Fin 43)) (d : ℕ), (T, d) ∈ reachD → T.card ≤ c ∨ b ≤ d)
    (hw : w.length < b) : (run lam w).card ≤ c := by
  rw [card_run_eq]
  rcases hsel _ _ (absRun_entry w) with h | h
  · exact h
  · exact absurd (le_trans h (absRun_le w).1) (by omega)

theorem N_le_of_lt (c b : ℕ)
    (hsel : ∀ (T : Finset (Fin 43)) (d : ℕ), (T, d) ∈ reachD → T.card ≤ c ∨ b ≤ d)
    (k : ℕ) (hk : k < b) : N lam k ≤ c := by
  apply Finset.sup_le
  intro v _
  refine card_run_le_of_length _ c b hsel ?_
  simpa using hk

theorem N_zero_le_zero : N lam 0 ≤ 0 :=
  N_le_of_lt 0 1 (fun _ _ h => (check_entry h).2.2.2.1) _ (by omega)

theorem N_two_le_one : N lam 2 ≤ 1 :=
  N_le_of_lt 1 3 (fun _ _ h => (check_entry h).2.2.2.2.1) _ (by omega)

theorem N_four_le_two : N lam 4 ≤ 2 :=
  N_le_of_lt 2 5 (fun _ _ h => (check_entry h).2.2.2.2.2.1) _ (by omega)

theorem N_ten_le_three : N lam 10 ≤ 3 :=
  N_le_of_lt 3 11 (fun _ _ h => (check_entry h).2.2.2.2.2.2) _ (by omega)

/-! ### Lower bounds from explicit runs -/

lemma le_N_of_word {k : ℕ} (v : Fin k → Move) : (absRun (List.ofFn v)).card ≤ N lam k := by
  have h : (run lam (List.ofFn v)).card = (absRun (List.ofFn v)).card := card_run_eq _
  rw [← h]
  exact Finset.le_sup (f := fun u : Fin k → Move => (run lam (List.ofFn u)).card)
    (Finset.mem_univ v)

/-- The run `M` gives one knot. -/
theorem one_le_N_one : 1 ≤ N lam 1 := by
  have h := le_N_of_word (k := 1) ![Move.M]
  have hc : (absRun (List.ofFn ![Move.M])).card = 1 := by decide +kernel
  omega

/-- The run `MLM` gives two knots. -/
theorem two_le_N_three : 2 ≤ N lam 3 := by
  have h := le_N_of_word (k := 3) ![Move.M, Move.L, Move.M]
  have hc : (absRun (List.ofFn ![Move.M, Move.L, Move.M])).card = 2 := by decide +kernel
  omega

/-- The run `MLMLM` gives three knots. -/
theorem three_le_N_five : 3 ≤ N lam 5 := by
  have h := le_N_of_word (k := 5) ![Move.M, Move.L, Move.M, Move.L, Move.M]
  have hc : (absRun (List.ofFn ![Move.M, Move.L, Move.M, Move.L, Move.M])).card = 3 := by decide +kernel
  omega

/-- The run `MLMLRRRLMRM` gives four knots. -/
theorem four_le_N_eleven : 4 ≤ N lam 11 := by
  have h := le_N_of_word (k := 11) ![Move.M, Move.L, Move.M, Move.L, Move.R, Move.R, Move.R, Move.L, Move.M, Move.R, Move.M]
  have hc : (absRun (List.ofFn ![Move.M, Move.L, Move.M, Move.L, Move.R, Move.R, Move.R, Move.L, Move.M, Move.R, Move.M])).card = 4 := by decide +kernel
  omega

/-- **T8 (supergolden, exact maximum).**  The largest number of simultaneous
knots at the supergolden parameter is `4`. -/
theorem sup_N_lam : IsGreatest (Set.range (N lam)) 4 := by
  constructor
  · exact ⟨11, le_antisymm (N_le_four 11) four_le_N_eleven⟩
  · rintro y ⟨k, rfl⟩
    exact N_le_four k

lemma N_mono' {a b : ℕ} (hab : a ≤ b) : N lam a ≤ N lam b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih => exact le_trans ih (N_mono one_lt_lam k)

/-- `d 1 = 1`. -/
theorem d_one : d lam 1 = 1 := by
  have hmem : (1:ℕ) ∈ {k | 1 ≤ N lam k} := one_le_N_one
  refine le_antisymm (Nat.sInf_le hmem) ?_
  refine le_csInf ⟨1, hmem⟩ ?_
  intro k hk
  by_contra hlt
  push_neg at hlt
  interval_cases k
  · have := N_zero_le_zero
    simp only [Set.mem_setOf_eq] at hk
    omega

/-- `d 2 = 3`. -/
theorem d_two : d lam 2 = 3 := by
  have hmem : (3:ℕ) ∈ {k | 2 ≤ N lam k} := two_le_N_three
  refine le_antisymm (Nat.sInf_le hmem) ?_
  refine le_csInf ⟨3, hmem⟩ ?_
  intro k hk
  by_contra hlt
  push_neg at hlt
  have hmono : N lam k ≤ N lam 2 := N_mono' (by omega)
  have := N_two_le_one
  simp only [Set.mem_setOf_eq] at hk
  omega

/-- `d 3 = 5`. -/
theorem d_three : d lam 3 = 5 := by
  have hmem : (5:ℕ) ∈ {k | 3 ≤ N lam k} := three_le_N_five
  refine le_antisymm (Nat.sInf_le hmem) ?_
  refine le_csInf ⟨5, hmem⟩ ?_
  intro k hk
  by_contra hlt
  push_neg at hlt
  have hmono : N lam k ≤ N lam 4 := N_mono' (by omega)
  have := N_four_le_two
  simp only [Set.mem_setOf_eq] at hk
  omega

/-- `d 4 = 11`. -/
theorem d_four : d lam 4 = 11 := by
  have hmem : (11:ℕ) ∈ {k | 4 ≤ N lam k} := four_le_N_eleven
  refine le_antisymm (Nat.sInf_le hmem) ?_
  refine le_csInf ⟨11, hmem⟩ ?_
  intro k hk
  by_contra hlt
  push_neg at hlt
  have hmono : N lam k ≤ N lam 10 := N_mono' (by omega)
  have := N_ten_le_three
  simp only [Set.mem_setOf_eq] at hk
  omega

end Supergolden
end KnotGame
