import RequestProject.Basic

/-!
# Running the game at `λ = 3/2` in exact integer arithmetic

At `λ = 3/2` every knot position after `j` moves is a dyadic rational with
denominator `2^j` (paper Section on `λ = 3/2`; the branch maps are
`x ↦ (3/2)x` and `x ↦ (3/2)x - 1/2`, and the newborn knot sits at `1/2`).  This
file records a *computable* model of `run` at that parameter: a configuration
after `j` moves is a `Finset ℤ` of numerators over the common denominator
`2^j`, and `runZ` is the corresponding transition system.

`run_eq_image_runZ` identifies the real configuration `run (3/2) w` with the
image of `runZ w` under `A ↦ A / 2^{|w|}`, so that statements about actual
configurations — their cardinality, and containments between configurations
produced by words of different lengths — reduce to decidable statements about
finite sets of integers.
-/

namespace KnotGame

/-! ## The integer model -/

/-- The embedding of a numerator over `2^j` into `ℝ`. -/
noncomputable def emb (j : ℕ) (A : ℤ) : ℝ := (A : ℝ) / 2 ^ j

lemma emb_injective (j : ℕ) : Function.Injective (emb j) := by
  intro a b hab
  have h2 : (2:ℝ) ^ j ≠ 0 := by positivity
  have h := congrArg (fun y : ℝ => y * 2 ^ j) hab
  simp only [emb, div_mul_cancel₀ _ h2] at h
  exact_mod_cast h

/-- Rescaling a numerator to a finer denominator does not move the point. -/
lemma emb_scale (j k : ℕ) (A : ℤ) : emb (j + k) (A * 2 ^ k) = emb j A := by
  have h2 : (2:ℝ) ^ j ≠ 0 := by positivity
  have h2k : (2:ℝ) ^ k ≠ 0 := by positivity
  simp only [emb, pow_add]
  push_cast
  field_simp

/-- Survival at `λ = 3/2`, on numerators over `2^j`. -/
def survivesZ (c : Move) (j : ℕ) (A : ℤ) : Bool :=
  match c with
  | Move.L => decide (2 ^ j < 3 * A)
  | Move.M => decide (3 * A < 2 ^ j) || decide (2 * 2 ^ j < 3 * A)
  | Move.R => decide (3 * A < 2 * 2 ^ j)

/-- The action at `λ = 3/2`, on numerators: the result is a numerator over
`2^{j+1}`. -/
def actZ (c : Move) (j : ℕ) (A : ℤ) : ℤ :=
  match c with
  | Move.L => 3 * A - 2 ^ j
  | Move.M => if 3 * A < 2 ^ j then 3 * A else 3 * A - 2 ^ j
  | Move.R => 3 * A

/-- One move on an integer configuration. -/
def stepZ (c : Move) (j : ℕ) (S : Finset ℤ) : Finset ℤ :=
  (S.filter (fun A => survivesZ c j A = true)).image (actZ c j) ∪
    (if c = Move.M then {2 ^ j} else ∅)

/-- A run on an integer configuration, starting at depth `j`. -/
def runZFrom : List Move → ℕ → Finset ℤ → Finset ℤ
  | [], _, S => S
  | c :: w, j, S => runZFrom w (j + 1) (stepZ c j S)

/-- The integer model of `run`: numerators over `2^{|w|}`. -/
def runZ (w : List Move) : Finset ℤ := runZFrom w 0 ∅

/-! ## The bridge -/

lemma survives_emb (c : Move) (j : ℕ) (A : ℤ) :
    survives (3/2 : ℝ) c (emb j A) ↔ survivesZ c j A = true := by
  have h2 : (0:ℝ) < 2 ^ j := by positivity
  have hr : r (3/2 : ℝ) = 2/3 := by norm_num [r]
  have hg : g (3/2 : ℝ) = 1/3 := by norm_num [g, r]
  cases c
  · rw [survives_L, hg, survivesZ]
    simp only [emb, decide_eq_true_eq]
    rw [lt_div_iff₀ h2]
    constructor
    · intro hh; exact_mod_cast (by linarith : ((2:ℝ) ^ j) < 3 * (A : ℝ))
    · intro hh
      have : ((2:ℝ) ^ j) < 3 * (A : ℝ) := by exact_mod_cast hh
      linarith
  · rw [survives_M, hr, survivesZ]
    simp only [emb, Bool.or_eq_true, decide_eq_true_eq]
    rw [div_lt_iff₀ h2, lt_div_iff₀ h2]
    constructor
    · rintro (hh | hh)
      · left
        have : 3 * (A:ℝ) < 2 ^ j := by linarith
        exact_mod_cast this
      · right
        have : 2 * (2:ℝ) ^ j < 3 * (A:ℝ) := by linarith
        exact_mod_cast this
    · rintro (hh | hh)
      · left
        have : 3 * (A:ℝ) < 2 ^ j := by exact_mod_cast hh
        linarith
      · right
        have : 2 * (2:ℝ) ^ j < 3 * (A:ℝ) := by exact_mod_cast hh
        linarith
  · rw [survives_R, hr, survivesZ]
    simp only [emb, decide_eq_true_eq]
    rw [div_lt_iff₀ h2]
    constructor
    · intro hh
      have : 3 * (A:ℝ) < 2 * 2 ^ j := by linarith
      exact_mod_cast this
    · intro hh
      have : 3 * (A:ℝ) < 2 * 2 ^ j := by exact_mod_cast hh
      linarith

lemma act_emb (c : Move) (j : ℕ) (A : ℤ) :
    act (3/2 : ℝ) c (emb j A) = emb (j + 1) (actZ c j A) := by
  have h2 : (0:ℝ) < 2 ^ j := by positivity
  have hr : r (3/2 : ℝ) = 2/3 := by norm_num [r]
  cases c
  · rw [act_L, actZ]
    simp only [emb, pow_succ]
    push_cast
    field_simp
    ring
  · by_cases hlt : 3 * A < 2 ^ j
    · have hlt' : emb j A < r (3/2:ℝ) / 2 := by
        rw [hr]
        have : 3 * (A:ℝ) < 2 ^ j := by exact_mod_cast hlt
        rw [emb, div_lt_iff₀ h2]
        linarith
      rw [act_M_of_lt _ _ hlt', actZ, if_pos hlt]
      simp only [emb, pow_succ]
      push_cast
      field_simp
    · have hlt' : ¬ emb j A < r (3/2:ℝ) / 2 := by
        rw [hr]
        have : ¬ 3 * (A:ℝ) < 2 ^ j := by
          intro hc
          exact hlt (by exact_mod_cast hc)
        rw [emb, div_lt_iff₀ h2]
        intro hc
        exact this (by linarith)
      rw [act_M_of_gt _ _ hlt', actZ, if_neg hlt]
      simp only [emb, pow_succ]
      push_cast
      field_simp
      ring
  · rw [act_R, actZ]
    simp only [emb, pow_succ]
    push_cast
    field_simp

lemma step_emb (c : Move) (j : ℕ) (S : Finset ℤ) :
    step (3/2 : ℝ) c (S.image (emb j)) = (stepZ c j S).image (emb (j + 1)) := by
  classical
  have hsing : (if c = Move.M then ({(1:ℝ)/2} : Finset ℝ) else ∅)
      = ((if c = Move.M then ({2 ^ j} : Finset ℤ) else ∅)).image (emb (j + 1)) := by
    by_cases hc : c = Move.M
    · rw [if_pos hc, if_pos hc, Finset.image_singleton]
      have h2 : (2:ℝ) ^ j ≠ 0 := by positivity
      simp only [emb, pow_succ]
      push_cast
      field_simp
    · rw [if_neg hc, if_neg hc, Finset.image_empty]
  have hfil : (S.filter (fun A => survives (3/2 : ℝ) c (emb j A)))
      = S.filter (fun A => survivesZ c j A = true) :=
    Finset.filter_congr (fun A _ => by simpa using survives_emb c j A)
  rw [step, survivors, hsing, stepZ, Finset.image_union, Finset.filter_image,
    Finset.image_image, Finset.image_image, hfil]
  congr 1
  exact Finset.image_congr (fun A _ => act_emb c j A)

lemma runFrom_emb : ∀ (w : List Move) (j : ℕ) (S : Finset ℤ),
    runFrom (3/2 : ℝ) (S.image (emb j)) w = (runZFrom w j S).image (emb (j + w.length))
  | [], j, S => by simp [runZFrom]
  | c :: w, j, S => by
      rw [runFrom_cons, step_emb, runFrom_emb w (j + 1) (stepZ c j S), runZFrom]
      congr 2
      simp only [List.length_cons]
      omega

/-- **The bridge.**  At `λ = 3/2` the configuration after the word `w` is the
image of the integer configuration `runZ w` under `A ↦ A / 2^{|w|}`. -/
theorem run_eq_image_runZ (w : List Move) :
    run (3/2 : ℝ) w = (runZ w).image (emb w.length) := by
  have := runFrom_emb w 0 ∅
  simpa [run, runZ] using this

/-- The number of knots after `w` is computed by the integer model. -/
theorem card_run_eq_card_runZ (w : List Move) :
    (run (3/2 : ℝ) w).card = (runZ w).card := by
  rw [run_eq_image_runZ, Finset.card_image_of_injective _ (emb_injective _)]

/-- Rescaling an integer configuration to a finer denominator. -/
def scaleZ (k : ℕ) (S : Finset ℤ) : Finset ℤ := S.image (fun A => A * 2 ^ k)

lemma image_scaleZ (j k : ℕ) (S : Finset ℤ) :
    (scaleZ k S).image (emb (j + k)) = S.image (emb j) := by
  rw [scaleZ, Finset.image_image]
  exact Finset.image_congr (fun A _ => emb_scale j k A)

/-- **Containment of configurations, decidably.**  For words `v` and `w` with
`|v| + k = |w|`, the configuration after `v` is contained in the configuration
after `w` exactly when the rescaled integer configurations are. -/
theorem run_subset_run_iff {v w : List Move} {k : ℕ} (hk : v.length + k = w.length) :
    run (3/2 : ℝ) v ⊆ run (3/2 : ℝ) w ↔ scaleZ k (runZ v) ⊆ runZ w := by
  rw [run_eq_image_runZ, run_eq_image_runZ, ← hk, ← image_scaleZ v.length k (runZ v),
    Finset.image_subset_image_iff (emb_injective _)]

end KnotGame
