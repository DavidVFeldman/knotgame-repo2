import Mathlib

/-!
# Knot counts in an interval deletion game — basic definitions

This file formalises the setting of Section 1 of the paper
*Knot counts in an interval deletion game* (Work Order 1 of the commission).

Fix a real `lam` with `1 < lam`, and write `r = lam⁻¹`, `g = 1 - r`.
A configuration is a `Finset ℝ` (thought of as a subset of the open interval
`(0,1)`).  There are three moves `L`, `M`, `R`; each deletes a *closed*
subinterval of length `g`, rejoins and rescales by `lam`.

All survival conditions use **strict** inequalities, since the deleted interval
is closed.
-/

namespace KnotGame

open scoped BigOperators

/-- The three moves of the game. -/
inductive Move
  | L : Move
  | M : Move
  | R : Move
  deriving DecidableEq, Repr

namespace Move

instance : Fintype Move := ⟨{Move.L, Move.M, Move.R}, by intro m; cases m <;> decide⟩

end Move

variable (lam : ℝ)

/-- The retained proportion `r = lam⁻¹`. -/
noncomputable def r : ℝ := lam⁻¹

/-- The deleted proportion `g = 1 - r`. -/
noncomputable def g : ℝ := 1 - r lam

lemma r_pos (h : 1 < lam) : 0 < r lam := by
  have : (0:ℝ) < lam := lt_trans zero_lt_one h
  simpa [r] using inv_pos.mpr this

lemma r_lt_one (h : 1 < lam) : r lam < 1 := by
  have h0 : (0:ℝ) < lam := lt_trans zero_lt_one h
  rw [r, inv_lt_one_iff₀]
  exact Or.inr h

lemma g_pos (h : 1 < lam) : 0 < g lam := by
  have := r_lt_one lam h
  simp [g]; linarith

lemma g_lt_one (h : 1 < lam) : g lam < 1 := by
  have := r_pos lam h
  simp [g]; linarith

/-- The closed interval deleted by each move. -/
noncomputable def deleted : Move → Set ℝ
  | .L => Set.Icc 0 (g lam)
  | .M => Set.Icc (r lam / 2) (1 - r lam / 2)
  | .R => Set.Icc (r lam) 1

/-- **Acceptance test for Work Order 1**: each of the three deleted intervals
has length `g`. -/
theorem volume_deleted (h : 1 < lam) (m : Move) :
    MeasureTheory.volume (deleted lam m) = ENNReal.ofReal (g lam) := by
  have h1 : r lam < 1 := r_lt_one lam h
  have h0 : 0 < r lam := r_pos lam h
  cases m
  · simp [deleted, Real.volume_Icc]
  · simp only [deleted, Real.volume_Icc]
    congr 1
    simp only [g]
    ring
  · simp [deleted, Real.volume_Icc, g]

/-- A knot at `x` survives the move `m`.  Strict inequalities throughout: a knot
on the boundary of the (closed) deleted interval is destroyed. -/
noncomputable def survives : Move → ℝ → Prop
  | .L, x => g lam < x
  | .M, x => x < r lam / 2 ∨ 1 - r lam / 2 < x
  | .R, x => x < r lam

@[simp] lemma survives_L (x : ℝ) : survives lam Move.L x ↔ g lam < x := Iff.rfl
@[simp] lemma survives_R (x : ℝ) : survives lam Move.R x ↔ x < r lam := Iff.rfl
@[simp] lemma survives_M (x : ℝ) :
    survives lam Move.M x ↔ (x < r lam / 2 ∨ 1 - r lam / 2 < x) := Iff.rfl

noncomputable instance decidableSurvives (m : Move) (x : ℝ) : Decidable (survives lam m x) := by
  cases m <;> simp only [survives_L, survives_M, survives_R] <;> infer_instance

/-- Survival is exactly the complement of the deleted interval, for a knot in the
open interval `(0,1)`. -/
theorem survives_iff_not_mem_deleted (h : 1 < lam) (m : Move) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) : survives lam m x ↔ x ∉ deleted lam m := by
  have h1 : r lam < 1 := r_lt_one lam h
  have h0 : 0 < r lam := r_pos lam h
  cases m
  · simp only [deleted, survives_L, Set.mem_Icc, not_and_or, not_le]
    constructor
    · intro hh; exact Or.inr hh
    · rintro (hh | hh)
      · linarith
      · exact hh
  · simp only [deleted, survives_M, Set.mem_Icc, not_and_or, not_le]
  · simp only [deleted, survives_R, Set.mem_Icc, not_and_or, not_le]
    constructor
    · intro hh; exact Or.inl hh
    · rintro (hh | hh)
      · exact hh
      · linarith

/-- The two branch maps: `f 0 x = lam * x` and `f 1 x = lam * x - (lam - 1)`. -/
noncomputable def f (i : Fin 2) (x : ℝ) : ℝ :=
  if i = 0 then lam * x else lam * x - (lam - 1)

@[simp] lemma f_zero (x : ℝ) : f lam 0 x = lam * x := by simp [f]
@[simp] lemma f_one (x : ℝ) : f lam 1 x = lam * x - (lam - 1) := by simp [f]

/-- The branch a surviving knot takes: `0` (lower) or `1` (upper).  This depends
only on the position of the knot. -/
noncomputable def branch : Move → ℝ → Fin 2
  | .L, _ => 1
  | .M, x => if x < r lam / 2 then 0 else 1
  | .R, _ => 0

@[simp] lemma branch_L (x : ℝ) : branch lam Move.L x = 1 := rfl
@[simp] lemma branch_R (x : ℝ) : branch lam Move.R x = 0 := rfl
@[simp] lemma branch_M (x : ℝ) :
    branch lam Move.M x = if x < r lam / 2 then 0 else 1 := rfl

/-- Where a knot at `x` is carried by the move `m` (meaningful when it survives). -/
noncomputable def act (m : Move) (x : ℝ) : ℝ := f lam (branch lam m x) x

@[simp] lemma act_L (x : ℝ) : act lam Move.L x = lam * x - (lam - 1) := by simp [act]
@[simp] lemma act_R (x : ℝ) : act lam Move.R x = lam * x := by simp [act]

lemma act_M_of_lt (x : ℝ) (hx : x < r lam / 2) : act lam Move.M x = lam * x := by
  simp [act, hx]

lemma act_M_of_gt (x : ℝ) (hx : ¬ x < r lam / 2) :
    act lam Move.M x = lam * x - (lam - 1) := by
  simp [act, hx]

/-- The survivors of a move inside a configuration. -/
noncomputable def survivors (m : Move) (S : Finset ℝ) : Finset ℝ :=
  S.filter (survives lam m)

/-- One move applied to a configuration: the images of the survivors, together
with the new knot at `1/2` when the move is `M`. -/
noncomputable def step (m : Move) (S : Finset ℝ) : Finset ℝ :=
  (survivors lam m S).image (act lam m) ∪ (if m = Move.M then {(1:ℝ)/2} else ∅)

@[simp] lemma step_L (S : Finset ℝ) :
    step lam Move.L S = (survivors lam Move.L S).image (act lam Move.L) := by
  simp [step]

@[simp] lemma step_R (S : Finset ℝ) :
    step lam Move.R S = (survivors lam Move.R S).image (act lam Move.R) := by
  simp [step]

@[simp] lemma step_M (S : Finset ℝ) :
    step lam Move.M S =
      (survivors lam Move.M S).image (act lam Move.M) ∪ {(1:ℝ)/2} := by
  simp [step]

/-- A run applied to a given starting configuration, letters applied left to
right. -/
noncomputable def runFrom (S : Finset ℝ) (w : List Move) : Finset ℝ :=
  w.foldl (fun T m => step lam m T) S

/-- A run applied to the empty configuration. -/
noncomputable def run (w : List Move) : Finset ℝ := runFrom lam ∅ w

@[simp] lemma runFrom_nil (S : Finset ℝ) : runFrom lam S [] = S := rfl

@[simp] lemma runFrom_cons (S : Finset ℝ) (m : Move) (w : List Move) :
    runFrom lam S (m :: w) = runFrom lam (step lam m S) w := rfl

@[simp] lemma run_nil : run lam [] = ∅ := rfl

/-- The largest number of knots present after a run of length `n`. -/
noncomputable def N (n : ℕ) : ℕ :=
  Finset.univ.sup (fun v : Fin n → Move => (run lam (List.ofFn v)).card)

/-- The least length of a run producing `k` simultaneous knots (`0` if there is
none). -/
noncomputable def d (k : ℕ) : ℕ := sInf {n | k ≤ N lam n}

/-- Whether a knot at `x` survives an entire word, moving along the way. -/
def survivesWord : ℝ → List Move → Prop
  | _, [] => True
  | x, m :: w => survives lam m x ∧ survivesWord (act lam m x) w

/-- The position of a knot after an entire word (meaningful if it survives). -/
noncomputable def posAfter : ℝ → List Move → ℝ
  | x, [] => x
  | x, m :: w => posAfter (act lam m x) w

@[simp] lemma survivesWord_nil (x : ℝ) : survivesWord lam x [] := trivial

@[simp] lemma survivesWord_cons (x : ℝ) (m : Move) (w : List Move) :
    survivesWord lam x (m :: w) ↔
      survives lam m x ∧ survivesWord lam (act lam m x) w := Iff.rfl

@[simp] lemma posAfter_nil (x : ℝ) : posAfter lam x [] = x := rfl

@[simp] lemma posAfter_cons (x : ℝ) (m : Move) (w : List Move) :
    posAfter lam x (m :: w) = posAfter lam (act lam m x) w := rfl

lemma posAfter_append (x : ℝ) (a b : List Move) :
    posAfter lam x (a ++ b) = posAfter lam (posAfter lam x a) b := by
  induction a generalizing x with
  | nil => simp
  | cons m a ih => simp [ih]

lemma survivesWord_append (x : ℝ) (a b : List Move) :
    survivesWord lam x (a ++ b) ↔
      survivesWord lam x a ∧ survivesWord lam (posAfter lam x a) b := by
  induction a generalizing x with
  | nil => simp
  | cons m a ih => simp [ih, and_assoc]

noncomputable instance decidableSurvivesWord : ∀ (x : ℝ) (w : List Move),
    Decidable (survivesWord lam x w)
  | _, [] => by simpa using instDecidableTrue
  | x, m :: w => by
      letI := decidableSurvivesWord (act lam m x) w
      simpa using instDecidableAnd

/-- The suffix count: the number of positions carrying an `M` whose subsequent
suffix keeps `1/2` alive. -/
noncomputable def births : List Move → ℕ
  | [] => 0
  | m :: w => births w + (if m = Move.M ∧ survivesWord lam (1/2) w then 1 else 0)

@[simp] lemma births_nil : births lam [] = 0 := rfl

lemma births_cons (m : Move) (w : List Move) :
    births lam (m :: w) =
      births lam w + (if m = Move.M ∧ survivesWord lam (1/2) w then 1 else 0) := rfl

end KnotGame
