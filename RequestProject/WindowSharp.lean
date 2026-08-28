import RequestProject.Transversality

/-!
# T25 — sharpness of the transversality window

Round 3 certified (`RequestProject.Transversality.transversality`) that for the
class

  `𝓑₀₁ = { g(x) = 1 + ∑_{i≥1} c_i x^i : c_i ∈ {−1,0,1} }`

and `δ = 1/1000`, on the window `x ∈ [1/2, 667/1000]`,

  `|g(x)| ≤ δ  ⟹  g′(x) < −δ`.

This file certifies that the conclusion **fails** just beyond that window: it
exhibits two explicit members of the class and two explicit rational points of
`(667/1000, 67/100]` at which the value is small and the derivative is not
below `−δ`.

* `witness_at_3339` — at `x = 3339/5000 = 0.6678`, only `0.0008` beyond the
  certified right endpoint, the degree-22 member `sharpPoly` has
  `0 < g(x) ≤ 1/1000` and `−1/1000 ≤ g′(x) < 0`.  Both inequalities of the
  transversality statement are met exactly at the tolerance `δ = 1/1000`.
* `witness_at_3343` — at `x = 3343/5000 = 0.6686` the degree-26 member
  `strongPoly` fails the conclusion with room to spare: `0 < g(x) ≤ 1/100000`
  and `g′(x) > 0`.

`transversality_fails_beyond_window` packages the first as a counterexample of
the shape of `transversality`, and `window_not_extendable` states the
consequence: the certified window `[1/2, 667/1000]` cannot be replaced by
`[1/2, 67/100]`, so it is essentially optimal for this class at this `δ`.
`deriv_witness_at_3339` restates the failure for the actual derivative, as in
`transversality_deriv`.

## What is trusted

Nothing about the search that produced the two coefficient vectors
(`scripts/window_sharp_search.py`) is trusted: the vectors are data, and every
inequality above is checked by the kernel over exact rationals.  The series is
*not* truncated — the coefficient sequences `coeffOf l` are zero from
`l.length` on, so `gval` and `gder` are the finite sums `gval_coeffOf`,
`gder_coeffOf` exactly, with no tail estimate needed.

## Conventions (SCRUPLES)

* The commission asks for `|g(x)| ≤ 1/1000` and `g′(x) ≥ −1/1000`; both
  witnesses satisfy the strict form of the failure, `g′(x) > −1/1000`.
* A member of the class must have constant term `1`; both lists start with `1`.
* `gder` is the termwise derivative series of `RequestProject.Transversality`;
  on `(−4/5, 4/5)` it is the derivative (`hasDerivAt_gval`), which is what
  `deriv_witness_at_3339` uses.
-/

namespace KnotGame
namespace Transversality

open Finset

/-! ### Coefficient sequences with finite support -/

/-- The coefficient sequence of a finite list of integers, extended by zero. -/
def coeffOf (l : List ℤ) (i : ℕ) : ℤ := l.getD i 0

lemma coeffOf_of_le {l : List ℤ} {i : ℕ} (h : l.length ≤ i) : coeffOf l i = 0 :=
  List.getD_eq_default l 0 h

/-- A list of `{−1,0,1}`s defines a coefficient sequence of the class. -/
lemma coeffOf_mem {l : List ℤ} (hl : ∀ z ∈ l, z = -1 ∨ z = 0 ∨ z = 1) (i : ℕ) :
    coeffOf l i = -1 ∨ coeffOf l i = 0 ∨ coeffOf l i = 1 := by
  rcases lt_or_ge i l.length with h | h
  · have : coeffOf l i = l[i] := by
      rw [coeffOf, List.getD_eq_getElem l 0 h]
    rw [this]
    exact hl _ (List.getElem_mem h)
  · exact Or.inr (Or.inl (coeffOf_of_le h))

/-- For a finitely supported coefficient sequence the series is a finite sum. -/
lemma gval_coeffOf (l : List ℤ) (x : ℝ) :
    gval (coeffOf l) x = ∑ i ∈ range l.length, ((coeffOf l i : ℤ) : ℝ) * x ^ i := by
  rw [gval, tsum_eq_sum]
  intro b hb
  rw [mem_range, not_lt] at hb
  rw [coeffOf_of_le hb]
  simp

/-- The same for the termwise derivative series. -/
lemma gder_coeffOf (l : List ℤ) (x : ℝ) :
    gder (coeffOf l) x = ∑ i ∈ range l.length, (i : ℝ) * ((coeffOf l i : ℤ) : ℝ) * x ^ (i - 1) := by
  rw [gder, tsum_eq_sum]
  intro b hb
  rw [mem_range, not_lt] at hb
  rw [coeffOf_of_le hb]
  simp

/-! ### The first witness: degree 22 at `x = 3339/5000` -/

/-- The coefficients of the first witness. -/
def sharpList : List ℤ :=
  [1, -1, -1, -1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0]

/-- The first witness, as a member of the class. -/
def sharpPoly : ℕ → ℤ := coeffOf sharpList

lemma sharpPoly_zero : sharpPoly 0 = 1 := rfl

lemma sharpPoly_mem (i : ℕ) : sharpPoly i = -1 ∨ sharpPoly i = 0 ∨ sharpPoly i = 1 :=
  coeffOf_mem (by decide) i

lemma gval_sharpPoly (x : ℝ) :
    gval sharpPoly x = ∑ i ∈ range 23, ((sharpPoly i : ℤ) : ℝ) * x ^ i := by
  rw [sharpPoly, gval_coeffOf]
  rfl

lemma gder_sharpPoly (x : ℝ) :
    gder sharpPoly x = ∑ i ∈ range 23, (i : ℝ) * ((sharpPoly i : ℤ) : ℝ) * x ^ (i - 1) := by
  rw [sharpPoly, gder_coeffOf]
  rfl

/-- **T25, first witness.**  At `x = 3339/5000`, just beyond the certified
window, the value is positive and at most `δ = 1/1000` while the derivative is
above `−δ`: the transversality conclusion fails. -/
theorem witness_at_3339 :
    0 < gval sharpPoly (3339 / 5000 : ℝ) ∧
    gval sharpPoly (3339 / 5000 : ℝ) ≤ 1 / 1000 ∧
    -(1 / 1000) < gder sharpPoly (3339 / 5000 : ℝ) ∧
    gder sharpPoly (3339 / 5000 : ℝ) < 0 := by
  rw [gval_sharpPoly, gder_sharpPoly]
  refine ⟨by norm_num [Finset.sum_range_succ, sharpPoly, coeffOf, sharpList],
    by norm_num [Finset.sum_range_succ, sharpPoly, coeffOf, sharpList],
    by norm_num [Finset.sum_range_succ, sharpPoly, coeffOf, sharpList],
    by norm_num [Finset.sum_range_succ, sharpPoly, coeffOf, sharpList]⟩

/-! ### The second witness: degree 26 at `x = 3343/5000`, with room to spare -/

/-- The coefficients of the second witness. -/
def strongList : List ℤ :=
  [1, -1, -1, -1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, -1, -1, 1, -1, 1]

/-- The second witness, as a member of the class. -/
def strongPoly : ℕ → ℤ := coeffOf strongList

lemma strongPoly_zero : strongPoly 0 = 1 := rfl

lemma strongPoly_mem (i : ℕ) : strongPoly i = -1 ∨ strongPoly i = 0 ∨ strongPoly i = 1 :=
  coeffOf_mem (by decide) i

lemma gval_strongPoly (x : ℝ) :
    gval strongPoly x = ∑ i ∈ range 27, ((strongPoly i : ℤ) : ℝ) * x ^ i := by
  rw [strongPoly, gval_coeffOf]
  rfl

lemma gder_strongPoly (x : ℝ) :
    gder strongPoly x = ∑ i ∈ range 27, (i : ℝ) * ((strongPoly i : ℤ) : ℝ) * x ^ (i - 1) := by
  rw [strongPoly, gder_coeffOf]
  rfl

/-- **T25, second witness.**  At `x = 3343/5000` the failure is not marginal:
the value is at most `1/100000` and the derivative is positive. -/
theorem witness_at_3343 :
    0 < gval strongPoly (3343 / 5000 : ℝ) ∧
    gval strongPoly (3343 / 5000 : ℝ) ≤ 1 / 100000 ∧
    0 < gder strongPoly (3343 / 5000 : ℝ) := by
  rw [gval_strongPoly, gder_strongPoly]
  refine ⟨by norm_num [Finset.sum_range_succ, strongPoly, coeffOf, strongList],
    by norm_num [Finset.sum_range_succ, strongPoly, coeffOf, strongList],
    by norm_num [Finset.sum_range_succ, strongPoly, coeffOf, strongList]⟩

/-! ### The sharpness statements -/

/-- **T25.**  Beyond the certified window there is a member of the class and a
point at which `δ`-transversality fails: an explicit `c ∈ {−1,0,1}^ℕ` with
`c₀ = 1` and a rational `x ∈ (667/1000, 67/100]` with `|g(x)| ≤ 1/1000` and
`g′(x) ≥ −1/1000`. -/
theorem transversality_fails_beyond_window :
    ∃ (c : ℕ → ℤ) (x : ℝ), c 0 = 1 ∧ (∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) ∧
      667 / 1000 < x ∧ x ≤ 67 / 100 ∧ |gval c x| ≤ 1 / 1000 ∧ -(1 / 1000) ≤ gder c x := by
  obtain ⟨hpos, hle, hder, -⟩ := witness_at_3339
  refine ⟨sharpPoly, 3339 / 5000, sharpPoly_zero, sharpPoly_mem, by norm_num, by norm_num, ?_,
    le_of_lt hder⟩
  rw [abs_of_pos hpos]
  exact hle

/-- **T25, the sharpness statement.**  The certified window `[1/2, 667/1000]`
cannot be enlarged to `[1/2, 67/100]`: the conclusion of `transversality` is
false there. -/
theorem window_not_extendable :
    ¬ (∀ (c : ℕ → ℤ), c 0 = 1 → (∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) → ∀ x : ℝ,
        1 / 2 ≤ x → x ≤ 67 / 100 → |gval c x| ≤ 1 / 1000 → gder c x < -(1 / 1000)) := by
  intro H
  obtain ⟨hpos, hle, hder, -⟩ := witness_at_3339
  have habs : |gval sharpPoly (3339 / 5000 : ℝ)| ≤ 1 / 1000 := by
    rw [abs_of_pos hpos]; exact hle
  have := H sharpPoly sharpPoly_zero sharpPoly_mem (3339 / 5000) (by norm_num) (by norm_num) habs
  linarith

/-- **T25, for the derivative.**  The failure at `x = 3339/5000` is a failure
for the actual derivative of the sum, not merely for the termwise series. -/
theorem deriv_witness_at_3339 :
    HasDerivAt (gval sharpPoly) (gder sharpPoly (3339 / 5000 : ℝ)) (3339 / 5000 : ℝ) ∧
      -(1 / 1000) < deriv (gval sharpPoly) (3339 / 5000 : ℝ) := by
  have hcabs : ∀ i, |((sharpPoly i : ℤ) : ℝ)| ≤ 1 := by
    intro i
    rcases sharpPoly_mem i with h | h | h <;> rw [h] <;> norm_num
  have hx : |(3339 / 5000 : ℝ)| < 4 / 5 := by
    rw [abs_of_pos (by norm_num : (0:ℝ) < 3339 / 5000)]; norm_num
  have hd := hasDerivAt_gval sharpPoly hcabs hx
  refine ⟨hd, ?_⟩
  rw [hd.deriv]
  exact witness_at_3339.2.2.1

end Transversality
end KnotGame
