import RequestProject.Pisot

/-!
# T22a — the ternary reformulation at `λ = 3/2` (paper `prop:ternary`)

At `λ = 3/2` one has `r = 2/3` and `g = 1/3`, so the three deleted intervals

  `L ↦ [0,1/3]`,  `M ↦ [1/3,2/3]`,  `R ↦ [2/3,1]`

are exactly the three ternary cells of `[0,1]`.  Coding the moves by digits
`L, M, R ↦ 0, 1, 2` (`code`) and writing `D x = ⌊3x⌋` for the leading ternary
digit, the rules become:

* a knot dies exactly when its digit is the forbidden one, `D x = code m`
  (`survives_iff_digit_ne`);
* a survivor moves to `(3x − [D x > code m])/2` (`act_eq_ternary`);
* when `m = M` the point `1/2` is adjoined — this is the definition
  `step_M` of `RequestProject.Basic`, restated here as `step_ternary`.

`D x` is a genuine ternary digit only when `x` is not an endpoint of a cell.
The second half of the file supplies the reason this never happens along the
game: every position reachable from `1/2` in `n` moves is `m / 2 ^ (n+1)` with
`m` odd (`Dyadic`, `dyadic_posAfter`), and `3 m` is odd while `2 ^ (n+1)` and
`2 ^ (n+2)` are even, so `3x ∉ {1, 2}` (`three_mul_ne_one`, `three_mul_ne_two`).

## Conventions (SCRUPLES)

* The paper writes the survivor's image as `(3x − [D(x) > c])/2`; the Lean form
  uses `if code m < D x then 1 else 0` for the bracket, which is the same thing.
* `D` is defined for every real `x`; all statements about it carry the
  hypotheses `0 < x`, `x < 1` and, where the cell boundary matters, `3x ≠ 1`,
  `3x ≠ 2`.
* Nothing here assumes the knot is on the orbit of `1/2`: the dyadic invariant
  is a separate statement, applied where the digit rule needs it.
-/

namespace KnotGame
namespace Ternary

variable {x : ℝ} {n : ℕ}

lemma one_lt_lam32 : (1 : ℝ) < 3 / 2 := by norm_num

lemma r32 : r (3 / 2 : ℝ) = 2 / 3 := by norm_num [r]

lemma g32 : g (3 / 2 : ℝ) = 1 / 3 := by rw [g, r32]; norm_num

/-- The leading ternary digit `D(x) = ⌊3x⌋`. -/
noncomputable def D (x : ℝ) : ℤ := ⌊3 * x⌋

/-- The three moves coded as ternary digits, `L, M, R ↦ 0, 1, 2`. -/
def code : Move → ℤ
  | .L => 0
  | .M => 1
  | .R => 2

@[simp] lemma code_L : code Move.L = 0 := rfl
@[simp] lemma code_M : code Move.M = 1 := rfl
@[simp] lemma code_R : code Move.R = 2 := rfl

lemma code_injective : Function.Injective code := by
  intro a b hab
  cases a <;> cases b <;> simp only [code_L, code_M, code_R] at hab ⊢ <;> omega

/-! ### The digit of a point of `(0,1)` -/

lemma D_eq_zero_iff (hx0 : 0 < x) : D x = 0 ↔ x < 1 / 3 := by
  rw [D, Int.floor_eq_iff]
  constructor
  · rintro ⟨-, h⟩; push_cast at h; linarith
  · intro h; refine ⟨by push_cast; linarith, by push_cast; linarith⟩

lemma D_eq_two_iff (hx1 : x < 1) : D x = 2 ↔ 2 / 3 ≤ x := by
  rw [D, Int.floor_eq_iff]
  constructor
  · rintro ⟨h, -⟩; push_cast at h; linarith
  · intro h; refine ⟨by push_cast; linarith, by push_cast; linarith⟩

lemma D_eq_one_iff : D x = 1 ↔ (1 / 3 ≤ x ∧ x < 2 / 3) := by
  rw [D, Int.floor_eq_iff]
  constructor
  · rintro ⟨h1, h2⟩; push_cast at h1 h2; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by push_cast; linarith, by push_cast; linarith⟩

/-- The digit of a point of `(0,1)` is `0`, `1` or `2`. -/
lemma D_cases (hx0 : 0 < x) (hx1 : x < 1) : D x = 0 ∨ D x = 1 ∨ D x = 2 := by
  rcases lt_or_ge x (1 / 3) with h | h
  · exact Or.inl ((D_eq_zero_iff hx0).mpr h)
  · rcases lt_or_ge x (2 / 3) with h' | h'
    · exact Or.inr (Or.inl (D_eq_one_iff.mpr ⟨h, h'⟩))
    · exact Or.inr (Or.inr ((D_eq_two_iff hx1).mpr h'))

/-! ### T22a: the digit rule -/

/-- **T22a, survival** (paper `prop:ternary`).  At `λ = 3/2` a knot dies under
the move `m` exactly when its ternary digit is the digit coding `m`. -/
theorem survives_iff_digit_ne (hx0 : 0 < x) (hx1 : x < 1)
    (h1 : 3 * x ≠ 1) (h2 : 3 * x ≠ 2) (m : Move) :
    survives (3 / 2 : ℝ) m x ↔ D x ≠ code m := by
  have hx13 : x ≠ 1 / 3 := fun h => h1 (by rw [h]; norm_num)
  have hx23 : x ≠ 2 / 3 := fun h => h2 (by rw [h]; norm_num)
  cases m
  · rw [survives_L, g32, code_L]
    constructor
    · intro h hD
      exact absurd ((D_eq_zero_iff hx0).mp hD) (by linarith)
    · intro h
      rcases lt_or_ge x (1 / 3) with h' | h'
      · exact absurd ((D_eq_zero_iff hx0).mpr h') h
      · exact lt_of_le_of_ne h' (Ne.symm hx13)
  · rw [survives_M, r32, code_M]
    constructor
    · rintro (h | h) hD
      · exact absurd (D_eq_one_iff.mp hD).1 (by linarith)
      · exact absurd (D_eq_one_iff.mp hD).2 (by linarith)
    · intro h
      rcases lt_or_ge x (1 / 3) with h' | h'
      · exact Or.inl (by linarith)
      · rcases lt_or_ge x (2 / 3) with h'' | h''
        · exact absurd (D_eq_one_iff.mpr ⟨h', h''⟩) h
        · exact Or.inr (by
            have : 2 / 3 < x := lt_of_le_of_ne h'' (Ne.symm hx23)
            linarith)
  · rw [survives_R, r32, code_R]
    constructor
    · intro h hD
      exact absurd ((D_eq_two_iff hx1).mp hD) (by linarith)
    · intro h
      rcases lt_or_ge x (2 / 3) with h' | h'
      · exact h'
      · exact absurd ((D_eq_two_iff hx1).mpr h') h

/-- **T22a, motion** (paper `prop:ternary`).  A survivor of the move `m` is
carried to `(3x − [D x > code m])/2`. -/
theorem act_eq_ternary (hx0 : 0 < x) (hx1 : x < 1) (m : Move)
    (hs : survives (3 / 2 : ℝ) m x) :
    act (3 / 2 : ℝ) m x = (3 * x - (if code m < D x then 1 else 0)) / 2 := by
  cases m
  · have hg : (1 : ℝ) / 3 < x := by
      have h' : g (3 / 2 : ℝ) < x := hs
      rwa [g32] at h'
    have hD : ¬ D x = 0 := fun h => absurd ((D_eq_zero_iff hx0).mp h) (by linarith)
    have hDpos : (0 : ℤ) < D x := by
      rcases D_cases hx0 hx1 with h | h | h <;> omega
    rw [act_L, if_pos (by simp only [code_L]; omega)]
    ring
  · rcases hs with hs | hs
    · have hlt : x < 1 / 3 := by rw [r32] at hs; linarith
      have hD : D x = 0 := (D_eq_zero_iff hx0).mpr hlt
      rw [act_M_of_lt (3 / 2 : ℝ) x (by rw [r32]; linarith), if_neg (by simp [hD])]
      ring
    · have hgt : (2 : ℝ) / 3 < x := by rw [r32] at hs; linarith
      have hD : D x = 2 := (D_eq_two_iff hx1).mpr (by linarith)
      rw [act_M_of_gt (3 / 2 : ℝ) x (by rw [r32]; push_neg; linarith),
        if_pos (by simp [hD])]
      ring
  · have hlt : x < 2 / 3 := by rw [survives_R, r32] at hs; exact hs
    have hD : ¬ D x = 2 := fun h => absurd ((D_eq_two_iff hx1).mp h) (by linarith)
    have hDlt : D x < 2 := by rcases D_cases hx0 hx1 with h | h | h <;> omega
    rw [act_R, if_neg (by simp only [code_R]; omega)]
    ring

/-- **T22a, the new knot.**  When `m = M` the point `1/2` is adjoined; for the
other two moves nothing is added.  (This is the definition of `step`, recorded
here so that `prop:ternary` is stated in one place.) -/
theorem step_ternary (S : Finset ℝ) :
    step (3 / 2 : ℝ) Move.M S
        = ((survivors (3 / 2 : ℝ) Move.M S).image (act (3 / 2 : ℝ) Move.M)) ∪ {(1 : ℝ) / 2} ∧
      step (3 / 2 : ℝ) Move.L S
        = (survivors (3 / 2 : ℝ) Move.L S).image (act (3 / 2 : ℝ) Move.L) ∧
      step (3 / 2 : ℝ) Move.R S
        = (survivors (3 / 2 : ℝ) Move.R S).image (act (3 / 2 : ℝ) Move.R) :=
  ⟨step_M _ S, step_L _ S, step_R _ S⟩

/-- Exactly one of the three moves is fatal at a point of `(0,1)` that is not a
cell endpoint: the tiling of `[0,1]` by the three cells, in the form the
cylinder count `T24a` uses. -/
theorem exists_unique_fatal (hx0 : 0 < x) (hx1 : x < 1)
    (h1 : 3 * x ≠ 1) (h2 : 3 * x ≠ 2) :
    ∃! m : Move, ¬ survives (3 / 2 : ℝ) m x := by
  have hiff : ∀ m : Move, ¬ survives (3 / 2 : ℝ) m x ↔ D x = code m := by
    intro m
    rw [survives_iff_digit_ne hx0 hx1 h1 h2 m, not_not]
  obtain ⟨m, hm⟩ : ∃ m : Move, D x = code m := by
    rcases D_cases hx0 hx1 with h | h | h
    · exact ⟨Move.L, by simpa using h⟩
    · exact ⟨Move.M, by simpa using h⟩
    · exact ⟨Move.R, by simpa using h⟩
  exact ⟨m, (hiff m).mpr hm, fun m' hm' => code_injective (((hiff m').mp hm').symm.trans hm)⟩

/-! ### The dyadic invariant -/

/-- `x` is an odd multiple of `2 ^ -(n+1)`. -/
def Dyadic (n : ℕ) (x : ℝ) : Prop := ∃ k : ℤ, Odd k ∧ x = (k : ℝ) / 2 ^ (n + 1)

lemma dyadic_half : Dyadic 0 (1 / 2 : ℝ) := ⟨1, odd_one, by norm_num⟩

/-- Both branch maps send an odd multiple of `2 ^ -(n+1)` to an odd multiple of
`2 ^ -(n+2)`, at `λ = 3/2`. -/
lemma dyadic_act (hd : Dyadic n x) (m : Move) : Dyadic (n + 1) (act (3 / 2 : ℝ) m x) := by
  obtain ⟨k, hk, rfl⟩ := hd
  have hbranch : act (3 / 2 : ℝ) m ((k : ℝ) / 2 ^ (n + 1)) = (3 / 2 : ℝ) * ((k : ℝ) / 2 ^ (n + 1))
      ∨ act (3 / 2 : ℝ) m ((k : ℝ) / 2 ^ (n + 1))
        = (3 / 2 : ℝ) * ((k : ℝ) / 2 ^ (n + 1)) - ((3 / 2 : ℝ) - 1) := by
    unfold act f
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hpow : ((2 : ℝ) ^ (n + 1)) ≠ 0 := by positivity
  rcases hbranch with h | h
  · refine ⟨3 * k, by simpa using (Odd.mul (by decide) hk), ?_⟩
    rw [h]
    push_cast
    field_simp
    ring
  · refine ⟨3 * k - 2 ^ (n + 1), ?_, ?_⟩
    · have h3 : Odd (3 * k) := Odd.mul (by decide) hk
      have h2 : Even ((2 : ℤ) ^ (n + 1)) := by
        exact (Int.even_pow).mpr ⟨by decide, by omega⟩
      exact Odd.sub_even h3 h2
    · rw [h]
      push_cast
      field_simp
      ring

/-- The position after `n` moves of a knot born at `1/2` is an odd multiple of
`2 ^ -(n+1)`. -/
lemma dyadic_posAfter (w : List Move) : Dyadic w.length (posAfter (3 / 2 : ℝ) (1 / 2 : ℝ) w) := by
  have key : ∀ (w : List Move) (n : ℕ) (y : ℝ), Dyadic n y →
      Dyadic (n + w.length) (posAfter (3 / 2 : ℝ) y w) := by
    intro w
    induction w with
    | nil => intro n y hy; simpa using hy
    | cons m w ih =>
        intro n y hy
        have := ih (n + 1) _ (dyadic_act hy m)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
  simpa using key w 0 (1 / 2 : ℝ) dyadic_half

/-- A dyadic point of the above kind is never the left endpoint `1/3` of the
middle cell. -/
lemma three_mul_ne_one (hd : Dyadic n x) : 3 * x ≠ 1 := by
  obtain ⟨k, hk, rfl⟩ := hd
  intro h
  have hpow : ((2 : ℝ) ^ (n + 1)) ≠ 0 := by positivity
  have hZ : (3 * k : ℤ) = 2 ^ (n + 1) := by
    have : (3 : ℝ) * (k : ℝ) = ((2 : ℝ) ^ (n + 1)) := by
      field_simp at h; linarith
    exact_mod_cast this
  have h3 : Odd (3 * k) := Odd.mul (by decide) hk
  have h2 : Even ((2 : ℤ) ^ (n + 1)) := (Int.even_pow).mpr ⟨by decide, by omega⟩
  rw [hZ] at h3
  exact (Int.not_even_iff_odd.mpr h3) h2

/-- A dyadic point of the above kind is never the right endpoint `2/3` of the
middle cell. -/
lemma three_mul_ne_two (hd : Dyadic n x) : 3 * x ≠ 2 := by
  obtain ⟨k, hk, rfl⟩ := hd
  intro h
  have hpow : ((2 : ℝ) ^ (n + 1)) ≠ 0 := by positivity
  have hZ : (3 * k : ℤ) = 2 ^ (n + 2) := by
    have : (3 : ℝ) * (k : ℝ) = ((2 : ℝ) ^ (n + 2)) := by
      field_simp at h; ring_nf at h ⊢; linarith
    exact_mod_cast this
  have h3 : Odd (3 * k) := Odd.mul (by decide) hk
  have h2 : Even ((2 : ℤ) ^ (n + 2)) := (Int.even_pow).mpr ⟨by decide, by omega⟩
  rw [hZ] at h3
  exact (Int.not_even_iff_odd.mpr h3) h2

end Ternary
end KnotGame
