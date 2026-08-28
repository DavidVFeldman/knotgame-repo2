import RequestProject.Threshold

/-!
# Section 7: the case `lam = √2` (Work Order 8)

Proposition 7.1: the blocks `RR` and `LL` preserve exactly `{x < 1/2}` and
`{x > 1/2}` and act as `x ↦ 2x` and `x ↦ 2x - 1`.

Proposition 7.2: writing `x = (a + b√2)/2`, the coordinate `b` doubles under
such a block, and the position after `n` of them is `{2^(n-1) b √2}`.
-/

namespace KnotGame
namespace Sqrt2

open Real

/-- The parameter `λ = √2`. -/
noncomputable abbrev lam2 : ℝ := Real.sqrt 2

lemma lam2_sq : lam2 * lam2 = 2 := Real.mul_self_sqrt (by norm_num)

lemma lam2_pos : 0 < lam2 := Real.sqrt_pos.mpr (by norm_num)

lemma one_lt_lam2 : 1 < lam2 := by nlinarith [lam2_sq, lam2_pos]

lemma lam2_lt_two : lam2 < 2 := by nlinarith [lam2_sq, lam2_pos]

lemma r_lam2 : r lam2 = Real.sqrt 2 / 2 := by
  rw [r, eq_div_iff (by norm_num : (2:ℝ) ≠ 0), inv_mul_eq_div,
    div_eq_iff (ne_of_gt lam2_pos)]
  nlinarith [lam2_sq]

lemma g_lam2 : g lam2 = 1 - Real.sqrt 2 / 2 := by rw [g, r_lam2]

/-- The composite of two branch maps: `f_δ ∘ f_ε` is
`x ↦ 2x + (δ - 2ε) + (ε - δ)√2`. -/
theorem comp_branch (e d : Fin 2) (x : ℝ) :
    f lam2 d (f lam2 e x)
      = 2 * x + (((d : ℕ) : ℝ) - 2 * ((e : ℕ) : ℝ))
          + ((((e : ℕ) : ℝ)) - ((d : ℕ) : ℝ)) * Real.sqrt 2 := by
  have h2 := lam2_sq
  fin_cases e <;> fin_cases d <;> simp [f] <;>
    first | linear_combination x * h2 | linear_combination (x - 1) * h2

/-- **Proposition 7.1** for `RR`: the block preserves exactly the knots with
`x < 1/2`. -/
theorem survivesWord_RR (x : ℝ) :
    survivesWord lam2 x [Move.R, Move.R] ↔ x < 1/2 := by
  have h2 := lam2_sq
  have hp := lam2_pos
  have h1 := one_lt_lam2
  simp only [survivesWord_cons, survivesWord_nil, and_true, survives_R, act_R, r_lam2]
  constructor
  · rintro ⟨-, h⟩
    have := mul_lt_mul_of_pos_left h hp
    nlinarith
  · intro h
    refine ⟨by linarith, ?_⟩
    have := mul_lt_mul_of_pos_left h hp
    linarith

/-- **Proposition 7.1** for `RR`: the block acts as `x ↦ 2x`. -/
theorem posAfter_RR (x : ℝ) : posAfter lam2 x [Move.R, Move.R] = 2 * x := by
  have h2 := lam2_sq
  simp only [posAfter_cons, posAfter_nil, act_R]
  linear_combination x * h2

/-- **Proposition 7.1** for `LL`: the block preserves exactly the knots with
`x > 1/2`. -/
theorem survivesWord_LL (x : ℝ) :
    survivesWord lam2 x [Move.L, Move.L] ↔ 1/2 < x := by
  have h2 := lam2_sq
  have hp := lam2_pos
  have h1 := one_lt_lam2
  simp only [survivesWord_cons, survivesWord_nil, and_true, survives_L, act_L, g_lam2]
  constructor
  · rintro ⟨-, h⟩
    nlinarith
  · intro h
    have := mul_lt_mul_of_pos_left h hp
    refine ⟨by linarith, by nlinarith⟩

/-- **Proposition 7.1** for `LL`: the block acts as `x ↦ 2x - 1`. -/
theorem posAfter_LL (x : ℝ) : posAfter lam2 x [Move.L, Move.L] = 2 * x - 1 := by
  have h2 := lam2_sq
  simp only [posAfter_cons, posAfter_nil, act_L]
  linear_combination (x - 1) * h2

/-- A word of blocks: `false` for `RR`, `true` for `LL`. -/
def blockWord : List Bool → List Move
  | [] => []
  | b :: s => (if b then [Move.L, Move.L] else [Move.R, Move.R]) ++ blockWord s

@[simp] lemma blockWord_nil : blockWord [] = [] := rfl

@[simp] lemma blockWord_false : blockWord [false] = [Move.R, Move.R] := by simp [blockWord]

@[simp] lemma blockWord_true : blockWord [true] = [Move.L, Move.L] := by simp [blockWord]

lemma blockWord_cons (c : Bool) (s : List Bool) :
    blockWord (c :: s) = blockWord [c] ++ blockWord s := by
  cases c <;> simp [blockWord]

lemma blockWord_length (s : List Bool) : (blockWord s).length = 2 * s.length := by
  induction s with
  | nil => simp
  | cons c s ih => cases c <;> simp [blockWord, ih] <;> omega

/-- **Proposition 7.2, first part.** Under a block of type `RR` or `LL` the
coordinate `b` of `x = (a+b√2)/2` doubles (and `a ↦ 2a - 2δ`). -/
theorem block_coords (a b : ℤ) (x : ℝ) (hx : x = (a + b * Real.sqrt 2) / 2)
    (c : Bool) :
    posAfter lam2 x (blockWord [c])
      = (((2 * a - 2 * (if c then 1 else 0) : ℤ) : ℝ) + ((2 * b : ℤ) : ℝ) * Real.sqrt 2) / 2 := by
  cases c
  · rw [blockWord_false, posAfter_RR, hx, if_neg (by simp)]
    push_cast
    ring
  · rw [blockWord_true, posAfter_LL, hx, if_pos rfl]
    push_cast
    ring

/-- A surviving block acts as the doubling map on the circle. -/
lemma posAfter_block_eq_fract (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (c : Bool)
    (hs : survivesWord lam2 x (blockWord [c])) :
    posAfter lam2 x (blockWord [c]) = Int.fract (2 * x) := by
  cases c
  · rw [blockWord_false] at hs ⊢
    rw [survivesWord_RR] at hs
    rw [posAfter_RR, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
  · rw [blockWord_true] at hs ⊢
    rw [survivesWord_LL] at hs
    rw [posAfter_LL]
    have h : Int.fract (2 * x) = Int.fract (2 * x - ((1:ℤ) : ℝ)) := (Int.fract_sub_intCast _ 1).symm
    rw [h]
    push_cast
    rw [Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]

lemma block_mem_Ioo (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (c : Bool)
    (hs : survivesWord lam2 x (blockWord [c])) :
    0 < posAfter lam2 x (blockWord [c]) ∧ posAfter lam2 x (blockWord [c]) < 1 := by
  cases c
  · rw [blockWord_false] at hs ⊢
    rw [survivesWord_RR] at hs
    rw [posAfter_RR]
    constructor <;> linarith
  · rw [blockWord_true] at hs ⊢
    rw [survivesWord_LL] at hs
    rw [posAfter_LL]
    constructor <;> linarith

lemma fract_pow_two_fract (n : ℕ) (y : ℝ) :
    Int.fract ((2:ℝ) ^ n * Int.fract y) = Int.fract (2 ^ n * y) := by
  conv_rhs => rw [← Int.fract_add_floor y]
  rw [mul_add]
  have h : (2:ℝ) ^ n * ((⌊y⌋ : ℤ) : ℝ) = ((2 ^ n * ⌊y⌋ : ℤ) : ℝ) := by push_cast; ring
  rw [h, Int.fract_add_intCast]

/-- The position after `n` surviving blocks is `{2ⁿ x}`. -/
lemma posAfter_blocks_eq_fract (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (s : List Bool)
    (hs : survivesWord lam2 x (blockWord s)) :
    posAfter lam2 x (blockWord s) = Int.fract (2 ^ s.length * x) := by
  induction s generalizing x with
  | nil => simp [Int.fract_eq_self.mpr ⟨le_of_lt hx0, hx1⟩]
  | cons c s ih =>
      rw [blockWord_cons] at hs ⊢
      rw [survivesWord_append] at hs
      rw [posAfter_append]
      obtain ⟨h1, h2⟩ := hs
      obtain ⟨hy0, hy1⟩ := block_mem_Ioo x hx0 hx1 c h1
      rw [ih _ hy0 hy1 h2, posAfter_block_eq_fract x hx0 hx1 c h1, fract_pow_two_fract]
      congr 1
      rw [List.length_cons, pow_succ]
      ring

/-- **Proposition 7.2.** The position after `n ≥ 1` blocks of type `RR` or `LL`
is `{2^(n-1) b √2}`, where `b` is the coordinate at the start. -/
theorem posAfter_blocks (a b : ℤ) (x : ℝ) (hx : x = (a + b * Real.sqrt 2) / 2)
    (hx0 : 0 < x) (hx1 : x < 1) (s : List Bool) (hs : survivesWord lam2 x (blockWord s))
    (hne : s ≠ []) :
    posAfter lam2 x (blockWord s)
      = Int.fract (2 ^ (s.length - 1) * (b : ℝ) * Real.sqrt 2) := by
  rw [posAfter_blocks_eq_fract x hx0 hx1 s hs]
  obtain ⟨n, hn⟩ : ∃ n, s.length = n + 1 := by
    cases s with
    | nil => exact absurd rfl hne
    | cons c s => exact ⟨s.length, rfl⟩
  rw [hn, hx]
  have key : (2:ℝ) ^ (n + 1) * ((a + b * Real.sqrt 2) / 2)
      = ((2 ^ n * a : ℤ) : ℝ) + 2 ^ n * (b : ℝ) * Real.sqrt 2 := by
    push_cast
    rw [pow_succ]
    ring
  rw [key, Int.fract_intCast_add]
  simp

end Sqrt2
end KnotGame
