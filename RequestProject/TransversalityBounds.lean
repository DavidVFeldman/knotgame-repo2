import Mathlib

/-!
# Analytic ingredients for δ-transversality (round 3, Target T9)

This file collects the estimates that reduce the transversality statement for
the class

  `𝓑₀₁ = { g(x) = 1 + ∑_{i≥1} c_i x^i : c_i ∈ {−1,0,1} }`

to a finite computation: the tail bounds beyond a truncation depth, and the
"centered form" bounds for the variation of a truncation, and of its
derivative, over an interval.  Nothing here is specific to the window
`[1/2, 667/1000]`.

The series and its termwise derivative are

  `gval c x = ∑' i, c i * x ^ i`,      `gder c x = ∑' i, i * c i * x ^ (i-1)`,

and the truncations at depth `i` (that is, using the coefficients `c 0 … c i`)
are `gpart c i x` and `dpart c i x`.  That `gder` really is the derivative of
`gval` is proved in `RequestProject.Transversality` (`hasDerivAt_gval`).
-/

namespace KnotGame
namespace Transversality

open Finset

/-- The value of a power series with integer coefficients. -/
noncomputable def gval (c : ℕ → ℤ) (x : ℝ) : ℝ := ∑' i : ℕ, (c i : ℝ) * x ^ i

/-- The termwise derivative series. -/
noncomputable def gder (c : ℕ → ℤ) (x : ℝ) : ℝ := ∑' i : ℕ, (i : ℝ) * (c i : ℝ) * x ^ (i - 1)

/-- The truncation of `gval` at depth `i` (coefficients `c 0 … c i`). -/
noncomputable def gpart (c : ℕ → ℤ) (i : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ range (i + 1), (c j : ℝ) * x ^ j

/-- The truncation of `gder` at depth `i`. -/
noncomputable def dpart (c : ℕ → ℤ) (i : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ range (i + 1), (j : ℝ) * (c j : ℝ) * x ^ (j - 1)

section

variable {c : ℕ → ℤ} {x b m : ℝ}

/-! ### Summability -/

lemma summable_nat_mul_pow (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Summable (fun i : ℕ => (i : ℝ) * x ^ (i - 1)) := by
  rw [← summable_nat_add_iff 1]
  have h2 : Summable (fun n : ℕ => (n : ℝ) * x ^ n) := by
    have := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := x)
      (by rw [Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx1)
    simpa using this
  have h3 : Summable (fun n : ℕ => x ^ n) := summable_geometric_of_lt_one hx0 hx1
  have h4 : Summable (fun n : ℕ => ((n : ℝ) + 1) * x ^ n) := by
    simpa [add_mul] using h2.add h3
  simpa using h4

lemma summable_gterm (hc : ∀ i, |(c i : ℝ)| ≤ 1) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Summable (fun i : ℕ => (c i : ℝ) * x ^ i) := by
  refine Summable.of_norm_bounded (g := fun i : ℕ => x ^ i)
    (summable_geometric_of_lt_one hx0 hx1) ?_
  intro i
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hx0]
  exact mul_le_of_le_one_left (by positivity) (hc i)

lemma summable_dterm (hc : ∀ i, |(c i : ℝ)| ≤ 1) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Summable (fun i : ℕ => (i : ℝ) * (c i : ℝ) * x ^ (i - 1)) := by
  refine Summable.of_norm_bounded (g := fun i : ℕ => (i : ℝ) * x ^ (i - 1))
    (summable_nat_mul_pow hx0 hx1) ?_
  intro i
  dsimp only
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_nonneg hx0, Nat.abs_cast]
  have hp : (0:ℝ) ≤ x ^ (i - 1) := by positivity
  have hi : (0:ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  nlinarith [mul_nonneg hi hp, abs_nonneg ((c i : ℝ)), hc i]

/-! ### The two geometric sums -/

lemma hasSum_succ_geom (hb0 : 0 ≤ b) (hb1 : b < 1) :
    HasSum (fun n : ℕ => ((n : ℝ) + 1) * b ^ n) ((1 - b)⁻¹ ^ 2) := by
  have h1 : HasSum (fun n : ℕ => (n : ℝ) * b ^ n) (b / (1 - b) ^ 2) := by
    have := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := b)
      (by rw [Real.norm_eq_abs, abs_of_nonneg hb0]; exact hb1)
    simpa using this
  have h2 : HasSum (fun n : ℕ => b ^ n) ((1 - b)⁻¹) := hasSum_geometric_of_lt_one hb0 hb1
  have h3 := h1.add h2
  have hne : (1 - b) ≠ 0 := ne_of_gt (by linarith)
  have heq : b / (1 - b) ^ 2 + (1 - b)⁻¹ = (1 - b)⁻¹ ^ 2 := by field_simp; ring
  rw [heq] at h3
  have hfun : (fun n : ℕ => (n : ℝ) * b ^ n + b ^ n) = fun n : ℕ => ((n : ℝ) + 1) * b ^ n := by
    funext n; ring
  rwa [hfun] at h3

/-! ### Tail bounds beyond the truncation depth -/

/-- The tail of the series beyond depth `i` is at most `b^(i+1)/(1-b)`. -/
lemma tail_le (hc : ∀ i, |(c i : ℝ)| ≤ 1) (hx0 : 0 ≤ x) (hxb : x ≤ b) (hb1 : b < 1) (i : ℕ) :
    |gval c x - gpart c i x| ≤ b ^ (i + 1) * (1 - b)⁻¹ := by
  have hb0 : 0 ≤ b := le_trans hx0 hxb
  have hsum := summable_gterm hc hx0 (lt_of_le_of_lt hxb hb1)
  have hsplit := hsum.sum_add_tsum_nat_add (i + 1)
  have hdiff : gval c x - gpart c i x = ∑' n : ℕ, (c (n + (i+1)) : ℝ) * x ^ (n + (i+1)) := by
    rw [gval, gpart, ← hsplit]; ring
  have hgeo : HasSum (fun n : ℕ => b ^ (n + (i+1))) (b ^ (i+1) * (1 - b)⁻¹) := by
    have h := (hasSum_geometric_of_lt_one hb0 hb1).mul_left (b ^ (i+1))
    have heq : (fun n : ℕ => b ^ (n + (i+1))) = fun n : ℕ => b ^ (i+1) * b ^ n := by
      funext n; rw [pow_add]; ring
    rw [heq]; exact h
  have hbnd : ∀ n : ℕ, ‖(c (n + (i+1)) : ℝ) * x ^ (n + (i+1))‖ ≤ b ^ (n + (i+1)) := by
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hx0]
    have h2 : x ^ (n + (i+1)) ≤ b ^ (n + (i+1)) := pow_le_pow_left₀ hx0 hxb _
    nlinarith [pow_nonneg hx0 (n + (i+1)), abs_nonneg ((c (n+(i+1)) : ℝ)), hc (n+(i+1))]
  have hkey := tsum_of_norm_bounded hgeo hbnd
  rw [hdiff]
  simpa [Real.norm_eq_abs] using hkey

/-- The tail of the derivative series beyond depth `i` is at most
`(i+1) b^i/(1-b)^2`. -/
lemma dtail_le (hc : ∀ i, |(c i : ℝ)| ≤ 1) (hx0 : 0 ≤ x) (hxb : x ≤ b) (hb1 : b < 1) (i : ℕ) :
    |gder c x - dpart c i x| ≤ ((i : ℝ) + 1) * b ^ i * (1 - b)⁻¹ ^ 2 := by
  have hb0 : 0 ≤ b := le_trans hx0 hxb
  have hsum := summable_dterm hc hx0 (lt_of_le_of_lt hxb hb1)
  have hsplit := hsum.sum_add_tsum_nat_add (i + 1)
  have hdiff : gder c x - dpart c i x
      = ∑' n : ℕ, ((n + (i+1) : ℕ) : ℝ) * (c (n + (i+1)) : ℝ) * x ^ ((n + (i+1)) - 1) := by
    rw [gder, dpart, ← hsplit]; ring
  have hgeo : HasSum (fun n : ℕ => ((i:ℝ) + 1) * b ^ i * (((n:ℝ) + 1) * b ^ n))
      (((i:ℝ) + 1) * b ^ i * (1 - b)⁻¹ ^ 2) := (hasSum_succ_geom hb0 hb1).mul_left _
  have hbnd : ∀ n : ℕ,
      ‖((n + (i+1) : ℕ) : ℝ) * (c (n + (i+1)) : ℝ) * x ^ ((n + (i+1)) - 1)‖
        ≤ ((i:ℝ) + 1) * b ^ i * (((n:ℝ) + 1) * b ^ n) := by
    intro n
    have hexp : (n + (i+1)) - 1 = n + i := by omega
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_nonneg hx0, hexp, Nat.abs_cast]
    have hxn : x ^ (n + i) ≤ b ^ (n + i) := pow_le_pow_left₀ hx0 hxb _
    have hcast : ((n + (i+1) : ℕ) : ℝ) = (n : ℝ) + (i : ℝ) + 1 := by push_cast; ring
    have h0 : (0:ℝ) ≤ (n : ℝ) + (i:ℝ) + 1 := by positivity
    have hx1 : (0:ℝ) ≤ x ^ (n+i) := pow_nonneg hx0 _
    have s2 : |(c (n + (i+1)) : ℝ)| * x ^ (n+i) ≤ 1 * b ^ (n+i) := by
      nlinarith [abs_nonneg ((c (n + (i+1)) : ℝ)), hc (n + (i+1))]
    calc ((n + (i+1) : ℕ) : ℝ) * |(c (n + (i+1)) : ℝ)| * x ^ (n + i)
        = ((n:ℝ) + (i:ℝ) + 1) * (|(c (n + (i+1)) : ℝ)| * x ^ (n+i)) := by rw [hcast]; ring
      _ ≤ ((n:ℝ) + (i:ℝ) + 1) * (1 * b ^ (n+i)) := mul_le_mul_of_nonneg_left s2 h0
      _ ≤ ((i:ℝ) + 1) * b ^ i * (((n:ℝ) + 1) * b ^ n) := by
          have hbpow : b ^ (n + i) = b ^ i * b ^ n := by rw [pow_add]; ring
          rw [hbpow]
          have hle : ((n:ℝ) + (i:ℝ) + 1) ≤ ((i:ℝ) + 1) * ((n:ℝ) + 1) := by
            nlinarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) i]
          have hbi : (0:ℝ) ≤ b ^ i := pow_nonneg hb0 _
          have hbn : (0:ℝ) ≤ b ^ n := pow_nonneg hb0 _
          nlinarith [mul_nonneg hbi hbn]
  have hkey := tsum_of_norm_bounded hgeo hbnd
  rw [hdiff]
  simpa [Real.norm_eq_abs] using hkey

/-! ### Variation of a truncation over a cell -/

lemma abs_pow_sub_pow_le {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hub : u ≤ b) (hvb : v ≤ b)
    (j : ℕ) : |u ^ j - v ^ j| ≤ (j : ℝ) * b ^ (j - 1) * |u - v| := by
  have hb0 : 0 ≤ b := le_trans hu hub
  induction j with
  | zero => simp
  | succ j ih =>
      have hstep : u ^ (j+1) - v ^ (j+1) = u * (u ^ j - v ^ j) + v ^ j * (u - v) := by ring
      have habs := abs_nonneg (u - v)
      have h1 : |u * (u ^ j - v ^ j)| ≤ b * ((j : ℝ) * b ^ (j - 1) * |u - v|) := by
        rw [abs_mul, abs_of_nonneg hu]
        have h2 : (0:ℝ) ≤ |u ^ j - v ^ j| := abs_nonneg _
        have h3 : (0:ℝ) ≤ (j : ℝ) * b ^ (j-1) * |u - v| := by positivity
        nlinarith
      have h4 : |v ^ j * (u - v)| ≤ b ^ j * |u - v| := by
        rw [abs_mul, abs_pow, abs_of_nonneg hv]
        have : v ^ j ≤ b ^ j := pow_le_pow_left₀ hv hvb j
        nlinarith [pow_nonneg hv j]
      have hpow : (j : ℝ) * (b * b ^ (j - 1)) ≤ (j : ℝ) * b ^ j := by
        rcases Nat.eq_zero_or_pos j with hj | hj
        · simp [hj]
        · have hjj : j - 1 + 1 = j := by omega
          have hbb : b * b ^ (j-1) = b ^ j := by rw [← pow_succ', hjj]
          rw [hbb]
      have hmul : (j : ℝ) * (b * b ^ (j-1)) * |u - v| ≤ (j : ℝ) * b ^ j * |u - v| :=
        mul_le_mul_of_nonneg_right hpow habs
      calc |u ^ (j+1) - v ^ (j+1)| = |u * (u ^ j - v ^ j) + v ^ j * (u - v)| := by rw [hstep]
        _ ≤ |u * (u ^ j - v ^ j)| + |v ^ j * (u - v)| := abs_add_le _ _
        _ ≤ b * ((j : ℝ) * b ^ (j - 1) * |u - v|) + b ^ j * |u - v| := by linarith
        _ = (j : ℝ) * (b * b ^ (j-1)) * |u - v| + b ^ j * |u - v| := by ring
        _ ≤ (j : ℝ) * b ^ j * |u - v| + b ^ j * |u - v| := by linarith
        _ = ((j : ℝ) + 1) * b ^ j * |u - v| := by ring
        _ = ((j+1 : ℕ) : ℝ) * b ^ ((j+1) - 1) * |u - v| := by push_cast; simp

/-- Centered form for the truncation: its variation over a cell is controlled
by `∑ j b^{j-1}` times the distance moved. -/
lemma var_le (hc : ∀ i, |(c i : ℝ)| ≤ 1) (hx0 : 0 ≤ x) (hxb : x ≤ b) (hm0 : 0 ≤ m) (hmb : m ≤ b)
    (i : ℕ) :
    |gpart c i m - gpart c i x| ≤ (∑ j ∈ range (i+1), (j : ℝ) * b ^ (j - 1)) * |m - x| := by
  rw [gpart, gpart, ← Finset.sum_sub_distrib, Finset.sum_mul]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
  intro j _
  have hpow := abs_pow_sub_pow_le (b := b) hm0 hx0 hmb hxb j
  have heq : (c j : ℝ) * m ^ j - (c j : ℝ) * x ^ j = (c j : ℝ) * (m ^ j - x ^ j) := by ring
  rw [heq, abs_mul]
  have h2 : (0:ℝ) ≤ |m ^ j - x ^ j| := abs_nonneg _
  have h3 : (0:ℝ) ≤ (j : ℝ) * b ^ (j-1) * |m - x| := by
    have : (0:ℝ) ≤ b := le_trans hx0 hxb
    positivity
  nlinarith [hc j, abs_nonneg ((c j : ℝ))]

/-- Centered form for the derivative of the truncation. -/
lemma dvar_le (hc : ∀ i, |(c i : ℝ)| ≤ 1) (hx0 : 0 ≤ x) (hxb : x ≤ b) (hm0 : 0 ≤ m) (hmb : m ≤ b)
    (i : ℕ) :
    |dpart c i m - dpart c i x|
      ≤ (∑ j ∈ range (i+1), ((j * (j-1) : ℕ) : ℝ) * b ^ (j - 2)) * |m - x| := by
  rw [dpart, dpart, ← Finset.sum_sub_distrib, Finset.sum_mul]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
  intro j _
  have hpow := abs_pow_sub_pow_le (b := b) hm0 hx0 hmb hxb (j - 1)
  have hexp : (j - 1) - 1 = j - 2 := by omega
  rw [hexp] at hpow
  have heq : (j : ℝ) * (c j : ℝ) * m ^ (j-1) - (j : ℝ) * (c j : ℝ) * x ^ (j-1)
      = (j : ℝ) * ((c j : ℝ) * (m ^ (j-1) - x ^ (j-1))) := by ring
  rw [heq, abs_mul, abs_mul, Nat.abs_cast]
  have hcast : ((j * (j-1) : ℕ) : ℝ) = (j : ℝ) * ((j - 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hcast]
  have h2 : (0:ℝ) ≤ |m ^ (j-1) - x ^ (j-1)| := abs_nonneg _
  have hb0 : (0:ℝ) ≤ b := le_trans hx0 hxb
  have h3 : (0:ℝ) ≤ ((j-1 : ℕ) : ℝ) * b ^ (j-2) * |m - x| := by positivity
  have hj : (0:ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have key : |(c j : ℝ)| * |m ^ (j-1) - x ^ (j-1)| ≤ ((j-1:ℕ) : ℝ) * b ^ (j-2) * |m - x| := by
    nlinarith [hc j, abs_nonneg ((c j : ℝ))]
  calc (j:ℝ) * (|(c j : ℝ)| * |m ^ (j-1) - x ^ (j-1)|)
      ≤ (j:ℝ) * (((j-1:ℕ) : ℝ) * b ^ (j-2) * |m - x|) := mul_le_mul_of_nonneg_left key hj
    _ = (j:ℝ) * ((j-1:ℕ) : ℝ) * b ^ (j-2) * |m - x| := by ring

end

end Transversality
end KnotGame
