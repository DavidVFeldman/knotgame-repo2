import Mathlib

/-!
# T29a(ii) — Lucas numbers and the distance from `φ^m` to the integers

The paper's Section `sec:conjugate` uses, at the golden ratio, that
`‖φ^m‖ → 0` geometrically, with rate the modulus `c(φ) = φ - 1 = φ⁻¹` of the
conjugate.  The mechanism is the trace identity: with `L_m` the Lucas numbers,

  `φ^m + ψ^m = L_m`,   `ψ = 1 - φ = -φ⁻¹`,

so that `φ^m` differs from the integer `L_m` by exactly `φ^{-m}`.

This file records that identity, the resulting distance bound, and — for the
non-vanishing of the cosine factors in `FourierFloor.lean` — the irrationality
of every positive power of `φ`.

## Conventions (SCRUPLES)

* `lucas` is defined here by its own recursion (`L₀ = 2`, `L₁ = 1`,
  `L_{n+2} = L_n + L_{n+1}`); Mathlib has `Nat.fib` but no Lucas sequence.
* The distance bound is stated in the sharp form
  `|φ^m - L_m| = (φ⁻¹)^m`, an equality, from which
  `|φ^m - round (φ^m)| ≤ (φ⁻¹)^m` follows for the nearest integer.  The paper
  states it for `m ≥ 2`; the identity above in fact holds for every `m ≥ 0`.
-/

namespace KnotGame
namespace Fourier

open Real

/-- The Lucas numbers `2, 1, 3, 4, 7, 11, …`. -/
def lucas : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | (n + 2) => lucas n + lucas (n + 1)

@[simp] lemma lucas_zero : lucas 0 = 2 := rfl
@[simp] lemma lucas_one : lucas 1 = 1 := rfl
lemma lucas_add_two (n : ℕ) : lucas (n + 2) = lucas n + lucas (n + 1) := rfl

/-- A root of `x² = x + 1` satisfies the Fibonacci recursion on its powers. -/
private lemma pow_step {x : ℝ} (hx : x ^ 2 = x + 1) (m : ℕ) :
    x ^ (m + 2) = x ^ (m + 1) + x ^ m := by
  calc x ^ (m + 2) = x ^ m * x ^ 2 := by ring
    _ = x ^ m * (x + 1) := by rw [hx]
    _ = x ^ (m + 1) + x ^ m := by ring

/-- **The trace identity**: `φ^m + ψ^m = L_m`. -/
theorem goldenRatio_pow_add_goldenConj_pow : ∀ m : ℕ,
    Real.goldenRatio ^ m + Real.goldenConj ^ m = (lucas m : ℝ)
  | 0 => by norm_num
  | 1 => by simp
  | (m + 2) => by
      have h1 := goldenRatio_pow_add_goldenConj_pow m
      have h2 := goldenRatio_pow_add_goldenConj_pow (m + 1)
      rw [pow_step Real.goldenRatio_sq m, pow_step Real.goldenConj_sq m, lucas_add_two]
      push_cast
      linarith

lemma abs_goldenConj : |Real.goldenConj| = Real.goldenRatio⁻¹ := by
  rw [Real.inv_goldenRatio, abs_of_neg Real.goldenConj_neg]

lemma goldenRatio_inv_pos : 0 < Real.goldenRatio⁻¹ := by
  simpa using Real.goldenRatio_pos

lemma goldenRatio_inv_lt_one : Real.goldenRatio⁻¹ < 1 := by
  rw [inv_lt_one_iff₀]
  exact Or.inr Real.one_lt_goldenRatio

/-- **T29a(ii)**: `φ^m` differs from the Lucas number `L_m` by exactly
`φ^{-m}`. -/
theorem abs_goldenRatio_pow_sub_lucas (m : ℕ) :
    |Real.goldenRatio ^ m - (lucas m : ℝ)| = (Real.goldenRatio⁻¹) ^ m := by
  have h := goldenRatio_pow_add_goldenConj_pow m
  have hrw : Real.goldenRatio ^ m - (lucas m : ℝ) = -(Real.goldenConj ^ m) := by linarith
  rw [hrw, abs_neg, abs_pow, abs_goldenConj]

/-- **T29a(ii)**, in the form the paper states it: the distance from `φ^m` to
the nearest integer is at most `φ^{-m}`. -/
theorem abs_goldenRatio_pow_sub_round_le (m : ℕ) :
    |Real.goldenRatio ^ m - round (Real.goldenRatio ^ m)| ≤ (Real.goldenRatio⁻¹) ^ m := by
  rw [← abs_goldenRatio_pow_sub_lucas m]
  exact round_le (Real.goldenRatio ^ m) (lucas m)

/-! ### Irrationality of the positive powers -/

/-- Every positive power of `φ` is irrational. -/
theorem irrational_goldenRatio_pow_succ (n : ℕ) :
    Irrational (Real.goldenRatio ^ (n + 1)) := by
  have h := Real.goldenRatio_mul_fib_succ_add_fib n
  rw [← h]
  have hne : Nat.fib (n + 1) ≠ 0 := (Nat.fib_pos.mpr (Nat.succ_pos n)).ne'
  exact (Real.goldenRatio_irrational.mul_natCast hne).add_natCast _

end Fourier
end KnotGame
