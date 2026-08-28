import RequestProject.FourierGeneral
import RequestProject.Tribonacci

/-!
# T29c at the tribonacci constant: trace, distance bound, and the Fourier floor

The same programme as `RequestProject.PlasticFourier` and
`RequestProject.SupergoldenFourier`, run at the **tribonacci constant** `τ`,
the real root of `x³ = x² + x + 1` (`KnotGame.Tribonacci.lam`), again without
naming the two complex conjugates:

* the trace `A_m = τ^m + α^m + ᾱ^m` is the integer sequence `3, 1, 3`,
  `A_{m+3} = A_{m+2} + A_{m+1} + A_m` (`triTrace`), and the error
  `e_m = τ^m − A_m` satisfies `e_{m+2} = (1−τ) e_{m+1} − (τ²−τ−1) e_m`
  (`triErr_add_two`), the characteristic polynomial being the quadratic
  cofactor of `x³ − x² − x − 1`;
* the form `Q_m = e_{m+1}² − (1−τ) e_{m+1} e_m + (τ²−τ−1) e_m²` is positive
  definite (discriminant `−(3τ²−2τ−5) < 0`) and satisfies
  `Q_{m+1} = (τ²−τ−1) Q_m`, whence `e_m² ≤ 4 (τ²−τ−1)^m` (`triErr_sq_le`) with
  `τ²−τ−1 = τ^{-1} ≈ 0.54369` the squared modulus of the conjugates;
* no power of `τ` is a half-integer: for `m ≥ 5` the distance bound forbids it,
  and the exponents `0, …, 4` (together with the negative ones, where
  `τ^m ∈ (0,1)`) are settled by rational enclosures of `τ` in the kernel.

Everything downstream is the parameter-free argument of
`RequestProject.FourierGeneral`.
-/

namespace KnotGame
namespace Fourier

open Real Filter Topology
open scoped Real
open KnotGame.Tribonacci (lam lam_cube lam_gt lam_lt one_lt_lam)

set_option maxHeartbeats 1000000

/-! ## Rational enclosures of the tribonacci constant -/

lemma tri_pos : (0:ℝ) < lam := lt_trans zero_lt_one one_lt_lam

lemma tri_sq_lb : (33826/10^4 : ℝ) ≤ lam ^ 2 := by nlinarith [lam_gt, tri_pos]

lemma tri_sq_ub : lam ^ 2 ≤ (33831/10^4 : ℝ) := by nlinarith [lam_lt, tri_pos]

/-- The rate `t = τ² − τ − 1 = τ^{-1}`. -/
lemma tri_t_eq_inv : lam ^ 2 - lam - 1 = lam⁻¹ := by
  have hne : lam ≠ 0 := ne_of_gt tri_pos
  field_simp
  linear_combination lam_cube

lemma tri_t_pos : (0:ℝ) < lam ^ 2 - lam - 1 := by
  rw [tri_t_eq_inv]
  exact inv_pos.2 tri_pos

lemma tri_t_lb : (5433/10^4 : ℝ) ≤ lam ^ 2 - lam - 1 := by linarith [tri_sq_lb, lam_lt]

lemma tri_t_ub : lam ^ 2 - lam - 1 ≤ (5439/10^4 : ℝ) := by linarith [tri_sq_ub, lam_gt]

lemma tri_t_lt_one : lam ^ 2 - lam - 1 < 1 := by linarith [tri_t_ub]

/-! ## The integer trace and the error term -/

/-- The trace sequence `3, 1, 3, 7, 11, 21, 39, …` of the powers of the
tribonacci constant. -/
def triTrace : ℕ → ℤ
  | 0 => 3
  | 1 => 1
  | 2 => 3
  | (n + 3) => triTrace (n + 2) + triTrace (n + 1) + triTrace n

lemma triTrace_add_three (n : ℕ) :
    triTrace (n + 3) = triTrace (n + 2) + triTrace (n + 1) + triTrace n := rfl

/-- The error `e_m = τ^m − A_m`. -/
noncomputable def triErr (m : ℕ) : ℝ := lam ^ m - (triTrace m : ℝ)

lemma triErr_zero : triErr 0 = -2 := by norm_num [triErr, triTrace]

lemma triErr_one : triErr 1 = lam - 1 := by norm_num [triErr, triTrace]

lemma triErr_two : triErr 2 = lam ^ 2 - 3 := by norm_num [triErr, triTrace]

lemma tri_pow_add_three (m : ℕ) :
    lam ^ (m + 3) = lam ^ (m + 2) + lam ^ (m + 1) + lam ^ m := by
  have h : lam ^ 3 = lam ^ 2 + lam + 1 := lam_cube
  calc lam ^ (m + 3) = lam ^ m * lam ^ 3 := by ring
    _ = lam ^ m * (lam ^ 2 + lam + 1) := by rw [h]
    _ = lam ^ (m + 2) + lam ^ (m + 1) + lam ^ m := by ring

lemma triErr_add_three (m : ℕ) :
    triErr (m + 3) = triErr (m + 2) + triErr (m + 1) + triErr m := by
  simp only [triErr, triTrace_add_three, tri_pow_add_three m]
  push_cast
  ring

/-- The error satisfies the second-order recurrence whose characteristic
polynomial is the quadratic cofactor `x² − (1−τ)x + (τ²−τ−1)` of
`x³ − x² − x − 1`. -/
lemma triErr_add_two (m : ℕ) :
    triErr (m + 2) = (1 - lam) * triErr (m + 1) - (lam ^ 2 - lam - 1) * triErr m := by
  suffices h : ∀ m : ℕ,
      (triErr (m + 2) - (1 - lam) * triErr (m + 1) + (lam ^ 2 - lam - 1) * triErr m = 0) ∧
      (triErr (m + 3) - (1 - lam) * triErr (m + 2) + (lam ^ 2 - lam - 1) * triErr (m + 1) = 0) ∧
      (triErr (m + 4) - (1 - lam) * triErr (m + 3) + (lam ^ 2 - lam - 1) * triErr (m + 2) = 0) by
    have := (h m).1
    linarith
  intro m
  induction m with
  | zero =>
      have h3 : triErr 3 = triErr 2 + triErr 1 + triErr 0 := triErr_add_three 0
      have h4 : triErr 4 = triErr 3 + triErr 2 + triErr 1 := triErr_add_three 1
      have hc : lam ^ 3 = lam ^ 2 + lam + 1 := lam_cube
      refine ⟨?_, ?_, ?_⟩
      · rw [triErr_zero, triErr_one, triErr_two]; ring
      · rw [h3, triErr_zero, triErr_one, triErr_two]; linear_combination 2 * hc
      · rw [h4, h3, triErr_zero, triErr_one, triErr_two]; linear_combination (lam + 1) * hc
  | succ n ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      refine ⟨h2, h3, ?_⟩
      have e5 : triErr (n + 5) = triErr (n + 4) + triErr (n + 3) + triErr (n + 2) :=
        triErr_add_three (n + 2)
      have hc : lam ^ 3 = lam ^ 2 + lam + 1 := lam_cube
      simp only [show n + 1 + 4 = n + 5 from by omega, show n + 1 + 3 = n + 4 from by omega,
        show n + 1 + 2 = n + 3 from by omega]
      linear_combination e5 + lam * h3 - triErr (n + 2) * hc

/-! ## The invariant quadratic form -/

/-- The positive definite form
`Q_m = e_{m+1}² − (1−τ) e_{m+1} e_m + (τ²−τ−1) e_m²`. -/
noncomputable def triQ (m : ℕ) : ℝ :=
  triErr (m + 1) ^ 2 - (1 - lam) * triErr (m + 1) * triErr m
    + (lam ^ 2 - lam - 1) * triErr m ^ 2

lemma triQ_succ (m : ℕ) : triQ (m + 1) = (lam ^ 2 - lam - 1) * triQ m := by
  have h : triErr (m + 2) = (1 - lam) * triErr (m + 1) - (lam ^ 2 - lam - 1) * triErr m :=
    triErr_add_two m
  simp only [triQ]
  rw [show m + 1 + 1 = m + 2 from rfl, h]
  ring

lemma triQ_zero : triQ 0 = 3 * lam ^ 2 - 2 * lam - 5 := by
  have h1 : triErr (0 + 1) = lam - 1 := triErr_one
  simp only [triQ, triErr_zero, h1]
  ring

lemma triQ_eq (m : ℕ) :
    triQ m = (lam ^ 2 - lam - 1) ^ m * (3 * lam ^ 2 - 2 * lam - 5) := by
  induction m with
  | zero => simpa using triQ_zero
  | succ n ih => rw [triQ_succ n, ih]; ring

/-- **T29c(ii)** at the tribonacci constant: the distance from `τ^m` to the
integer `A_m` is at most `2 (τ²−τ−1)^{m/2}`, stated for the square. -/
theorem triErr_sq_le (m : ℕ) : triErr m ^ 2 ≤ 4 * (lam ^ 2 - lam - 1) ^ m := by
  have hkappa : (0:ℝ) < 3 * lam ^ 2 - 2 * lam - 5 := by nlinarith [tri_sq_lb, lam_lt]
  have hQ : triQ m = (lam ^ 2 - lam - 1) ^ m * (3 * lam ^ 2 - 2 * lam - 5) := triQ_eq m
  have hlow : (3 * lam ^ 2 - 2 * lam - 5) / 4 * triErr m ^ 2 ≤ triQ m := by
    have hsq : (0:ℝ) ≤ (triErr (m + 1) - (1 - lam) * triErr m / 2) ^ 2 := sq_nonneg _
    simp only [triQ]
    nlinarith [hsq]
  rw [hQ] at hlow
  have hpow : (0:ℝ) < (lam ^ 2 - lam - 1) ^ m := pow_pos tri_t_pos m
  nlinarith [hlow, hkappa, hpow]

/-! ## The approximation certificate -/

lemma tri_zpow_neg (k : ℕ) : lam ^ (-(k : ℤ)) = (lam ^ 2 - lam - 1) ^ k := by
  rw [zpow_neg, ← inv_zpow, zpow_natCast, ← tri_t_eq_inv]

lemma tri_t_sq_le : (lam ^ 2 - lam - 1) ^ 2 ≤ lam ^ 2 - lam - 1 := by
  nlinarith [tri_t_pos, tri_t_ub]

lemma tri_approx (m : ℤ) :
    ∃ n : ℤ, (lam ^ m - (n : ℝ)) ^ 2 ≤ 4 * (lam ^ 2 - lam - 1) ^ m.natAbs := by
  rcases le_or_gt 0 m with hm | hm
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    refine ⟨triTrace k, ?_⟩
    have hnat : ((k : ℤ)).natAbs = k := by omega
    rw [zpow_natCast, hnat]
    simpa [triErr] using triErr_sq_le k
  · refine ⟨0, ?_⟩
    obtain ⟨k, hk, hkabs⟩ : ∃ k : ℕ, m = -(k : ℤ) ∧ m.natAbs = k := ⟨m.natAbs, by omega, rfl⟩
    have hval : lam ^ m = (lam ^ 2 - lam - 1) ^ k := by rw [hk, tri_zpow_neg]
    rw [hkabs, hval, Int.cast_zero, sub_zero]
    have h1 : ((lam ^ 2 - lam - 1) ^ k) ^ 2 = ((lam ^ 2 - lam - 1) ^ 2) ^ k := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [h1]
    have h2 : ((lam ^ 2 - lam - 1) ^ 2) ^ k ≤ (lam ^ 2 - lam - 1) ^ k :=
      pow_le_pow_left₀ (by positivity) tri_t_sq_le k
    nlinarith [pow_pos tri_t_pos k, h2]

/-! ## No power of `τ` is a half-integer -/

lemma tri_pow_bounds (k : ℕ) :
    ((18392/10^4 : ℝ)) ^ k ≤ lam ^ k ∧ lam ^ k ≤ ((18393/10^4 : ℝ)) ^ k :=
  ⟨pow_le_pow_left₀ (by norm_num) (by linarith [lam_gt]) k,
    pow_le_pow_left₀ tri_pos.le (by linarith [lam_lt]) k⟩

lemma tri_t_bounds (k : ℕ) :
    ((5433/10^4 : ℝ)) ^ k ≤ (lam ^ 2 - lam - 1) ^ k ∧
      (lam ^ 2 - lam - 1) ^ k ≤ ((5439/10^4 : ℝ)) ^ k :=
  ⟨pow_le_pow_left₀ (by norm_num) tri_t_lb k, pow_le_pow_left₀ tri_t_pos.le tri_t_ub k⟩

/-- The five small exponents, by kernel arithmetic on rational enclosures. -/
lemma cos_pi_tri_pow_ne_zero_small {k : ℕ} (hk : k ≤ 4) : Real.cos (π * lam ^ k) ≠ 0 := by
  interval_cases k
  · have h0 : Real.cos (π * lam ^ (0:ℕ)) = -1 := by simp
    rw [h0]
    norm_num
  · exact cos_pi_ne_zero_of_between (j := 3)
      (by have := (tri_pow_bounds 1).1; norm_num at this ⊢; linarith)
      (by have := (tri_pow_bounds 1).2; norm_num at this ⊢; linarith)
  · exact cos_pi_ne_zero_of_between (j := 6)
      (by have := (tri_pow_bounds 2).1; norm_num at this ⊢; linarith)
      (by have := (tri_pow_bounds 2).2; norm_num at this ⊢; linarith)
  · exact cos_pi_ne_zero_of_between (j := 12)
      (by have := (tri_pow_bounds 3).1; norm_num at this ⊢; linarith)
      (by have := (tri_pow_bounds 3).2; norm_num at this ⊢; linarith)
  · exact cos_pi_ne_zero_of_between (j := 22)
      (by have := (tri_pow_bounds 4).1; norm_num at this ⊢; linarith)
      (by have := (tri_pow_bounds 4).2; norm_num at this ⊢; linarith)

/-- For `m ≥ 5` the distance bound alone forbids a half-integer. -/
lemma cos_pi_tri_pow_ne_zero_large {k : ℕ} (hk : 5 ≤ k) : Real.cos (π * lam ^ k) ≠ 0 := by
  intro hc
  obtain ⟨n, hn⟩ := (cos_pi_mul_eq_zero_iff (lam ^ k)).1 hc
  have hbig : (1:ℝ)/4 ≤ triErr k ^ 2 := by
    have he : triErr k = ((n - triTrace k : ℤ) : ℝ) + 1/2 := by
      rw [triErr, hn]; push_cast; ring
    have hcase : ((n - triTrace k : ℤ) : ℝ) + 1/2 ≤ -(1/2) ∨
        (1:ℝ)/2 ≤ ((n - triTrace k : ℤ) : ℝ) + 1/2 := by
      rcases le_or_gt (n - triTrace k) (-1) with h | h
      · left
        have : ((n - triTrace k : ℤ) : ℝ) ≤ -1 := by exact_mod_cast h
        linarith
      · right
        have h0 : (0:ℤ) ≤ n - triTrace k := by omega
        have : (0:ℝ) ≤ ((n - triTrace k : ℤ) : ℝ) := by exact_mod_cast h0
        linarith
    rcases hcase with h | h <;> rw [he] <;> nlinarith [h]
  have hsmall : triErr k ^ 2 ≤ 4 * (lam ^ 2 - lam - 1) ^ k := triErr_sq_le k
  have hmono : (lam ^ 2 - lam - 1) ^ k ≤ (lam ^ 2 - lam - 1) ^ 5 :=
    pow_le_pow_of_le_one tri_t_pos.le tri_t_lt_one.le hk
  have h5 : (lam ^ 2 - lam - 1) ^ 5 ≤ ((5439/10^4 : ℝ)) ^ 5 := (tri_t_bounds 5).2
  have hnum : (4:ℝ) * ((5439/10^4 : ℝ)) ^ 5 < 1/4 := by norm_num
  linarith [hbig, hsmall, hmono, h5]

lemma cos_pi_tri_pow_ne_zero_nat (k : ℕ) : Real.cos (π * lam ^ k) ≠ 0 := by
  rcases le_or_gt k 4 with h | h
  · exact cos_pi_tri_pow_ne_zero_small h
  · exact cos_pi_tri_pow_ne_zero_large (by omega)

lemma cos_pi_tri_zpow_neg_ne_zero (k : ℕ) (hk : 1 ≤ k) :
    Real.cos (π * lam ^ (-(k : ℤ))) ≠ 0 := by
  rw [tri_zpow_neg]
  rcases le_or_gt k 1 with h | h
  · interval_cases k
    refine cos_pi_ne_zero_of_between (j := 1) ?_ ?_
    · simp only [pow_one]; push_cast; linarith [tri_t_lb]
    · simp only [pow_one]; push_cast; linarith [tri_t_ub]
  · refine cos_pi_ne_zero_of_between (j := 0) ?_ ?_
    · push_cast
      have : (0:ℝ) < (lam ^ 2 - lam - 1) ^ k := pow_pos tri_t_pos k
      linarith
    · push_cast
      have hmono : (lam ^ 2 - lam - 1) ^ k ≤ (lam ^ 2 - lam - 1) ^ 2 :=
        pow_le_pow_of_le_one tri_t_pos.le tri_t_lt_one.le (by omega)
      have h2 := (tri_t_bounds 2).2
      norm_num at h2
      linarith

lemma cos_pi_tri_zpow_ne_zero (m : ℤ) : Real.cos (π * lam ^ m) ≠ 0 := by
  rcases le_or_gt 0 m with hm | hm
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    rw [zpow_natCast]
    exact cos_pi_tri_pow_ne_zero_nat k
  · have hk : m = -((m.natAbs : ℤ)) := by omega
    rw [hk]
    exact cos_pi_tri_zpow_neg_ne_zero m.natAbs (by omega)

/-! ## The certificate and the conclusions -/

/-- The tribonacci constant satisfies the hypotheses of the general argument,
with `C = 4` and rate `t = τ² − τ − 1 = τ^{-1}`. -/
noncomputable def tribonacciApprox : ConjApprox lam where
  C := 4
  t := lam ^ 2 - lam - 1
  hC := by norm_num
  ht0 := tri_t_pos
  ht1 := tri_t_lt_one
  approx := tri_approx
  nonzero := cos_pi_tri_zpow_ne_zero

/-- **T29c(iii)** at the tribonacci constant: the two-sided product converges … -/
theorem multipliable_tribonacciFac : Multipliable (cosFac lam) :=
  multipliable_cosFac tribonacciApprox

/-- … and its value is strictly positive. -/
theorem tribonacciFourierFloor_pos : 0 < ∏' m : ℤ, cosFac lam m :=
  tprod_cosFac_pos tribonacciApprox

/-- **T29c(iv)** at the tribonacci constant: the transform of the backward
system along `ξ_N = τ^N/(1−r)` converges to the tribonacci Fourier floor. -/
theorem tendsto_cosProd_xi_tribonacci :
    Tendsto (fun N : ℕ => cosProd (r lam) (xi lam N)) atTop (𝓝 (∏' m : ℤ, cosFac lam m)) :=
  tendsto_cosProd_xi_gen tribonacciApprox one_lt_lam

end Fourier
end KnotGame
