import RequestProject.FourierGeneral
import RequestProject.Supergolden

/-!
# T29c at the supergolden number: trace, distance bound, and the Fourier floor

The same programme as `RequestProject.PlasticFourier`, run at the **supergolden
ratio** `ψ`, the real root of `x³ = x² + 1` (`KnotGame.Supergolden.lam`).  As
there, the two complex conjugates are never named:

* the trace `A_m = ψ^m + α^m + ᾱ^m` is the integer sequence `3, 1, 1`,
  `A_{m+3} = A_{m+2} + A_m` (`sgTrace`), and the error `e_m = ψ^m − A_m`
  satisfies the second-order recurrence
  `e_{m+2} = (1−ψ) e_{m+1} − (ψ²−ψ) e_m` (`sgErr_add_two`), whose
  characteristic polynomial is the quadratic cofactor of `x³ − x² − 1`;
* the quadratic form `Q_m = e_{m+1}² − (1−ψ) e_{m+1} e_m + (ψ²−ψ) e_m²` is
  positive definite (its discriminant is `−(3ψ²−2ψ−1) < 0`) and satisfies
  `Q_{m+1} = (ψ²−ψ) Q_m`, whence `e_m² ≤ 4 (ψ²−ψ)^m` (`sgErr_sq_le`) with
  `ψ²−ψ = ψ^{-1} ≈ 0.68233` the squared modulus of the conjugates;
* no power of `ψ` is a half-integer: for `m ≥ 8` the distance bound forbids it,
  and the exponents `0, …, 7` (together with the negative ones, where
  `ψ^m ∈ (0,1)`) are settled by rational enclosures of `ψ` in the kernel.

Everything downstream is the parameter-free argument of
`RequestProject.FourierGeneral`.
-/

namespace KnotGame
namespace Fourier

open Real Filter Topology
open scoped Real
open KnotGame.Supergolden (lam lam_cube lam_gt lam_lt lam_sq_gt lam_sq_lt one_lt_lam)

set_option maxHeartbeats 1000000

/-! ## Rational enclosures of the supergolden ratio -/

lemma sg_pos : (0:ℝ) < lam := lt_trans zero_lt_one one_lt_lam

/-- The rate `t = ψ² − ψ = ψ^{-1}`. -/
lemma sg_t_eq_inv : lam ^ 2 - lam = lam⁻¹ := by
  have hne : lam ≠ 0 := ne_of_gt sg_pos
  field_simp
  linear_combination lam_cube

lemma sg_t_pos : (0:ℝ) < lam ^ 2 - lam := by
  rw [sg_t_eq_inv]
  exact inv_pos.2 sg_pos

lemma sg_t_lb : (6823276/10^7 : ℝ) ≤ lam ^ 2 - lam := by
  linarith [lam_sq_gt, lam_lt]

lemma sg_t_ub : lam ^ 2 - lam ≤ (6823282/10^7 : ℝ) := by
  linarith [lam_sq_lt, lam_gt]

lemma sg_t_lt_one : lam ^ 2 - lam < 1 := by linarith [sg_t_ub]

/-! ## The integer trace and the error term -/

/-- The trace sequence `3, 1, 1, 4, 5, 6, 10, 15, 21, …` of the powers of the
supergolden ratio. -/
def sgTrace : ℕ → ℤ
  | 0 => 3
  | 1 => 1
  | 2 => 1
  | (n + 3) => sgTrace (n + 2) + sgTrace n

lemma sgTrace_add_three (n : ℕ) : sgTrace (n + 3) = sgTrace (n + 2) + sgTrace n := rfl

/-- The error `e_m = ψ^m − A_m`. -/
noncomputable def sgErr (m : ℕ) : ℝ := lam ^ m - (sgTrace m : ℝ)

lemma sgErr_zero : sgErr 0 = -2 := by norm_num [sgErr, sgTrace]

lemma sgErr_one : sgErr 1 = lam - 1 := by norm_num [sgErr, sgTrace]

lemma sgErr_two : sgErr 2 = lam ^ 2 - 1 := by norm_num [sgErr, sgTrace]

lemma sg_pow_add_three (m : ℕ) : lam ^ (m + 3) = lam ^ (m + 2) + lam ^ m := by
  have h : lam ^ 3 = lam ^ 2 + 1 := lam_cube
  calc lam ^ (m + 3) = lam ^ m * lam ^ 3 := by ring
    _ = lam ^ m * (lam ^ 2 + 1) := by rw [h]
    _ = lam ^ (m + 2) + lam ^ m := by ring

lemma sgErr_add_three (m : ℕ) : sgErr (m + 3) = sgErr (m + 2) + sgErr m := by
  simp only [sgErr, sgTrace_add_three, sg_pow_add_three m]
  push_cast
  ring

/-- The error satisfies the second-order recurrence whose characteristic
polynomial is the quadratic cofactor `x² − (1−ψ)x + (ψ²−ψ)` of `x³ − x² − 1`. -/
lemma sgErr_add_two (m : ℕ) :
    sgErr (m + 2) = (1 - lam) * sgErr (m + 1) - (lam ^ 2 - lam) * sgErr m := by
  suffices h : ∀ m : ℕ,
      (sgErr (m + 2) - (1 - lam) * sgErr (m + 1) + (lam ^ 2 - lam) * sgErr m = 0) ∧
      (sgErr (m + 3) - (1 - lam) * sgErr (m + 2) + (lam ^ 2 - lam) * sgErr (m + 1) = 0) ∧
      (sgErr (m + 4) - (1 - lam) * sgErr (m + 3) + (lam ^ 2 - lam) * sgErr (m + 2) = 0) by
    have := (h m).1
    linarith
  intro m
  induction m with
  | zero =>
      have h3 : sgErr 3 = sgErr 2 + sgErr 0 := sgErr_add_three 0
      have h4 : sgErr 4 = sgErr 3 + sgErr 1 := sgErr_add_three 1
      have hc : lam ^ 3 = lam ^ 2 + 1 := lam_cube
      refine ⟨?_, ?_, ?_⟩
      · rw [sgErr_zero, sgErr_one, sgErr_two]; ring
      · rw [h3, sgErr_zero, sgErr_one, sgErr_two]; linear_combination 2 * hc
      · rw [h4, h3, sgErr_zero, sgErr_one, sgErr_two]; linear_combination (lam + 1) * hc
  | succ n ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      refine ⟨h2, h3, ?_⟩
      have e5 : sgErr (n + 5) = sgErr (n + 4) + sgErr (n + 2) := sgErr_add_three (n + 2)
      have hc : lam ^ 3 = lam ^ 2 + 1 := lam_cube
      simp only [show n + 1 + 4 = n + 5 from by omega, show n + 1 + 3 = n + 4 from by omega,
        show n + 1 + 2 = n + 3 from by omega]
      linear_combination e5 + lam * h3 - sgErr (n + 2) * hc

/-! ## The invariant quadratic form -/

/-- The positive definite form `Q_m = e_{m+1}² − (1−ψ) e_{m+1} e_m + (ψ²−ψ) e_m²`. -/
noncomputable def sgQ (m : ℕ) : ℝ :=
  sgErr (m + 1) ^ 2 - (1 - lam) * sgErr (m + 1) * sgErr m + (lam ^ 2 - lam) * sgErr m ^ 2

lemma sgQ_succ (m : ℕ) : sgQ (m + 1) = (lam ^ 2 - lam) * sgQ m := by
  have h : sgErr (m + 2) = (1 - lam) * sgErr (m + 1) - (lam ^ 2 - lam) * sgErr m :=
    sgErr_add_two m
  simp only [sgQ]
  rw [show m + 1 + 1 = m + 2 from rfl, h]
  ring

lemma sgQ_zero : sgQ 0 = 3 * lam ^ 2 - 2 * lam - 1 := by
  have h1 : sgErr (0 + 1) = lam - 1 := sgErr_one
  simp only [sgQ, sgErr_zero, h1]
  ring

lemma sgQ_eq (m : ℕ) : sgQ m = (lam ^ 2 - lam) ^ m * (3 * lam ^ 2 - 2 * lam - 1) := by
  induction m with
  | zero => simpa using sgQ_zero
  | succ n ih => rw [sgQ_succ n, ih]; ring

/-- **T29c(ii)** at the supergolden ratio: the distance from `ψ^m` to the
integer `A_m` is at most `2 (ψ²−ψ)^{m/2}`, stated for the square. -/
theorem sgErr_sq_le (m : ℕ) : sgErr m ^ 2 ≤ 4 * (lam ^ 2 - lam) ^ m := by
  have hkappa : (0:ℝ) < 3 * lam ^ 2 - 2 * lam - 1 := by nlinarith [lam_sq_gt, lam_lt]
  have hQ : sgQ m = (lam ^ 2 - lam) ^ m * (3 * lam ^ 2 - 2 * lam - 1) := sgQ_eq m
  have hlow : (3 * lam ^ 2 - 2 * lam - 1) / 4 * sgErr m ^ 2 ≤ sgQ m := by
    have hsq : (0:ℝ) ≤ (sgErr (m + 1) - (1 - lam) * sgErr m / 2) ^ 2 := sq_nonneg _
    simp only [sgQ]
    nlinarith [hsq]
  rw [hQ] at hlow
  have hpow : (0:ℝ) < (lam ^ 2 - lam) ^ m := pow_pos sg_t_pos m
  nlinarith [hlow, hkappa, hpow]

/-! ## The approximation certificate -/

lemma sg_zpow_neg (k : ℕ) : lam ^ (-(k : ℤ)) = (lam ^ 2 - lam) ^ k := by
  rw [zpow_neg, ← inv_zpow, zpow_natCast, ← sg_t_eq_inv]

lemma sg_t_sq_le : (lam ^ 2 - lam) ^ 2 ≤ lam ^ 2 - lam := by
  nlinarith [sg_t_pos, sg_t_ub]

lemma sg_approx (m : ℤ) :
    ∃ n : ℤ, (lam ^ m - (n : ℝ)) ^ 2 ≤ 4 * (lam ^ 2 - lam) ^ m.natAbs := by
  rcases le_or_gt 0 m with hm | hm
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    refine ⟨sgTrace k, ?_⟩
    have hnat : ((k : ℤ)).natAbs = k := by omega
    rw [zpow_natCast, hnat]
    simpa [sgErr] using sgErr_sq_le k
  · refine ⟨0, ?_⟩
    obtain ⟨k, hk, hkabs⟩ : ∃ k : ℕ, m = -(k : ℤ) ∧ m.natAbs = k := ⟨m.natAbs, by omega, rfl⟩
    have hval : lam ^ m = (lam ^ 2 - lam) ^ k := by rw [hk, sg_zpow_neg]
    rw [hkabs, hval, Int.cast_zero, sub_zero]
    have h1 : ((lam ^ 2 - lam) ^ k) ^ 2 = ((lam ^ 2 - lam) ^ 2) ^ k := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [h1]
    have h2 : ((lam ^ 2 - lam) ^ 2) ^ k ≤ (lam ^ 2 - lam) ^ k :=
      pow_le_pow_left₀ (by positivity) sg_t_sq_le k
    nlinarith [pow_pos sg_t_pos k, h2]

/-! ## No power of `ψ` is a half-integer -/

lemma sg_pow_bounds (k : ℕ) :
    ((14655712/10^7 : ℝ)) ^ k ≤ lam ^ k ∧ lam ^ k ≤ ((14655713/10^7 : ℝ)) ^ k :=
  ⟨pow_le_pow_left₀ (by norm_num) (by linarith [lam_gt]) k,
    pow_le_pow_left₀ sg_pos.le (by linarith [lam_lt]) k⟩

lemma sg_t_bounds (k : ℕ) :
    ((6823276/10^7 : ℝ)) ^ k ≤ (lam ^ 2 - lam) ^ k ∧
      (lam ^ 2 - lam) ^ k ≤ ((6823282/10^7 : ℝ)) ^ k :=
  ⟨pow_le_pow_left₀ (by norm_num) sg_t_lb k, pow_le_pow_left₀ sg_t_pos.le sg_t_ub k⟩

/-- The eight small exponents, by kernel arithmetic on rational enclosures. -/
lemma cos_pi_sg_pow_ne_zero_small {k : ℕ} (hk : k ≤ 7) : Real.cos (π * lam ^ k) ≠ 0 := by
  interval_cases k
  · have h0 : Real.cos (π * lam ^ (0:ℕ)) = -1 := by simp
    rw [h0]
    norm_num
  · exact cos_pi_ne_zero_of_between (j := 2)
      (by have := (sg_pow_bounds 1).1; norm_num at this ⊢; linarith)
      (by have := (sg_pow_bounds 1).2; norm_num at this ⊢; linarith)
  · exact cos_pi_ne_zero_of_between (j := 4)
      (by have := (sg_pow_bounds 2).1; norm_num at this ⊢; linarith)
      (by have := (sg_pow_bounds 2).2; norm_num at this ⊢; linarith)
  · exact cos_pi_ne_zero_of_between (j := 6)
      (by have := (sg_pow_bounds 3).1; norm_num at this ⊢; linarith)
      (by have := (sg_pow_bounds 3).2; norm_num at this ⊢; linarith)
  · exact cos_pi_ne_zero_of_between (j := 9)
      (by have := (sg_pow_bounds 4).1; norm_num at this ⊢; linarith)
      (by have := (sg_pow_bounds 4).2; norm_num at this ⊢; linarith)
  · exact cos_pi_ne_zero_of_between (j := 13)
      (by have := (sg_pow_bounds 5).1; norm_num at this ⊢; linarith)
      (by have := (sg_pow_bounds 5).2; norm_num at this ⊢; linarith)
  · exact cos_pi_ne_zero_of_between (j := 19)
      (by have := (sg_pow_bounds 6).1; norm_num at this ⊢; linarith)
      (by have := (sg_pow_bounds 6).2; norm_num at this ⊢; linarith)
  · exact cos_pi_ne_zero_of_between (j := 29)
      (by have := (sg_pow_bounds 7).1; norm_num at this ⊢; linarith)
      (by have := (sg_pow_bounds 7).2; norm_num at this ⊢; linarith)

/-- For `m ≥ 8` the distance bound alone forbids a half-integer. -/
lemma cos_pi_sg_pow_ne_zero_large {k : ℕ} (hk : 8 ≤ k) : Real.cos (π * lam ^ k) ≠ 0 := by
  intro hc
  obtain ⟨n, hn⟩ := (cos_pi_mul_eq_zero_iff (lam ^ k)).1 hc
  have hbig : (1:ℝ)/4 ≤ sgErr k ^ 2 := by
    have he : sgErr k = ((n - sgTrace k : ℤ) : ℝ) + 1/2 := by
      rw [sgErr, hn]; push_cast; ring
    have hcase : ((n - sgTrace k : ℤ) : ℝ) + 1/2 ≤ -(1/2) ∨
        (1:ℝ)/2 ≤ ((n - sgTrace k : ℤ) : ℝ) + 1/2 := by
      rcases le_or_gt (n - sgTrace k) (-1) with h | h
      · left
        have : ((n - sgTrace k : ℤ) : ℝ) ≤ -1 := by exact_mod_cast h
        linarith
      · right
        have h0 : (0:ℤ) ≤ n - sgTrace k := by omega
        have : (0:ℝ) ≤ ((n - sgTrace k : ℤ) : ℝ) := by exact_mod_cast h0
        linarith
    rcases hcase with h | h <;> rw [he] <;> nlinarith [h]
  have hsmall : sgErr k ^ 2 ≤ 4 * (lam ^ 2 - lam) ^ k := sgErr_sq_le k
  have hmono : (lam ^ 2 - lam) ^ k ≤ (lam ^ 2 - lam) ^ 8 :=
    pow_le_pow_of_le_one sg_t_pos.le sg_t_lt_one.le hk
  have h8 : (lam ^ 2 - lam) ^ 8 ≤ ((6823282/10^7 : ℝ)) ^ 8 := (sg_t_bounds 8).2
  have hnum : (4:ℝ) * ((6823282/10^7 : ℝ)) ^ 8 < 1/4 := by norm_num
  linarith [hbig, hsmall, hmono, h8]

lemma cos_pi_sg_pow_ne_zero_nat (k : ℕ) : Real.cos (π * lam ^ k) ≠ 0 := by
  rcases le_or_gt k 7 with h | h
  · exact cos_pi_sg_pow_ne_zero_small h
  · exact cos_pi_sg_pow_ne_zero_large (by omega)

lemma cos_pi_sg_zpow_neg_ne_zero (k : ℕ) (hk : 1 ≤ k) :
    Real.cos (π * lam ^ (-(k : ℤ))) ≠ 0 := by
  rw [sg_zpow_neg]
  rcases le_or_gt k 1 with h | h
  · interval_cases k
    refine cos_pi_ne_zero_of_between (j := 1) ?_ ?_
    · simp only [pow_one]; push_cast; linarith [sg_t_lb]
    · simp only [pow_one]; push_cast; linarith [sg_t_ub]
  · refine cos_pi_ne_zero_of_between (j := 0) ?_ ?_
    · push_cast
      have : (0:ℝ) < (lam ^ 2 - lam) ^ k := pow_pos sg_t_pos k
      linarith
    · push_cast
      have hmono : (lam ^ 2 - lam) ^ k ≤ (lam ^ 2 - lam) ^ 2 :=
        pow_le_pow_of_le_one sg_t_pos.le sg_t_lt_one.le (by omega)
      have h2 := (sg_t_bounds 2).2
      norm_num at h2
      linarith

lemma cos_pi_sg_zpow_ne_zero (m : ℤ) : Real.cos (π * lam ^ m) ≠ 0 := by
  rcases le_or_gt 0 m with hm | hm
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    rw [zpow_natCast]
    exact cos_pi_sg_pow_ne_zero_nat k
  · have hk : m = -((m.natAbs : ℤ)) := by omega
    rw [hk]
    exact cos_pi_sg_zpow_neg_ne_zero m.natAbs (by omega)

/-! ## The certificate and the conclusions -/

/-- The supergolden ratio satisfies the hypotheses of the general argument,
with `C = 4` and rate `t = ψ² − ψ = ψ^{-1}`. -/
noncomputable def supergoldenApprox : ConjApprox lam where
  C := 4
  t := lam ^ 2 - lam
  hC := by norm_num
  ht0 := sg_t_pos
  ht1 := sg_t_lt_one
  approx := sg_approx
  nonzero := cos_pi_sg_zpow_ne_zero

/-- **T29c(iii)** at the supergolden ratio: the two-sided product converges … -/
theorem multipliable_supergoldenFac : Multipliable (cosFac lam) :=
  multipliable_cosFac supergoldenApprox

/-- … and its value is strictly positive. -/
theorem supergoldenFourierFloor_pos : 0 < ∏' m : ℤ, cosFac lam m :=
  tprod_cosFac_pos supergoldenApprox

/-- **T29c(iv)** at the supergolden ratio: the transform of the backward system
along `ξ_N = ψ^N/(1−r)` converges to the supergolden Fourier floor. -/
theorem tendsto_cosProd_xi_supergolden :
    Tendsto (fun N : ℕ => cosProd (r lam) (xi lam N)) atTop (𝓝 (∏' m : ℤ, cosFac lam m)) :=
  tendsto_cosProd_xi_gen supergoldenApprox one_lt_lam

end Fourier
end KnotGame
