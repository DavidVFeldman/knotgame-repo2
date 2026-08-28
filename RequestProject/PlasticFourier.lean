import RequestProject.FourierGeneral
import RequestProject.Plastic

/-!
# T29c at the plastic number: trace, distance bound, and the Fourier floor

The commission's optional target T29c asks for the analogues of T29a(ii)–(iv)
at the plastic, supergolden and tribonacci parameters, "via their integer
trace recurrences".  This file carries that out at the **plastic number**
`ρ` (the real root of `x³ = x + 1`), and does so without ever naming the two
complex conjugates:

* **(ii)** the trace is the Perrin sequence `perrin` (`3, 0, 2`,
  `P_{m+3} = P_{m+1} + P_m`), and the error `e_m = ρ^m − P_m` satisfies the
  *second-order* recurrence `e_{m+2} = −ρ e_{m+1} − (ρ²−1) e_m`, whose
  characteristic polynomial is the quadratic cofactor of `x³ − x − 1`.  The
  positive definite quadratic form `Q_m = e_{m+1}² + ρ e_{m+1} e_m + (ρ²−1)e_m²`
  is multiplied by `ρ²−1` at each step, which yields the sharp bound
  `e_m² ≤ 4 (ρ²−1)^m` (`perr_sq_le`) — the analogue of `‖φ^m‖ ≤ φ^{-m}`, with
  `ρ²−1 = ρ^{-1} ≈ 0.7549` playing the role of the squared conjugate modulus.
* **(iii)** hence `∏_{m ∈ ℤ}|cos(π ρ^m)|` converges to a positive limit
  (`plasticFourierFloor_pos`).  Positivity of the individual factors is the
  one place where a finite computation enters: for `m ≥ 10` the distance bound
  already forbids `ρ^m ∈ ℤ + 1/2`, and the ten remaining exponents (and the
  negative ones, where `ρ^m ∈ (0,1)`) are settled by rational enclosures of
  `ρ` in the kernel.
* **(iv)** the transform along `ξ_N` converges to that product
  (`tendsto_cosProd_xi_plastic`).

Everything downstream of the two inputs is the general argument of
`RequestProject.FourierGeneral`; nothing of the golden case is re-derived.

The supergolden and tribonacci analogues follow the same skeleton and live in
`RequestProject.SupergoldenFourier` and `RequestProject.TribonacciFourier`.
-/

namespace KnotGame
namespace Fourier

open Real Filter Topology
open scoped Real
open KnotGame.Plastic

set_option maxHeartbeats 1000000

/-! ## Rational enclosures of the plastic number -/

lemma rho_pos : (0:ℝ) < rho := lt_trans zero_lt_one one_lt_rho

lemma rho_lb : (13247179/10^7 : ℝ) ≤ rho := by
  have key : (rho - 13247179/10^7) * (rho ^ 2 + (13247179/10^7) * rho +
      (13247179/10^7) ^ 2 - 1) = 1 + 13247179/10^7 - (13247179/10^7) ^ 3 := by
    linear_combination rho_cubic
  have hfac : (0:ℝ) < rho ^ 2 + (13247179/10^7) * rho + (13247179/10^7) ^ 2 - 1 := by
    nlinarith [rho_gt]
  nlinarith [key, hfac]

lemma rho_ub : rho ≤ (13247180/10^7 : ℝ) := by
  have key : (rho - 13247180/10^7) * (rho ^ 2 + (13247180/10^7) * rho +
      (13247180/10^7) ^ 2 - 1) = 1 + 13247180/10^7 - (13247180/10^7) ^ 3 := by
    linear_combination rho_cubic
  have hfac : (0:ℝ) < rho ^ 2 + (13247180/10^7) * rho + (13247180/10^7) ^ 2 - 1 := by
    nlinarith [rho_gt]
  nlinarith [key, hfac]

/-- `ρ² − 1 = ρ^{-1}`: the conjugates have squared modulus `ρ²−1`. -/
lemma rho_sq_sub_one_eq_inv : rho ^ 2 - 1 = rho⁻¹ := by
  have hne : rho ≠ 0 := ne_of_gt rho_pos
  field_simp
  linear_combination rho_cubic

lemma rho_sq_sub_one_pos : (0:ℝ) < rho ^ 2 - 1 := by
  rw [rho_sq_sub_one_eq_inv]
  exact inv_pos.2 rho_pos

lemma rho_sq_sub_one_lt_one : rho ^ 2 - 1 < 1 := by
  nlinarith [rho_lb, rho_ub]

/-! ## The Perrin trace and the error term -/

/-- The Perrin sequence `3, 0, 2, 3, 2, 5, 5, 7, 10, 12, …`, the trace of the
powers of the plastic number. -/
def perrin : ℕ → ℤ
  | 0 => 3
  | 1 => 0
  | 2 => 2
  | (n + 3) => perrin (n + 1) + perrin n

lemma perrin_add_three (n : ℕ) : perrin (n + 3) = perrin (n + 1) + perrin n := rfl

/-- The error `e_m = ρ^m − P_m`. -/
noncomputable def perr (m : ℕ) : ℝ := rho ^ m - (perrin m : ℝ)

lemma perr_zero : perr 0 = -2 := by norm_num [perr, perrin]

lemma perr_one : perr 1 = rho := by norm_num [perr, perrin]

lemma perr_two : perr 2 = rho ^ 2 - 2 := by norm_num [perr, perrin]

lemma rho_pow_add_three (m : ℕ) : rho ^ (m + 3) = rho ^ (m + 1) + rho ^ m := by
  have h : rho ^ 3 = rho + 1 := by linarith [rho_cubic]
  calc rho ^ (m + 3) = rho ^ m * rho ^ 3 := by ring
    _ = rho ^ m * (rho + 1) := by rw [h]
    _ = rho ^ (m + 1) + rho ^ m := by ring

lemma perr_add_three (m : ℕ) : perr (m + 3) = perr (m + 1) + perr m := by
  simp only [perr, perrin_add_three, rho_pow_add_three m]
  push_cast
  ring

/-- The error satisfies the second-order recurrence whose characteristic
polynomial is the quadratic cofactor `x² + ρx + (ρ²−1)` of `x³ − x − 1`. -/
lemma perr_add_two (m : ℕ) :
    perr (m + 2) = -rho * perr (m + 1) - (rho ^ 2 - 1) * perr m := by
  suffices h : ∀ m : ℕ, (perr (m + 2) + rho * perr (m + 1) + (rho ^ 2 - 1) * perr m = 0) ∧
      (perr (m + 3) + rho * perr (m + 2) + (rho ^ 2 - 1) * perr (m + 1) = 0) ∧
      (perr (m + 4) + rho * perr (m + 3) + (rho ^ 2 - 1) * perr (m + 2) = 0) by
    have := (h m).1
    linarith
  intro m
  induction m with
  | zero =>
      have h3 : perr 3 = perr 1 + perr 0 := perr_add_three 0
      have h4 : perr 4 = perr 2 + perr 1 := perr_add_three 1
      have hc := rho_cubic
      refine ⟨?_, ?_, ?_⟩
      · rw [perr_zero, perr_one, perr_two]; ring
      · rw [h3, perr_zero, perr_one, perr_two]; linear_combination 2 * hc
      · rw [h4, h3, perr_zero, perr_one, perr_two]; linear_combination rho * hc
  | succ n ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      refine ⟨h2, h3, ?_⟩
      have e5 : perr (n + 5) = perr (n + 3) + perr (n + 2) := perr_add_three (n + 2)
      have e4 : perr (n + 4) = perr (n + 2) + perr (n + 1) := perr_add_three (n + 1)
      have e3 : perr (n + 3) = perr (n + 1) + perr n := perr_add_three n
      have : n + 1 + 4 = n + 5 := by omega
      rw [this]
      rw [e5, e4, e3]
      linarith [h1, h2, e3]

/-! ## The invariant quadratic form -/

/-- The positive definite form `Q_m = e_{m+1}² + ρ e_{m+1} e_m + (ρ²−1) e_m²`. -/
noncomputable def pQ (m : ℕ) : ℝ :=
  perr (m + 1) ^ 2 + rho * perr (m + 1) * perr m + (rho ^ 2 - 1) * perr m ^ 2

lemma pQ_succ (m : ℕ) : pQ (m + 1) = (rho ^ 2 - 1) * pQ m := by
  have h : perr (m + 2) = -rho * perr (m + 1) - (rho ^ 2 - 1) * perr m := perr_add_two m
  simp only [pQ]
  rw [show m + 1 + 1 = m + 2 from rfl, h]
  ring

lemma pQ_zero : pQ 0 = 3 * rho ^ 2 - 4 := by
  have h1 : perr (0 + 1) = rho := perr_one
  simp only [pQ, perr_zero, h1]
  ring

lemma pQ_eq (m : ℕ) : pQ m = (rho ^ 2 - 1) ^ m * (3 * rho ^ 2 - 4) := by
  induction m with
  | zero => simpa using pQ_zero
  | succ n ih => rw [pQ_succ n, ih]; ring

/-- **T29c(ii)**: the distance from `ρ^m` to the integer `P_m` is at most
`2 (ρ²−1)^{m/2}`, stated for the square so that no root is needed. -/
theorem perr_sq_le (m : ℕ) : perr m ^ 2 ≤ 4 * (rho ^ 2 - 1) ^ m := by
  have hkappa : (0:ℝ) < 3 * rho ^ 2 - 4 := by nlinarith [rho_lb, rho_ub]
  have hQ : pQ m = (rho ^ 2 - 1) ^ m * (3 * rho ^ 2 - 4) := pQ_eq m
  have hlow : (3 * rho ^ 2 - 4) / 4 * perr m ^ 2 ≤ pQ m := by
    have hsq : (0:ℝ) ≤ (perr (m + 1) + rho * perr m / 2) ^ 2 := sq_nonneg _
    simp only [pQ]
    nlinarith [hsq]
  rw [hQ] at hlow
  have hpow : (0:ℝ) < (rho ^ 2 - 1) ^ m := pow_pos rho_sq_sub_one_pos m
  nlinarith [hlow, hkappa, hpow]

/-! ## The approximation certificate -/

lemma rho_zpow_neg (k : ℕ) : rho ^ (-(k : ℤ)) = (rho ^ 2 - 1) ^ k := by
  rw [zpow_neg, ← inv_zpow, zpow_natCast, ← rho_sq_sub_one_eq_inv]

/-- `ρ^{-2} ≤ ρ² − 1`, since `ρ⁴ − ρ² = ρ > 1`. -/
lemma rho_inv_sq_le : (rho ^ 2 - 1) ^ 2 ≤ rho ^ 2 - 1 := by
  have h2 : rho ^ 2 ≤ 2 := by nlinarith [rho_ub, rho_pos]
  nlinarith [rho_sq_sub_one_pos, h2]

lemma plastic_approx (m : ℤ) :
    ∃ n : ℤ, (rho ^ m - (n : ℝ)) ^ 2 ≤ 4 * (rho ^ 2 - 1) ^ m.natAbs := by
  rcases le_or_gt 0 m with hm | hm
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    refine ⟨perrin k, ?_⟩
    have hnat : ((k : ℤ)).natAbs = k := by omega
    rw [zpow_natCast, hnat]
    simpa [perr] using perr_sq_le k
  · refine ⟨0, ?_⟩
    obtain ⟨k, hk, hkabs⟩ : ∃ k : ℕ, m = -(k : ℤ) ∧ m.natAbs = k := ⟨m.natAbs, by omega, rfl⟩
    have hval : rho ^ m = (rho ^ 2 - 1) ^ k := by rw [hk, rho_zpow_neg]
    rw [hkabs, hval, Int.cast_zero, sub_zero]
    have h1 : ((rho ^ 2 - 1) ^ k) ^ 2 = ((rho ^ 2 - 1) ^ 2) ^ k := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [h1]
    have h2 : ((rho ^ 2 - 1) ^ 2) ^ k ≤ (rho ^ 2 - 1) ^ k :=
      pow_le_pow_left₀ (by positivity) rho_inv_sq_le k
    nlinarith [pow_pos rho_sq_sub_one_pos k, h2]

/-! ## No power of `ρ` is a half-integer -/

lemma rho_pow_bounds (k : ℕ) :
    ((13247179/10^7 : ℝ)) ^ k ≤ rho ^ k ∧ rho ^ k ≤ ((13247180/10^7 : ℝ)) ^ k :=
  ⟨pow_le_pow_left₀ (by norm_num) rho_lb k, pow_le_pow_left₀ rho_pos.le rho_ub k⟩

lemma c_lb : (7548775/10^7 : ℝ) ≤ rho ^ 2 - 1 := by nlinarith [rho_lb, rho_pos]

lemma c_ub : rho ^ 2 - 1 ≤ (7548778/10^7 : ℝ) := by nlinarith [rho_ub, rho_pos]

lemma c_bounds (k : ℕ) :
    ((7548775/10^7 : ℝ)) ^ k ≤ (rho ^ 2 - 1) ^ k ∧
      (rho ^ 2 - 1) ^ k ≤ ((7548778/10^7 : ℝ)) ^ k :=
  ⟨pow_le_pow_left₀ (by norm_num) c_lb k, pow_le_pow_left₀ rho_sq_sub_one_pos.le c_ub k⟩

/-- The ten small exponents, by kernel arithmetic on rational enclosures. -/
lemma cos_pi_rho_pow_ne_zero_small {k : ℕ} (hk : k ≤ 9) : Real.cos (π * rho ^ k) ≠ 0 := by
  interval_cases k
  · have h0 : Real.cos (π * rho ^ (0:ℕ)) = -1 := by simp
    rw [h0]
    norm_num
  · exact cos_pi_ne_zero_of_between (j := 2)
      (by have := (rho_pow_bounds 1).1; norm_num at this ⊢; linarith)
      (by have := (rho_pow_bounds 1).2; norm_num at this ⊢; linarith)
  · exact cos_pi_ne_zero_of_between (j := 3)
      (by have := (rho_pow_bounds 2).1; norm_num at this ⊢; linarith)
      (by have := (rho_pow_bounds 2).2; norm_num at this ⊢; linarith)
  · exact cos_pi_ne_zero_of_between (j := 4)
      (by have := (rho_pow_bounds 3).1; norm_num at this ⊢; linarith)
      (by have := (rho_pow_bounds 3).2; norm_num at this ⊢; linarith)
  · exact cos_pi_ne_zero_of_between (j := 6)
      (by have := (rho_pow_bounds 4).1; norm_num at this ⊢; linarith)
      (by have := (rho_pow_bounds 4).2; norm_num at this ⊢; linarith)
  · exact cos_pi_ne_zero_of_between (j := 8)
      (by have := (rho_pow_bounds 5).1; norm_num at this ⊢; linarith)
      (by have := (rho_pow_bounds 5).2; norm_num at this ⊢; linarith)
  · exact cos_pi_ne_zero_of_between (j := 10)
      (by have := (rho_pow_bounds 6).1; norm_num at this ⊢; linarith)
      (by have := (rho_pow_bounds 6).2; norm_num at this ⊢; linarith)
  · exact cos_pi_ne_zero_of_between (j := 14)
      (by have := (rho_pow_bounds 7).1; norm_num at this ⊢; linarith)
      (by have := (rho_pow_bounds 7).2; norm_num at this ⊢; linarith)
  · exact cos_pi_ne_zero_of_between (j := 18)
      (by have := (rho_pow_bounds 8).1; norm_num at this ⊢; linarith)
      (by have := (rho_pow_bounds 8).2; norm_num at this ⊢; linarith)
  · exact cos_pi_ne_zero_of_between (j := 25)
      (by have := (rho_pow_bounds 9).1; norm_num at this ⊢; linarith)
      (by have := (rho_pow_bounds 9).2; norm_num at this ⊢; linarith)

/-- For `m ≥ 10` the distance bound alone forbids a half-integer. -/
lemma cos_pi_rho_pow_ne_zero_large {k : ℕ} (hk : 10 ≤ k) : Real.cos (π * rho ^ k) ≠ 0 := by
  intro hc
  obtain ⟨n, hn⟩ := (cos_pi_mul_eq_zero_iff (rho ^ k)).1 hc
  have hbig : (1:ℝ)/4 ≤ perr k ^ 2 := by
    have he : perr k = ((n - perrin k : ℤ) : ℝ) + 1/2 := by
      rw [perr, hn]; push_cast; ring
    have : ((n - perrin k : ℤ) : ℝ) + 1/2 ≤ -(1/2) ∨ (1:ℝ)/2 ≤ ((n - perrin k : ℤ) : ℝ) + 1/2 := by
      rcases le_or_gt (n - perrin k) (-1) with h | h
      · left
        have : ((n - perrin k : ℤ) : ℝ) ≤ -1 := by exact_mod_cast h
        linarith
      · right
        have : (0:ℤ) ≤ n - perrin k := by omega
        have : (0:ℝ) ≤ ((n - perrin k : ℤ) : ℝ) := by exact_mod_cast this
        linarith
    rcases this with h | h <;> rw [he] <;> nlinarith [h]
  have hsmall : perr k ^ 2 ≤ 4 * (rho ^ 2 - 1) ^ k := perr_sq_le k
  have hmono : (rho ^ 2 - 1) ^ k ≤ (rho ^ 2 - 1) ^ 10 :=
    pow_le_pow_of_le_one rho_sq_sub_one_pos.le rho_sq_sub_one_lt_one.le hk
  have h10 : (rho ^ 2 - 1) ^ 10 ≤ ((7548778/10^7 : ℝ)) ^ 10 := (c_bounds 10).2
  have : (4:ℝ) * ((7548778/10^7 : ℝ)) ^ 10 < 1/4 := by norm_num
  linarith [hbig, hsmall, hmono, h10]

lemma cos_pi_rho_pow_ne_zero_nat (k : ℕ) : Real.cos (π * rho ^ k) ≠ 0 := by
  rcases le_or_gt k 9 with h | h
  · exact cos_pi_rho_pow_ne_zero_small h
  · exact cos_pi_rho_pow_ne_zero_large (by omega)

lemma cos_pi_rho_zpow_neg_ne_zero (k : ℕ) (hk : 1 ≤ k) :
    Real.cos (π * rho ^ (-(k : ℤ))) ≠ 0 := by
  rw [rho_zpow_neg]
  rcases le_or_gt k 2 with h | h
  · interval_cases k
    · refine cos_pi_ne_zero_of_between (j := 1) ?_ ?_
      · simp only [pow_one]; push_cast; linarith [c_lb]
      · simp only [pow_one]; push_cast; linarith [c_ub]
    · refine cos_pi_ne_zero_of_between (j := 1) ?_ ?_
      · push_cast; nlinarith [c_lb, c_ub, rho_sq_sub_one_pos]
      · push_cast; nlinarith [c_lb, c_ub, rho_sq_sub_one_pos]
  · refine cos_pi_ne_zero_of_between (j := 0) ?_ ?_
    · push_cast
      have : (0:ℝ) < (rho ^ 2 - 1) ^ k := pow_pos rho_sq_sub_one_pos k
      linarith
    · push_cast
      have hmono : (rho ^ 2 - 1) ^ k ≤ (rho ^ 2 - 1) ^ 3 :=
        pow_le_pow_of_le_one rho_sq_sub_one_pos.le rho_sq_sub_one_lt_one.le (by omega)
      have h3 := (c_bounds 3).2
      norm_num at h3
      linarith

lemma cos_pi_rho_zpow_ne_zero (m : ℤ) : Real.cos (π * rho ^ m) ≠ 0 := by
  rcases le_or_gt 0 m with hm | hm
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    rw [zpow_natCast]
    exact cos_pi_rho_pow_ne_zero_nat k
  · have hk : m = -((m.natAbs : ℤ)) := by omega
    rw [hk]
    exact cos_pi_rho_zpow_neg_ne_zero m.natAbs (by omega)

/-! ## The certificate and the conclusions -/

/-- The plastic number satisfies the hypotheses of the general argument, with
`C = 4` and rate `t = ρ² − 1 = ρ^{-1}`. -/
noncomputable def plasticApprox : ConjApprox rho where
  C := 4
  t := rho ^ 2 - 1
  hC := by norm_num
  ht0 := rho_sq_sub_one_pos
  ht1 := rho_sq_sub_one_lt_one
  approx := plastic_approx
  nonzero := cos_pi_rho_zpow_ne_zero

/-- **T29c(iii)** at the plastic number: the two-sided product converges … -/
theorem multipliable_plasticFac : Multipliable (cosFac rho) :=
  multipliable_cosFac plasticApprox

/-- … and its value is strictly positive. -/
theorem plasticFourierFloor_pos : 0 < ∏' m : ℤ, cosFac rho m :=
  tprod_cosFac_pos plasticApprox

/-- **T29c(iv)** at the plastic number: the transform of the backward system
along `ξ_N = ρ^N/(1−r)` converges to the plastic Fourier floor. -/
theorem tendsto_cosProd_xi_plastic :
    Tendsto (fun N : ℕ => cosProd (r rho) (xi rho N)) atTop (𝓝 (∏' m : ℤ, cosFac rho m)) :=
  tendsto_cosProd_xi_gen plasticApprox one_lt_rho

end Fourier
end KnotGame
