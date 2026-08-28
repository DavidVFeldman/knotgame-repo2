import RequestProject.FourierFloor

/-!
# The Fourier floor for a general geometrically integral parameter (round 9)

`RequestProject.FourierFloor` proves, at `λ = φ`, that the two-sided product
`∏_{m ∈ ℤ}|cos(π λ^m)|` converges to a positive limit and that it is the limit
of the transform along the frequencies `ξ_N`.  Only two features of `φ` are
used:

* its powers approach the integers geometrically — for `φ` this is the Lucas
  trace identity for `m ≥ 0` and `φ^m → 0` for `m < 0`;
* no power of `φ` is a half-integer, so no factor vanishes.

This file isolates those two inputs into the structure `ConjApprox` and
re-proves the conclusions from them alone, so that the argument can be
instantiated at other parameters (T29c).  Nothing here re-derives the golden
case, which stays in `FourierFloor`.

The approximation hypothesis is stated for the **square** of the distance,
`(λ^m − n)^2 ≤ C t^{|m|}`, which is the form the deficit bound
`1 − |cos(π d)| ≤ π² d²/2` consumes; this avoids square roots at the point of
use (at the plastic number the natural constant is `t = ρ² − 1`, the squared
modulus of the complex conjugates).
-/

namespace KnotGame
namespace Fourier

open Real Filter Topology
open scoped Real

set_option maxHeartbeats 1000000

/-- Certificate that the powers of `lam` approach the integers geometrically
(with squared distance at most `C t^{|m|}`) and that no factor
`|cos(π lam^m)|` vanishes. -/
structure ConjApprox (lam : ℝ) where
  /-- The multiplicative constant in the distance bound. -/
  C : ℝ
  /-- The geometric rate of the distance bound (for the *squared* distance). -/
  t : ℝ
  hC : 0 ≤ C
  ht0 : 0 < t
  ht1 : t < 1
  /-- `λ^m` is within `√(C t^{|m|})` of an integer. -/
  approx : ∀ m : ℤ, ∃ n : ℤ, (lam ^ m - (n : ℝ)) ^ 2 ≤ C * t ^ m.natAbs
  /-- No power of `λ` is a half-integer. -/
  nonzero : ∀ m : ℤ, Real.cos (π * lam ^ m) ≠ 0

variable {lam : ℝ}

lemma cosFac_le_one (lam : ℝ) (m : ℤ) : cosFac lam m ≤ 1 := by
  simpa [cosFac] using Real.abs_cos_le_one (π * lam ^ m)

lemma cosFac_nonneg (lam : ℝ) (m : ℤ) : 0 ≤ cosFac lam m := abs_nonneg _

lemma cosFac_pos (d : ConjApprox lam) (m : ℤ) : 0 < cosFac lam m :=
  abs_pos.2 (d.nonzero m)

/-- A convenient way to certify one instance of the `nonzero` field: if `2x`
lies strictly between two consecutive integers then `x` is not a half-integer,
so `cos (π x) ≠ 0`. -/
lemma cos_pi_ne_zero_of_between {x : ℝ} {j : ℤ} (h1 : (j : ℝ) < 2 * x) (h2 : 2 * x < j + 1) :
    Real.cos (π * x) ≠ 0 := by
  intro hc
  obtain ⟨n, hn⟩ := (cos_pi_mul_eq_zero_iff x).1 hc
  rw [hn] at h1 h2
  have e : 2 * ((n : ℝ) + 1/2) = ((2 * n + 1 : ℤ) : ℝ) := by push_cast; ring
  rw [e] at h1 h2
  have h1' : j < 2 * n + 1 := by exact_mod_cast h1
  have h2' : 2 * n + 1 < j + 1 := by exact_mod_cast h2
  omega

/-- The deficit of a factor is controlled by the distance bound. -/
lemma one_sub_cosFac_le (d : ConjApprox lam) (m : ℤ) :
    1 - cosFac lam m ≤ π ^ 2 * (d.C * d.t ^ m.natAbs) / 2 := by
  obtain ⟨n, hn⟩ := d.approx m
  have hshift : cosFac lam m = |Real.cos (π * (lam ^ m - n))| := abs_cos_pi_sub_int _ n
  have hb := one_sub_abs_cos_le (lam ^ m - n)
  rw [← hshift] at hb
  have hpi : (0:ℝ) < π ^ 2 := by positivity
  nlinarith [hb, hn]

/-- Once the geometric bound is below `1`, it also bounds the logarithm. -/
lemma abs_log_cosFac_le (d : ConjApprox lam) {m : ℤ}
    (h : π ^ 2 * (d.C * d.t ^ m.natAbs) ≤ 1) :
    |Real.log (cosFac lam m)| ≤ π ^ 2 * (d.C * d.t ^ m.natAbs) := by
  have hdef := one_sub_cosFac_le d m
  have hhalf : 1 / 2 ≤ cosFac lam m := by linarith
  have hle := abs_log_le_of_mem _ hhalf (cosFac_le_one lam m)
  linarith

lemma summable_geom_bound_gen (d : ConjApprox lam) :
    Summable (fun n : ℕ => π ^ 2 * (d.C * d.t ^ n)) := by
  have h := (summable_geometric_of_lt_one d.ht0.le d.ht1).mul_left (π ^ 2 * d.C)
  exact h.congr (fun n => by ring)

lemma exists_threshold_gen (d : ConjApprox lam) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → π ^ 2 * (d.C * d.t ^ n) ≤ 1 := by
  have htend : Tendsto (fun n : ℕ => π ^ 2 * (d.C * d.t ^ n)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ => d.t ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one d.ht0.le d.ht1
    simpa using (h0.const_mul d.C).const_mul (π ^ 2)
  have h := htend.eventually_le_const (show (0:ℝ) < 1 by norm_num)
  rw [eventually_atTop] at h
  obtain ⟨n₀, hn₀⟩ := h
  exact ⟨n₀, hn₀⟩

lemma summable_log_cosFac_nat (d : ConjApprox lam) :
    Summable (fun n : ℕ => Real.log (cosFac lam n)) := by
  obtain ⟨n₀, hn₀⟩ := exists_threshold_gen d
  rw [← summable_nat_add_iff n₀]
  refine Summable.of_norm_bounded (g := fun n : ℕ => π ^ 2 * (d.C * d.t ^ (n + n₀)))
    ((summable_nat_add_iff n₀).mpr (summable_geom_bound_gen d)) (fun n => ?_)
  have hnat : ((n + n₀ : ℕ) : ℤ).natAbs = n + n₀ := by omega
  have h := abs_log_cosFac_le d (m := ((n + n₀ : ℕ) : ℤ)) (by rw [hnat]; exact hn₀ _ (by omega))
  rw [hnat] at h
  rw [Real.norm_eq_abs]
  exact h

lemma summable_log_cosFac_neg (d : ConjApprox lam) :
    Summable (fun n : ℕ => Real.log (cosFac lam (-((n : ℤ) + 1)))) := by
  obtain ⟨n₀, hn₀⟩ := exists_threshold_gen d
  rw [← summable_nat_add_iff n₀]
  refine Summable.of_norm_bounded (g := fun n : ℕ => π ^ 2 * (d.C * d.t ^ (n + n₀ + 1)))
    ((summable_nat_add_iff (n₀ + 1)).mpr (summable_geom_bound_gen d)) (fun n => ?_)
  have hnat : (-(((n + n₀ : ℕ) : ℤ) + 1)).natAbs = n + n₀ + 1 := by omega
  have h := abs_log_cosFac_le d (m := -(((n + n₀ : ℕ) : ℤ) + 1))
    (by rw [hnat]; exact hn₀ _ (by omega))
  rw [hnat] at h
  rw [Real.norm_eq_abs]
  exact h

theorem summable_log_cosFac (d : ConjApprox lam) :
    Summable (fun m : ℤ => Real.log (cosFac lam m)) :=
  Summable.of_nat_of_neg_add_one (summable_log_cosFac_nat d) (summable_log_cosFac_neg d)

/-- The two-sided product converges. -/
theorem multipliable_cosFac (d : ConjApprox lam) : Multipliable (cosFac lam) :=
  Real.multipliable_of_summable_log (cosFac_pos d) (summable_log_cosFac d)

theorem tprod_cosFac_eq_exp (d : ConjApprox lam) :
    ∏' m : ℤ, cosFac lam m = Real.exp (∑' m : ℤ, Real.log (cosFac lam m)) :=
  (Real.rexp_tsum_eq_tprod (cosFac_pos d) (summable_log_cosFac d)).symm

/-- The Fourier floor at `lam` is strictly positive. -/
theorem tprod_cosFac_pos (d : ConjApprox lam) : 0 < ∏' m : ℤ, cosFac lam m := by
  rw [tprod_cosFac_eq_exp d]
  exact Real.exp_pos _

/-! ## The limit along the frequencies `ξ_N` -/

private lemma summable_log_shift_gen (d : ConjApprox lam) (N : ℕ) :
    Summable (fun j : ℕ => Real.log (cosFac lam ((N : ℤ) - j))) :=
  (summable_log_cosFac d).comp_injective (i := fun j : ℕ => (N : ℤ) - j)
    (fun a b hab => by simp only at hab; omega)

private lemma tsum_split_gen (d : ConjApprox lam) (N : ℕ) :
    ∑' m : ℤ, Real.log (cosFac lam m)
      = ∑' n : ℕ, Real.log (cosFac lam ((n : ℤ) + N + 1))
        + ∑' j : ℕ, Real.log (cosFac lam ((N : ℤ) - j)) := by
  have hGsum : Summable (fun m : ℤ => Real.log (cosFac lam (m + ((N : ℤ) + 1)))) :=
    (summable_log_cosFac d).comp_injective (i := fun m : ℤ => m + ((N : ℤ) + 1))
      (fun a b hab => by simpa using hab)
  have h1 : Summable (fun n : ℕ => Real.log (cosFac lam ((n : ℤ) + ((N : ℤ) + 1)))) :=
    hGsum.comp_injective (i := fun n : ℕ => (n : ℤ)) (fun a b hab => by simpa using hab)
  have h2 : Summable (fun n : ℕ => Real.log (cosFac lam (-((n : ℤ) + 1) + ((N : ℤ) + 1)))) :=
    hGsum.comp_injective (i := fun n : ℕ => -((n : ℤ) + 1))
      (fun a b hab => by simp only at hab; omega)
  have hsplit := tsum_of_nat_of_neg_add_one
    (f := fun m : ℤ => Real.log (cosFac lam (m + ((N : ℤ) + 1)))) h1 h2
  have hfull := Equiv.tsum_eq (Equiv.addRight ((N : ℤ) + 1))
    (fun m : ℤ => Real.log (cosFac lam m))
  simp only [Equiv.coe_addRight] at hfull
  rw [hfull] at hsplit
  have e1 : ∑' n : ℕ, Real.log (cosFac lam ((n : ℤ) + ((N : ℤ) + 1)))
      = ∑' n : ℕ, Real.log (cosFac lam ((n : ℤ) + N + 1)) :=
    tsum_congr (fun n => by
      rw [show ((n : ℤ) + ((N : ℤ) + 1)) = (n : ℤ) + N + 1 from by ring])
  have e2 : ∑' n : ℕ, Real.log (cosFac lam (-((n : ℤ) + 1) + ((N : ℤ) + 1)))
      = ∑' j : ℕ, Real.log (cosFac lam ((N : ℤ) - j)) :=
    tsum_congr (fun n => by
      rw [show (-((n : ℤ) + 1) + ((N : ℤ) + 1)) = (N : ℤ) - n from by ring])
  rw [hsplit]
  simp only [e1, e2]

private lemma tendsto_tail_zero_gen (lam : ℝ) :
    Tendsto (fun N : ℕ => ∑' n : ℕ, Real.log (cosFac lam ((n : ℤ) + N + 1))) atTop (𝓝 0) := by
  have h := tendsto_sum_nat_add (fun k : ℕ => Real.log (cosFac lam ((k : ℤ) + 1)))
  refine h.congr (fun N => ?_)
  exact tsum_congr (fun k =>
    by rw [show (((k + N : ℕ) : ℤ) + 1) = (k : ℤ) + N + 1 from by push_cast; ring])

theorem tendsto_log_partial_gen (d : ConjApprox lam) :
    Tendsto (fun N : ℕ => ∑' j : ℕ, Real.log (cosFac lam ((N : ℤ) - j))) atTop
      (𝓝 (∑' m : ℤ, Real.log (cosFac lam m))) := by
  have hrw : ∀ N : ℕ, ∑' j : ℕ, Real.log (cosFac lam ((N : ℤ) - j))
      = (∑' m : ℤ, Real.log (cosFac lam m))
        - ∑' n : ℕ, Real.log (cosFac lam ((n : ℤ) + N + 1)) := by
    intro N
    rw [tsum_split_gen d N]
    ring
  simp only [hrw]
  have hc : Tendsto (fun _ : ℕ => ∑' m : ℤ, Real.log (cosFac lam m)) atTop
      (𝓝 (∑' m : ℤ, Real.log (cosFac lam m))) := tendsto_const_nhds
  simpa using hc.sub (tendsto_tail_zero_gen lam)

/-- The truncated products `∏_{m ≤ N}|cos(π λ^m)|` converge to the two-sided
product. -/
theorem tendsto_tprod_partial_gen (d : ConjApprox lam) :
    Tendsto (fun N : ℕ => ∏' j : ℕ, cosFac lam ((N : ℤ) - j)) atTop
      (𝓝 (∏' m : ℤ, cosFac lam m)) := by
  have hexp : ∀ N : ℕ, ∏' j : ℕ, cosFac lam ((N : ℤ) - j)
      = Real.exp (∑' j : ℕ, Real.log (cosFac lam ((N : ℤ) - j))) :=
    fun N => (Real.rexp_tsum_eq_tprod (fun j => cosFac_pos d _)
      (summable_log_shift_gen d N)).symm
  simp only [hexp, tprod_cosFac_eq_exp d]
  exact (Real.continuous_exp.tendsto _).comp (tendsto_log_partial_gen d)

/-- The transform of the backward system at the frequencies `ξ_N = λ^N/(1−r)`
converges to the Fourier floor of `λ`. -/
theorem tendsto_cosProd_xi_gen (d : ConjApprox lam) (hlam : 1 < lam) :
    Tendsto (fun N : ℕ => cosProd (r lam) (xi lam N)) atTop (𝓝 (∏' m : ℤ, cosFac lam m)) := by
  have hrw : ∀ N : ℕ, cosProd (r lam) (xi lam N) = ∏' j : ℕ, cosFac lam ((N : ℤ) - j) :=
    fun N => cosProd_xi hlam N
  simp only [hrw]
  exact tendsto_tprod_partial_gen d

end Fourier
end KnotGame
