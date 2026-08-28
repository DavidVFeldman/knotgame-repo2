import RequestProject.FourierFloor

/-!
# The reflection symmetry of the golden Fourier floor (round 9, T29a addendum)

A bonus of the Lucas trace identity of `RequestProject.Lucas`: the factor
`|cos (π φ^m)|` is unchanged by `m ↦ -m`, so the two-sided product certified
in `RequestProject.FourierFloor` is the square of its one-sided half.  This is
the shape a numerical enclosure of the floor (the optional target T29b, not
attempted) would use.

Kept in a separate module purely for build hygiene: `FourierFloor.lean` is
expensive to elaborate and nothing there depends on the statements below.
-/

namespace KnotGame
namespace Fourier

open Real Filter Topology
open scoped Real

set_option maxHeartbeats 1000000

/-! ## The reflection symmetry and the square form

A bonus of the trace identity: `|cos(π φ^m)| = |cos(π φ^{-m})|`, because
`φ^m` and `(-1)^m φ^{-m}` differ by the integer `L_m`.  The two-sided product
is therefore the square of its one-sided half, which is the shape a numerical
enclosure (T29b) would use.
-/

@[simp] lemma goldenFac_zero : goldenFac 0 = 1 := by
  have h : Real.goldenRatio ^ (0 : ℤ) = 1 := zpow_zero _
  rw [goldenFac, cosFac, h, mul_one, Real.cos_pi, abs_neg, abs_one]

/-- **Reflection**: the golden factors at `m` and `-m` agree. -/
theorem goldenFac_neg_natCast (k : ℕ) : goldenFac (-(k : ℤ)) = goldenFac (k : ℤ) := by
  have hpsi : Real.goldenConj = -Real.goldenRatio⁻¹ := by
    rw [Real.inv_goldenRatio, neg_neg]
  have hid : Real.goldenRatio ^ k - (lucas k : ℝ) = -((-1) ^ k * (Real.goldenRatio⁻¹) ^ k) := by
    have h := goldenRatio_pow_add_goldenConj_pow k
    have hc : Real.goldenConj ^ k = (-1) ^ k * (Real.goldenRatio⁻¹) ^ k := by
      rw [hpsi, neg_pow]
    rw [← hc]
    linarith
  have hneg : Real.goldenRatio ^ (-(k : ℤ)) = (Real.goldenRatio⁻¹) ^ k := by
    rw [zpow_neg, ← inv_zpow, zpow_natCast]
  have hpos : Real.goldenRatio ^ (k : ℤ) = Real.goldenRatio ^ k := by
    rw [zpow_natCast]
  rw [goldenFac, goldenFac, cosFac, cosFac, hneg, hpos,
    abs_cos_pi_sub_int (Real.goldenRatio ^ k) (lucas k), hid]
  rcases Nat.even_or_odd k with hk | hk
  · rw [hk.neg_one_pow, one_mul, mul_neg, Real.cos_neg]
  · rw [hk.neg_one_pow, neg_one_mul, neg_neg]

/-- **T29a(iii)**, square form: the two-sided Fourier floor is the square of
the one-sided product over the negative exponents. -/
theorem goldenFourierFloor_eq_sq :
    ∏' m : ℤ, goldenFac m = (∏' k : ℕ, goldenFac (-((k : ℤ) + 1))) ^ 2 := by
  have hQ : ∏' k : ℕ, goldenFac (-((k : ℤ) + 1))
      = Real.exp (∑' k : ℕ, Real.log (goldenFac (-((k : ℤ) + 1)))) :=
    (Real.rexp_tsum_eq_tprod (fun k => goldenFac_pos _) summable_log_goldenFac_neg).symm
  have hnat : ∑' n : ℕ, Real.log (goldenFac (n : ℤ))
      = ∑' k : ℕ, Real.log (goldenFac (-((k : ℤ) + 1))) := by
    rw [summable_log_goldenFac_nat.tsum_eq_zero_add]
    have h0 : Real.log (goldenFac ((0 : ℕ) : ℤ)) = 0 := by simp
    rw [h0, zero_add]
    refine tsum_congr (fun n => ?_)
    rw [← goldenFac_neg_natCast (n + 1)]
    congr 2
  have hsplit := tsum_of_nat_of_neg_add_one (f := fun m : ℤ => Real.log (goldenFac m))
    summable_log_goldenFac_nat summable_log_goldenFac_neg
  rw [tprod_goldenFac_eq_exp, hQ, sq, ← Real.exp_add]
  simp only [hsplit, hnat]

end Fourier
end KnotGame
