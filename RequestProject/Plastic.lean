import RequestProject.Pisot

/-!
# Proposition 3.4: the plastic number (Work Order 6)

What is certified here is the hypothesis of Proposition 3.4: the plastic number
is a Pisot number, so by `KnotGame.orb_finite` (Theorem 3.1) its orbit is
finite.

The full statement — a `153`-point orbit, `25 525` reachable configurations,
`sup N = 7` and the least lengths — is a finite verification, carried out in
`PlasticOrbit.lean`, `PlasticIndex.lean`, `PlasticCert.lean`,
`PlasticConfig.lean` and `PlasticOrbitCount.lean`; see `PROP9-PLASTIC.md`.
(`PLASTIC-REPORT.md` records the first, unsuccessful route and its cost
measurements.)
-/

namespace KnotGame
namespace Plastic

open Polynomial

/-- The cubic `X³ - X - 1`, whose real root is the plastic number. -/
noncomputable def cubic : Polynomial ℤ := X ^ 3 - X - 1

lemma cubic_monic : cubic.Monic := by
  unfold cubic
  monicity!

lemma aeval_cubic {R : Type*} [CommRing R] (z : R) :
    Polynomial.aeval z cubic = z ^ 3 - z - 1 := by
  simp [cubic]

private lemma exists_root : ∃ x : ℝ, x ∈ Set.Ioo (1:ℝ) 2 ∧ x ^ 3 - x - 1 = 0 := by
  have hcont : ContinuousOn (fun x : ℝ => x ^ 3 - x - 1) (Set.Icc 1 2) :=
    (Continuous.continuousOn (by continuity))
  have h0 : (0:ℝ) ∈ Set.Ioo ((1:ℝ) ^ 3 - 1 - 1) ((2:ℝ) ^ 3 - 2 - 1) := by
    constructor <;> norm_num
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Ioo (by norm_num : (1:ℝ) ≤ 2) hcont h0
  exact ⟨x, hx, hfx⟩

/-- The **plastic number**: the real root of `x³ = x + 1`. -/
noncomputable def rho : ℝ := Classical.choose exists_root

lemma rho_mem : rho ∈ Set.Ioo (1:ℝ) 2 := (Classical.choose_spec exists_root).1

lemma rho_cubic : rho ^ 3 - rho - 1 = 0 := (Classical.choose_spec exists_root).2

lemma one_lt_rho : 1 < rho := rho_mem.1

lemma rho_lt : rho < 1.33 := by
  have h := rho_cubic
  nlinarith [h, rho_mem.1, sq_nonneg (rho - 1.33), sq_nonneg (rho + 1.33), sq_nonneg rho]

lemma rho_gt : 1.32 < rho := by
  have h := rho_cubic
  nlinarith [h, rho_mem.1, sq_nonneg (rho - 1.32), sq_nonneg (rho + 1.32), sq_nonneg rho]

/-- The quadratic factor `X² + ρX + (ρ²-1)` of the cubic. -/
lemma cubic_factor (z : ℂ) :
    z ^ 3 - z - 1 = (z - (rho : ℂ)) * (z ^ 2 + (rho : ℂ) * z + ((rho : ℂ) ^ 2 - 1)) := by
  have h : ((rho : ℂ)) ^ 3 - (rho : ℂ) - 1 = 0 := by
    have := rho_cubic
    exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) this
  linear_combination h

/-- **The plastic number is a Pisot number.** -/
theorem isPisot_rho : IsPisot rho := by
  refine ⟨one_lt_rho, cubic, cubic_monic, ?_, ?_⟩
  · rw [aeval_cubic]
    linarith [rho_cubic]
  · intro z hz hne
    rw [aeval_cubic] at hz
    rw [cubic_factor] at hz
    have hq : z ^ 2 + (rho : ℂ) * z + ((rho : ℂ) ^ 2 - 1) = 0 := by
      rcases mul_eq_zero.mp hz with h | h
      · exact absurd (sub_eq_zero.mp h) hne
      · exact h
    -- the conjugate root
    have hqc : (starRingEnd ℂ) z ^ 2 + (rho : ℂ) * (starRingEnd ℂ) z
        + ((rho : ℂ) ^ 2 - 1) = 0 := by
      have := congrArg (starRingEnd ℂ) hq
      simpa using this
    have hzne : (starRingEnd ℂ) z ≠ z := by
      intro hc
      -- then `z` is real and the real quadratic has negative discriminant
      have hreal : ∃ a : ℝ, z = (a : ℂ) := ⟨z.re, (Complex.conj_eq_iff_re.mp hc).symm⟩
      obtain ⟨a, rfl⟩ := hreal
      have : (a : ℝ) ^ 2 + rho * a + (rho ^ 2 - 1) = 0 := by
        exact_mod_cast hq
      nlinarith [sq_nonneg (a + rho / 2), rho_gt, rho_lt]
    -- Vieta: the sum of the two roots is `-ρ`
    have hsum : z + (starRingEnd ℂ) z = -(rho : ℂ) := by
      have hdiff : (z - (starRingEnd ℂ) z) * (z + (starRingEnd ℂ) z + (rho : ℂ)) = 0 := by
        linear_combination hq - hqc
      rcases mul_eq_zero.mp hdiff with h | h
      · exact absurd (sub_eq_zero.mp h).symm hzne
      · linear_combination h
    have hprod : z * (starRingEnd ℂ) z = ((rho : ℂ) ^ 2 - 1) := by
      have hw : (starRingEnd ℂ) z = -(rho : ℂ) - z := by linear_combination hsum
      rw [hw]
      linear_combination -hq
    have hns : (Complex.normSq z : ℝ) = rho ^ 2 - 1 := by
      have := Complex.mul_conj z
      rw [hprod] at this
      exact_mod_cast this.symm
    have hlt1 : rho ^ 2 - 1 < 1 := by nlinarith [rho_lt, one_lt_rho]
    have h0 : 0 ≤ rho ^ 2 - 1 := by nlinarith [one_lt_rho]
    have : ‖z‖ ^ 2 < 1 := by
      rw [Complex.sq_norm, hns]
      exact hlt1
    nlinarith [norm_nonneg z]

/-- **Theorem 3.1 applied to the plastic number**: the orbit of `1/2` is
finite. -/
theorem orb_rho_finite : (Orb rho).Finite := orb_finite isPisot_rho

end Plastic
end KnotGame
