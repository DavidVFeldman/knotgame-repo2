import RequestProject.Contraction
import RequestProject.EquiMean

/-!
# T45 — an invariant probability measure for the normalised counting operator

`RequestProject.Contraction` proves that the normalised counting operator

  `(P h)(y) = (1/2) [ h (r y) + h (r y + 1 - r) ]`,   `r = 1/λ`,

contracts the Lipschitz seminorm by `r`, so that `P^[m] h` converges uniformly
on `[0,1]` to a constant, and it identifies that constant as `∫ h dν` *given* a
probability measure `ν` carried by `[0,1]` which is invariant for `P` in the
sense of `Contraction.InvariantOn` — one step, tested against Lipschitz
functions.  Until now nothing in the project produced such a measure.

This module constructs one.  It is the law of

  `X = (1 - r) ∑_{j ≥ 0} ε_j r^j`,  `ε_j` the binary digits of a uniform point,

realised as the push-forward of Lebesgue measure on `(0,1]` under the digit
series `bval`.  No identification of this measure with any object named
elsewhere in the project or in the literature is asserted; what is proved about
it is exactly the list below:

* `digit j t` — the `j`-th binary digit of `t` (`0` or `1`), as a real number;
* `bval lam t = (1 - r) ∑' j, digit j t · r^j`, which takes values in `[0,1]`;
* `nu lam = map (bval lam) (volume.restrict (Ioc 0 1))`;
* `isProbabilityMeasure_nu`, `nu_compl_Icc` — `nu` is a probability measure
  carried by `[0,1]`;
* `invariantOn_nu` — **the theorem**: `nu` is invariant for `P`;
* `const_eq_integral_nu`, `tendsto_integral_nu`, `equidistribution_in_mean_nu`
  — the hypotheses of `Contraction.const_eq_integral_of_invariant` and of
  `EquiMean.equidistribution_in_mean` discharged.

## Conventions (SCRUPLES)

* **Why Lebesgue and not a product measure.**  One route is the product of
  Bernoulli(1/2) laws on `ℕ → Fin 2` pushed forward by the digit series, with
  invariance coming from the factorisation of the product measure into its
  first coordinate and the shift.  The route taken here is the digits of a
  *uniform real*: they are independent and uniform on `{0,1}` for free, since
  Lebesgue measure on `(0,1]` already is the law of the digit sequence; the
  shift is the doubling map; and the factorisation is the elementary change of
  variables `s = 2t` on each half of `(0,1]`, which is exactly where the factor
  `1/2` in `P` comes from.  Nothing about infinite products, product
  σ-algebras or measurable equivalences `(ℕ → X) ≃ᵐ X × (ℕ → X)` is needed.
* **The recursion holds off a finite set.**  `bval t = (1-r)·digit 0 t +
  r·bval (fract (2t))` holds for every `t`; the two branch forms
  `bval t = r · bval (2t)` on `[0, 1/2)` and
  `bval t = (1-r) + r · bval (2t-1)` on `[1/2, 1)` fail at the single point
  `t = 1` (where all digits vanish), which is why the change of variables is
  performed with an a.e. congruence.
* **`Ioc 0 1`, not `Icc 0 1`**, as the domain of the uniform point: it is a
  probability measure and matches the interval integral `∫ t in 0..1`.  The
  endpoints carry no mass, so the choice is immaterial.
* The measure is `nu lam` for arbitrary real `lam`; every statement about it
  assumes `1 < lam`, without which the defining series need not converge.
-/

namespace KnotGame
namespace InvariantMeasure

open MeasureTheory Set Filter Topology
open KnotGame.Contraction

variable {lam : ℝ}

/-! ### Binary digits -/

/-- The `j`-th binary digit of `t`, as a real number: `0` or `1`. -/
noncomputable def digit (j : ℕ) (t : ℝ) : ℝ := if Int.fract (2 ^ j * t) < 1 / 2 then 0 else 1

lemma digit_nonneg (j : ℕ) (t : ℝ) : 0 ≤ digit j t := by
  unfold digit; split <;> norm_num

lemma digit_le_one (j : ℕ) (t : ℝ) : digit j t ≤ 1 := by
  unfold digit; split <;> norm_num

lemma measurable_digit (j : ℕ) : Measurable (digit j) := by
  have hs : MeasurableSet {t : ℝ | Int.fract (2 ^ j * t) < 1 / 2} :=
    measurableSet_lt (measurable_fract.comp (measurable_id.const_mul _)) measurable_const
  exact Measurable.ite hs measurable_const measurable_const

/-- The fractional part sees the shift of the digit index. -/
lemma fract_shift (j : ℕ) (t : ℝ) :
    Int.fract ((2:ℝ) ^ j * Int.fract (2 * t)) = Int.fract ((2:ℝ) ^ (j + 1) * t) := by
  have e : (2:ℝ) ^ j * Int.fract (2 * t) = (2:ℝ) ^ (j + 1) * t - ((2 ^ j * ⌊2 * t⌋ : ℤ) : ℝ) := by
    rw [Int.fract]; push_cast; ring
  rw [e, Int.fract_sub_intCast]

/-- The digits of `fract (2t)` are the digits of `t`, shifted. -/
lemma digit_shift (j : ℕ) (t : ℝ) : digit j (Int.fract (2 * t)) = digit (j + 1) t := by
  unfold digit
  rw [fract_shift]

lemma digit_zero_of_lt_half {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1 / 2) : digit 0 t = 0 := by
  have ht : Int.fract t = t := Int.fract_eq_self.2 ⟨h0, by linarith⟩
  unfold digit
  rw [pow_zero, one_mul, ht, if_pos h1]

lemma digit_zero_of_half_le {t : ℝ} (h0 : 1 / 2 ≤ t) (h1 : t < 1) : digit 0 t = 1 := by
  have ht : Int.fract t = t := Int.fract_eq_self.2 ⟨by linarith, h1⟩
  unfold digit
  simp only [pow_zero, one_mul, ht]
  rw [if_neg (by linarith)]

/-! ### The digit series -/

/-- The value of the digit series: `bval t = (1 - r) ∑ digit j t · r^j`.  The
measure `nu` below is its law under a uniform `t`. -/
noncomputable def bval (lam t : ℝ) : ℝ := (1 - r lam) * ∑' j : ℕ, digit j t * (r lam) ^ j

lemma summable_digit (hlam : 1 < lam) (t : ℝ) :
    Summable (fun j : ℕ => digit j t * (r lam) ^ j) := by
  have hr0 : 0 ≤ r lam := le_of_lt (KnotGame.r_pos lam hlam)
  have hr1 : r lam < 1 := KnotGame.r_lt_one lam hlam
  refine Summable.of_nonneg_of_le
    (fun j => mul_nonneg (digit_nonneg j t) (pow_nonneg hr0 j)) (fun j => ?_)
    (summable_geometric_of_lt_one hr0 hr1)
  exact mul_le_of_le_one_left (pow_nonneg hr0 j) (digit_le_one j t)

lemma bval_mem_Icc (hlam : 1 < lam) (t : ℝ) : bval lam t ∈ Icc (0:ℝ) 1 := by
  have hr0 : 0 ≤ r lam := le_of_lt (KnotGame.r_pos lam hlam)
  have hr1 : r lam < 1 := KnotGame.r_lt_one lam hlam
  have hden : 0 < 1 - r lam := by linarith
  have hlow : 0 ≤ ∑' j : ℕ, digit j t * (r lam) ^ j :=
    tsum_nonneg (fun j => mul_nonneg (digit_nonneg j t) (pow_nonneg hr0 j))
  have hhigh : ∑' j : ℕ, digit j t * (r lam) ^ j ≤ (1 - r lam)⁻¹ := by
    have := Summable.tsum_mono (f := fun j : ℕ => digit j t * (r lam) ^ j)
      (g := fun j : ℕ => (r lam) ^ j)
      (summable_digit hlam t) (summable_geometric_of_lt_one hr0 hr1)
      (fun j => mul_le_of_le_one_left (pow_nonneg hr0 j) (digit_le_one j t))
    rwa [tsum_geometric_of_lt_one hr0 hr1] at this
  constructor
  · exact mul_nonneg (le_of_lt hden) hlow
  · rw [bval]
    calc (1 - r lam) * ∑' j : ℕ, digit j t * (r lam) ^ j
        ≤ (1 - r lam) * (1 - r lam)⁻¹ := by
          exact mul_le_mul_of_nonneg_left hhigh (le_of_lt hden)
      _ = 1 := by field_simp

lemma bval_nonneg (hlam : 1 < lam) (t : ℝ) : 0 ≤ bval lam t := (bval_mem_Icc hlam t).1

lemma measurable_bval (hlam : 1 < lam) : Measurable (bval lam) := by
  have hpartial : ∀ n : ℕ,
      Measurable (fun t => ∑ j ∈ Finset.range n, digit j t * (r lam) ^ j) := by
    intro n
    exact Finset.measurable_sum _ (fun j _ => (measurable_digit j).mul_const _)
  have htend : Tendsto (fun n t => ∑ j ∈ Finset.range n, digit j t * (r lam) ^ j) atTop
      (𝓝 (fun t => ∑' j : ℕ, digit j t * (r lam) ^ j)) := by
    rw [tendsto_pi_nhds]
    intro t
    exact (summable_digit hlam t).hasSum.tendsto_sum_nat
  exact (measurable_of_tendsto_metrizable hpartial htend).const_mul _

/-- **The self-similarity of the digit series.** -/
lemma bval_rec (hlam : 1 < lam) (t : ℝ) :
    bval lam t = (1 - r lam) * digit 0 t + r lam * bval lam (Int.fract (2 * t)) := by
  have hsum := summable_digit hlam t
  have h1 : ∑' j : ℕ, digit j t * (r lam) ^ j
      = digit 0 t + ∑' j : ℕ, digit (j + 1) t * (r lam) ^ (j + 1) := by
    simpa using hsum.tsum_eq_zero_add
  have h2 : ∑' j : ℕ, digit (j + 1) t * (r lam) ^ (j + 1)
      = r lam * ∑' j : ℕ, digit j (Int.fract (2 * t)) * (r lam) ^ j := by
    rw [← tsum_mul_left]
    refine tsum_congr (fun j => ?_)
    rw [digit_shift]
    ring
  rw [bval, bval, h1, h2]
  ring

/-- The lower branch of the self-similarity. -/
lemma bval_of_lt_half (hlam : 1 < lam) {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1 / 2) :
    bval lam t = r lam * bval lam (2 * t) := by
  have hfr : Int.fract (2 * t) = 2 * t := Int.fract_eq_self.2 ⟨by linarith, by linarith⟩
  rw [bval_rec hlam t, digit_zero_of_lt_half h0 h1, hfr]
  ring

/-- The upper branch of the self-similarity. -/
lemma bval_of_half_le (hlam : 1 < lam) {t : ℝ} (h0 : 1 / 2 ≤ t) (h1 : t < 1) :
    bval lam t = (1 - r lam) + r lam * bval lam (2 * t - 1) := by
  have hfr : Int.fract (2 * t) = 2 * t - 1 := by
    have h2 : Int.fract (2 * t - ((1 : ℤ) : ℝ)) = Int.fract (2 * t) :=
      Int.fract_sub_intCast _ _
    have h3 : Int.fract (2 * t - ((1 : ℤ) : ℝ)) = 2 * t - ((1 : ℤ) : ℝ) :=
      Int.fract_eq_self.2 ⟨by push_cast; linarith, by push_cast; linarith⟩
    rw [h2] at h3
    rw [h3]
    norm_num
  rw [bval_rec hlam t, digit_zero_of_half_le h0 h1, hfr]
  ring

/-! ### Integrability of the compositions -/

lemma intervalIntegrable_of_bounded {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) (a b : ℝ) : IntervalIntegrable f volume a b := by
  have key : ∀ u v : ℝ, IntegrableOn f (Ioc u v) volume := by
    intro u v
    haveI : IsFiniteMeasure (volume.restrict (Ioc u v)) := by
      constructor
      rw [Measure.restrict_apply_univ, Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top
    exact Integrable.of_bound hf.aestronglyMeasurable C
      (Eventually.of_forall (fun x => by simpa [Real.norm_eq_abs] using hC x))
  exact ⟨key a b, key b a⟩

/-- A continuous function is bounded on `[0,1]`. -/
lemma exists_bound_on_Icc {psi : ℝ → ℝ} (hpsi : Continuous psi) :
    ∃ C : ℝ, ∀ y ∈ Icc (0:ℝ) 1, |psi y| ≤ C := by
  obtain ⟨y0, -, hy0⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.2 (by norm_num : (0:ℝ) ≤ 1)) hpsi.abs.continuousOn
  exact ⟨|psi y0|, fun y hy => hy0 hy⟩

lemma intervalIntegrable_comp_bval (hlam : 1 < lam) {psi : ℝ → ℝ} (hpsi : Continuous psi)
    (a b : ℝ) : IntervalIntegrable (fun t => psi (bval lam t)) volume a b := by
  obtain ⟨C, hC⟩ := exists_bound_on_Icc hpsi
  exact intervalIntegrable_of_bounded (hpsi.measurable.comp (measurable_bval hlam))
    (fun t => hC _ (bval_mem_Icc hlam t)) a b

/-! ### The measure -/

/-- **The invariant measure**: the law of the digit series under a uniform point
of `(0,1]`. -/
noncomputable def nu (lam : ℝ) : Measure ℝ :=
  Measure.map (bval lam) (volume.restrict (Ioc (0:ℝ) 1))

theorem isProbabilityMeasure_nu (hlam : 1 < lam) : IsProbabilityMeasure (nu lam) := by
  constructor
  rw [nu, Measure.map_apply (measurable_bval hlam) MeasurableSet.univ]
  simp

/-- `nu` is carried by `[0,1]`. -/
theorem nu_compl_Icc (hlam : 1 < lam) : nu lam (Icc (0:ℝ) 1)ᶜ = 0 := by
  rw [nu, Measure.map_apply (measurable_bval hlam) (measurableSet_Icc.compl)]
  have : bval lam ⁻¹' (Icc (0:ℝ) 1)ᶜ = ∅ := by
    ext t
    simp [bval_mem_Icc hlam t]
  rw [this]
  simp

/-- Integration against `nu` is integration of the composition with `bval` over
`(0,1]`. -/
theorem integral_nu (hlam : 1 < lam) {psi : ℝ → ℝ} (hpsi : Continuous psi) :
    ∫ y, psi y ∂(nu lam) = ∫ t in (0:ℝ)..1, psi (bval lam t) := by
  rw [nu, integral_map (measurable_bval hlam).aemeasurable hpsi.aestronglyMeasurable,
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]

/-! ### The invariance -/

/-- **T45.**  `nu` is invariant for the normalised counting operator: the
hypothesis of `Contraction.const_eq_integral_of_invariant` holds. -/
theorem invariantOn_nu (hlam : 1 < lam) : InvariantOn lam (nu lam) := by
  rintro phi ⟨K, hK⟩
  have hphi : Continuous phi := continuous_of_lipBound hK
  have hA : Continuous (fun y : ℝ => phi (r lam * y)) := hphi.comp (by fun_prop)
  have hB : Continuous (fun y : ℝ => phi (r lam * y + 1 - r lam)) := hphi.comp (by fun_prop)
  have hP : Continuous (P lam phi) := by
    have e : P lam phi = fun y => (1/2) * (phi (r lam * y) + phi (r lam * y + 1 - r lam)) := rfl
    rw [e]
    exact continuous_const.mul (hA.add hB)
  -- the two integrals, as interval integrals
  rw [integral_nu hlam hP, integral_nu hlam hphi]
  -- integrability
  have iA : ∀ a b : ℝ, IntervalIntegrable (fun t => phi (r lam * bval lam t)) volume a b :=
    fun a b => intervalIntegrable_comp_bval hlam hA a b
  have iB : ∀ a b : ℝ,
      IntervalIntegrable (fun t => phi (r lam * bval lam t + 1 - r lam)) volume a b :=
    fun a b => intervalIntegrable_comp_bval hlam hB a b
  have iphi : ∀ a b : ℝ, IntervalIntegrable (fun t => phi (bval lam t)) volume a b :=
    fun a b => intervalIntegrable_comp_bval hlam hphi a b
  -- the left-hand side splits by linearity
  have hleft : ∫ t in (0:ℝ)..1, P lam phi (bval lam t)
      = (1/2) * (∫ t in (0:ℝ)..1, phi (r lam * bval lam t))
        + (1/2) * (∫ t in (0:ℝ)..1, phi (r lam * bval lam t + 1 - r lam)) := by
    have hpt : ∀ t : ℝ, P lam phi (bval lam t)
        = (1/2) * phi (r lam * bval lam t) + (1/2) * phi (r lam * bval lam t + 1 - r lam) := by
      intro t; rw [P]; ring
    simp only [hpt]
    rw [intervalIntegral.integral_add ((iA 0 1).const_mul _) ((iB 0 1).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  -- the right-hand side splits at 1/2 and rescales
  have hne : ∀ᵐ t : ℝ, t ≠ 1 / 2 := by
    rw [ae_iff]
    simp
  have hne1 : ∀ᵐ t : ℝ, t ≠ 1 := by
    rw [ae_iff]
    simp
  have e1 : ∫ t in (0:ℝ)..(1/2), phi (bval lam t)
      = (1/2) * ∫ s in (0:ℝ)..1, phi (r lam * bval lam s) := by
    have hcongr : ∫ t in (0:ℝ)..(1/2), phi (bval lam t)
        = ∫ t in (0:ℝ)..(1/2), (fun s => phi (r lam * bval lam s)) (2 * t) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hne] with t ht hmem
      rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1/2)] at hmem
      have h0 : 0 ≤ t := le_of_lt hmem.1
      have h1 : t < 1 / 2 := lt_of_le_of_ne hmem.2 ht
      rw [bval_of_lt_half hlam h0 h1]
    rw [hcongr, intervalIntegral.integral_comp_mul_left
      (fun s => phi (r lam * bval lam s)) (by norm_num : (2:ℝ) ≠ 0)]
    norm_num
  have e2 : ∫ t in (1/2:ℝ)..1, phi (bval lam t)
      = (1/2) * ∫ s in (0:ℝ)..1, phi (r lam * bval lam s + 1 - r lam) := by
    have hcongr : ∫ t in (1/2:ℝ)..1, phi (bval lam t)
        = ∫ t in (1/2:ℝ)..1,
            (fun s => phi (r lam * bval lam (s - 1) + 1 - r lam)) (2 * t) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hne1] with t ht hmem
      rw [uIoc_of_le (by norm_num : (1/2:ℝ) ≤ 1)] at hmem
      have h0 : 1 / 2 ≤ t := le_of_lt hmem.1
      have h1 : t < 1 := lt_of_le_of_ne hmem.2 ht
      have : (2 : ℝ) * t - 1 = 2 * t - 1 := rfl
      rw [bval_of_half_le hlam h0 h1]
      ring_nf
    rw [hcongr, intervalIntegral.integral_comp_mul_left
      (fun s => phi (r lam * bval lam (s - 1) + 1 - r lam)) (by norm_num : (2:ℝ) ≠ 0)]
    have hsub := intervalIntegral.integral_comp_sub_right
      (a := (1:ℝ)) (b := (2:ℝ)) (fun s => phi (r lam * bval lam s + 1 - r lam)) 1
    norm_num at hsub ⊢
    rw [hsub]
  have hsplit : (∫ t in (0:ℝ)..(1/2), phi (bval lam t))
        + (∫ t in (1/2:ℝ)..1, phi (bval lam t))
      = ∫ t in (0:ℝ)..1, phi (bval lam t) :=
    intervalIntegral.integral_add_adjacent_intervals (iphi 0 (1/2)) (iphi (1/2) 1)
  rw [hleft, ← hsplit, e1, e2]

/-! ### The hypotheses discharged -/

/-- **T45, applied.**  The limit constant of the iterates is `∫ h dν`. -/
theorem const_eq_integral_nu (hlam : 1 < lam) {K : ℝ} {h : ℝ → ℝ} (hK : LipBound K h) {c : ℝ}
    (hc : ∀ (m : ℕ), ∀ y ∈ Icc (0:ℝ) 1,
      |(P lam)^[m] h y - c| ≤ (2 * K / (1 - r lam)) * (r lam) ^ m) :
    ∫ y, h y ∂(nu lam) = c := by
  haveI := isProbabilityMeasure_nu hlam
  exact const_eq_integral_of_invariant hlam hK hc (nu_compl_Icc hlam) (invariantOn_nu hlam)

/-- **T45, unconditional form of `prop:gap`.**  For a Lipschitz `h` the iterates
`P^[m] h` converge uniformly on `[0,1]` to `∫ h dν`, at the rate `r^m`, with no
hypothesis beyond `1 < lam`. -/
theorem tendsto_integral_nu (hlam : 1 < lam) {K : ℝ} {h : ℝ → ℝ} (hK : LipBound K h) :
    ∀ (m : ℕ), ∀ y ∈ Icc (0:ℝ) 1,
      |(P lam)^[m] h y - ∫ z, h z ∂(nu lam)| ≤ (2 * K / (1 - r lam)) * (r lam) ^ m := by
  haveI := isProbabilityMeasure_nu hlam
  exact tendsto_integral_of_invariant hlam hK (nu_compl_Icc hlam) (invariantOn_nu hlam)

/-- **T45, applied to `thm:equimean`.**  The equidistribution-in-mean statement
with its constant identified: no hypothesis on the limit is left. -/
theorem equidistribution_in_mean_nu (hlam : 1 < lam) {Ch Cg K : ℝ} {h k : ℝ → ℝ}
    (hh : EquiMean.BddMeas Ch h) (hk : EquiMean.BddMeas Cg k) (hlip : LipBound K k) :
    Tendsto (fun m : ℕ => (lam / 2) ^ m * ∫ x in Ioo (0:ℝ) 1, (EquiMean.S lam)^[m] h x * k x)
      atTop (𝓝 ((∫ x in Ioo (0:ℝ) 1, h x) * ∫ y, k y ∂(nu lam))) := by
  obtain ⟨c, hc⟩ := tendsto_const hlam hlip
  rw [const_eq_integral_nu hlam hlip hc]
  exact EquiMean.equidistribution_in_mean hlam hh hk hlip hc

end InvariantMeasure
end KnotGame
