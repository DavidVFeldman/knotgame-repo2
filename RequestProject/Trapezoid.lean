import RequestProject.Sqrt2
import RequestProject.Mahler

/-!
# T39 — the trapezoid at `λ = √2` (paper `prop:trapezoid`)

The backward form of the game is the iterated function system
`{r x, r x + (1−r)}` with `r = 1/λ`; by `Mahler.itinerary_tsum` a knot whose
orbit along the itinerary `ε` stays in `[0,1]` is exactly

  `(1 − r) ∑_{j ≥ 0} ε_j r^j`,

so the *backward measure* is the law of that series when the bits `ε_j` are
fair and independent.  At `λ = √2` we have `r² = 1/2`, so splitting the series
over even and odd `j` writes it as a sum of two pieces, each of which is
`(1 − r)` (respectively `(1 − r) r`) times a base-`1/2` series with fair bits,
i.e. a uniform variable on `[0, 2]` rescaled.  The two ranges are
`[0, 2 − √2]` and `[0, √2 − 1]`, and the law is the convolution of the two
uniform laws: the trapezoidal density that rises linearly on `[0, √2 − 1]`,
is constant at `(2 + √2)/2` on `[√2 − 1, 2 − √2]`, and falls linearly on
`[2 − √2, 1]`.

This file certifies:

* `bval_split` — the even/odd splitting of the series at `λ = √2`, with the
  two pieces `evenPart` and `oddPart`;
* `evenPart_mem_Icc`, `oddPart_mem_Icc` — their exact ranges `[0, 2 − √2]` and
  `[0, √2 − 1]`;
* `unifSum_eq_withDensity` — for all `a b`, the pushforward of
  `(Lebesgue on (0,a)) × (Lebesgue on (0,b))` under `(u,v) ↦ u + v` has
  density `convDens a b`, the elementary convolution profile
  `max 0 (min a x − max 0 (x − b))`;
* `convDens_sqrt_two` — at `a = 2 − √2`, `b = √2 − 1` that profile is
  `(3√2 − 4) · trapDens`, `3√2 − 4 = a b` being the normalising constant;
* `trapezoid_law` — the sum of the two *normalised* uniforms is the measure
  with density `trapDens`, a probability measure
  (`isProbabilityMeasure_trapDens`);
* `trapezoid_of_split` — consequently, on any probability space carrying two
  variables `E`, `O` whose joint law is that product, the law of `E + O` is
  the trapezoid.

## Conventions and what is *not* proved (SCRUPLES)

* **The missing link is the independence and uniformity of the two pieces.**
  Nothing here proves that, for fair independent bits `ε_j`, the even-indexed
  and odd-indexed sub-series are independent and uniformly distributed.  That
  step needs the law of the bit sequence as a measure (an infinite product, or
  equivalently Lebesgue measure on `[0,1)` read through binary digits) and a
  de-interleaving measure isomorphism; it is not formalised.  It enters
  `trapezoid_of_split` as an explicit hypothesis on the joint law, so the
  final statement is honest: *given* the split into independent uniforms, the
  law is the trapezoid.  Everything else — the algebraic splitting, the two
  ranges, and the whole convolution computation — is proved outright.
* The uniform laws are taken on the **open** intervals `(0,a)`, `(0,b)`; the
  endpoints are Lebesgue-null, so this is the same measure as on `[0,a]`.
* `trapDens` is a genuine pointwise density with respect to Lebesgue measure,
  written with `if`s; it agrees with the paper's piecewise description at
  every point, the breakpoints being assigned to the lower piece (immaterial,
  the breakpoints being null).
* `convDens a b` is stated for arbitrary real `a, b`; for `a, b > 0` it is the
  usual trapezoid, and the general form is what makes the proof of
  `unifSum_eq_withDensity` unconditional.
-/

namespace KnotGame
namespace Trapezoid

open MeasureTheory Set Sqrt2 Ternary
open scoped ENNReal

/-! ### 1. The even/odd splitting of the backward series at `λ = √2` -/

/-- The value of the backward series with bits `eps` at `λ = √2`; by
`Mahler.itinerary_tsum` this is the knot whose forward itinerary is `eps`. -/
noncomputable def bval (eps : ℕ → Fin 2) : ℝ :=
  (1 - r lam2) * ∑' k : ℕ, ((eps k : ℕ) : ℝ) * (r lam2) ^ k

/-- The contribution of the even-indexed bits. -/
noncomputable def evenPart (eps : ℕ → Fin 2) : ℝ :=
  (1 - r lam2) * ∑' i : ℕ, ((eps (2 * i) : ℕ) : ℝ) * (1 / 2 : ℝ) ^ i

/-- The contribution of the odd-indexed bits. -/
noncomputable def oddPart (eps : ℕ → Fin 2) : ℝ :=
  (1 - r lam2) * (r lam2) * ∑' i : ℕ, ((eps (2 * i + 1) : ℕ) : ℝ) * (1 / 2 : ℝ) ^ i

lemma r_lam2_sq : (r lam2) ^ 2 = 1 / 2 := by
  rw [r_lam2]
  nlinarith [lam2_sq, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

lemma summable_half (c : ℕ → Fin 2) :
    Summable (fun i : ℕ => ((c i : ℕ) : ℝ) * (1 / 2 : ℝ) ^ i) := by
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (summable_geometric_of_lt_one (by norm_num) (by norm_num : (1/2:ℝ) < 1))
  have hc : ((c k : ℕ) : ℝ) ≤ 1 := by
    have : (c k : ℕ) ≤ 1 := Nat.lt_succ_iff.mp (c k).isLt
    exact_mod_cast this
  have hp : (0:ℝ) < (1/2 : ℝ) ^ k := by positivity
  nlinarith

lemma tsum_half_nonneg (c : ℕ → Fin 2) :
    0 ≤ ∑' i : ℕ, ((c i : ℕ) : ℝ) * (1 / 2 : ℝ) ^ i :=
  tsum_nonneg (fun i => by positivity)

lemma tsum_half_le_two (c : ℕ → Fin 2) :
    ∑' i : ℕ, ((c i : ℕ) : ℝ) * (1 / 2 : ℝ) ^ i ≤ 2 := by
  have hgeo : Summable (fun i : ℕ => (1/2 : ℝ) ^ i) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hle : ∑' i : ℕ, ((c i : ℕ) : ℝ) * (1 / 2 : ℝ) ^ i ≤ ∑' i : ℕ, (1/2 : ℝ) ^ i := by
    refine (summable_half c).tsum_le_tsum (fun i => ?_) hgeo
    have hc : ((c i : ℕ) : ℝ) ≤ 1 := by
      have : (c i : ℕ) ≤ 1 := Nat.lt_succ_iff.mp (c i).isLt
      exact_mod_cast this
    have hp : (0:ℝ) < (1/2 : ℝ) ^ i := by positivity
    nlinarith
  have : ∑' i : ℕ, (1/2 : ℝ) ^ i = 2 := by
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  linarith [hle, this.le, this.ge]

/-- **The even/odd splitting.**  At `λ = √2` the backward series is the sum of
an even part and an odd part, each a base-`1/2` series. -/
theorem bval_split (eps : ℕ → Fin 2) : bval eps = evenPart eps + oddPart eps := by
  have hsum := summable_itinerary one_lt_lam2 eps
  have heven : (fun i : ℕ => ((eps (2 * i) : ℕ) : ℝ) * (r lam2) ^ (2 * i))
      = fun i : ℕ => ((eps (2 * i) : ℕ) : ℝ) * (1 / 2 : ℝ) ^ i := by
    funext i
    rw [pow_mul, r_lam2_sq]
  have hodd : (fun i : ℕ => ((eps (2 * i + 1) : ℕ) : ℝ) * (r lam2) ^ (2 * i + 1))
      = fun i : ℕ => (r lam2) * (((eps (2 * i + 1) : ℕ) : ℝ) * (1 / 2 : ℝ) ^ i) := by
    funext i
    rw [pow_succ, pow_mul, r_lam2_sq]
    ring
  have hse : Summable (fun i : ℕ => ((eps (2 * i) : ℕ) : ℝ) * (r lam2) ^ (2 * i)) := by
    rw [heven]; exact summable_half _
  have hso : Summable (fun i : ℕ => ((eps (2 * i + 1) : ℕ) : ℝ) * (r lam2) ^ (2 * i + 1)) := by
    rw [hodd]; exact (summable_half _).mul_left _
  have hsplit := tsum_even_add_odd (f := fun k : ℕ => ((eps k : ℕ) : ℝ) * (r lam2) ^ k) hse hso
  rw [bval, ← hsplit, heven, hodd, tsum_mul_left, evenPart, oddPart]
  ring

lemma evenPart_mem_Icc (eps : ℕ → Fin 2) : evenPart eps ∈ Icc (0:ℝ) (2 - Real.sqrt 2) := by
  have hr : r lam2 = Real.sqrt 2 / 2 := r_lam2
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hlt : Real.sqrt 2 < 1.5 := by nlinarith [Real.sqrt_nonneg 2]
  have h0 := tsum_half_nonneg (fun i => eps (2 * i))
  have h2 := tsum_half_le_two (fun i => eps (2 * i))
  constructor
  · rw [evenPart, hr]
    have : (0:ℝ) ≤ 1 - Real.sqrt 2 / 2 := by linarith
    positivity
  · rw [evenPart, hr]
    nlinarith

lemma oddPart_mem_Icc (eps : ℕ → Fin 2) : oddPart eps ∈ Icc (0:ℝ) (Real.sqrt 2 - 1) := by
  have hr : r lam2 = Real.sqrt 2 / 2 := r_lam2
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hlt : Real.sqrt 2 < 1.5 := by nlinarith [Real.sqrt_nonneg 2]
  have hgt : (1:ℝ) < Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
  have h0 := tsum_half_nonneg (fun i => eps (2 * i + 1))
  have h2 := tsum_half_le_two (fun i => eps (2 * i + 1))
  constructor
  · rw [oddPart, hr]
    have h1 : (0:ℝ) ≤ 1 - Real.sqrt 2 / 2 := by linarith
    have h2' : (0:ℝ) ≤ Real.sqrt 2 / 2 := by positivity
    positivity
  · rw [oddPart, hr]
    nlinarith

/-! ### 2. The convolution of two uniform laws -/

/-- The elementary convolution profile of the two intervals `(0,a)`, `(0,b)`:
the length of `(0,a) ∩ (x−b, x)`. -/
noncomputable def convDens (a b x : ℝ) : ℝ := max 0 (min a x - max 0 (x - b))

/-- The pushforward of `(Lebesgue on (0,a)) × (Lebesgue on (0,b))` under
addition.  Its total mass is `a b`; the normalised version is `unif a`
convolved with `unif b`, see `trapezoid_law`. -/
noncomputable def unifSum (a b : ℝ) : Measure ℝ :=
  Measure.map (fun p : ℝ × ℝ => p.1 + p.2)
    ((volume.restrict (Ioo 0 a)).prod (volume.restrict (Ioo 0 b)))

/-- The uniform probability measure on `(0,a)`. -/
noncomputable def unif (a : ℝ) : Measure ℝ := (ENNReal.ofReal a)⁻¹ • volume.restrict (Ioo 0 a)

lemma inner_convDens (a b x : ℝ) :
    ∫⁻ u, (Ioo (0:ℝ) a).indicator (fun _ => (1:ℝ≥0∞)) u *
        (Ioo (0:ℝ) b).indicator (fun _ => (1:ℝ≥0∞)) (x - u) = ENNReal.ofReal (convDens a b x) := by
  have hset : (fun u : ℝ => (Ioo (0:ℝ) a).indicator (fun _ => (1:ℝ≥0∞)) u *
      (Ioo (0:ℝ) b).indicator (fun _ => (1:ℝ≥0∞)) (x - u))
      = (Ioo (max 0 (x - b)) (min a x)).indicator (fun _ => (1:ℝ≥0∞)) := by
    funext u
    simp only [Set.indicator_apply, mem_Ioo, lt_min_iff, max_lt_iff, mul_ite, mul_one, mul_zero]
    split_ifs <;> simp_all <;> linarith
  rw [hset, lintegral_indicator_const measurableSet_Ioo, one_mul, Real.volume_Ioo]
  unfold convDens
  rcases le_or_gt (min a x - max 0 (x - b)) 0 with h | h
  · rw [max_eq_left h]
    simp [ENNReal.ofReal_eq_zero.mpr h]
  · rw [max_eq_right h.le]

/-- **The convolution formula.**  The law of the sum of two independent
uniform variables, before normalisation. -/
theorem unifSum_apply (a b : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    unifSum a b A = ∫⁻ x in A, ENNReal.ofReal (convDens a b x) := by
  classical
  set F : ℝ → ℝ≥0∞ := A.indicator (fun _ => 1) with hF
  set Ia : ℝ → ℝ≥0∞ := (Ioo (0:ℝ) a).indicator (fun _ => 1) with hIa
  set Ib : ℝ → ℝ≥0∞ := (Ioo (0:ℝ) b).indicator (fun _ => 1) with hIb
  have hmeas : Measurable (fun p : ℝ × ℝ => p.1 + p.2) := measurable_fst.add measurable_snd
  have hP : MeasurableSet ((fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' A) := hmeas hA
  have hFm : Measurable F := (measurable_one).indicator hA
  have hIam : Measurable Ia := (measurable_one).indicator measurableSet_Ioo
  have hIbm : Measurable Ib := (measurable_one).indicator measurableSet_Ioo
  have hFle : ∀ x, F x ≠ ∞ := by
    intro x; by_cases hx : x ∈ A <;> simp [hF, hx]
  have hIale : ∀ u, Ia u ≠ ∞ := by
    intro u; by_cases hu : u ∈ Ioo (0:ℝ) a <;> simp [hIa, hu]
  have h1 : unifSum a b A
      = ∫⁻ u, (volume.restrict (Ioo (0:ℝ) b)) {v | u + v ∈ A} ∂(volume.restrict (Ioo (0:ℝ) a)) := by
    rw [unifSum, Measure.map_apply hmeas hA, Measure.prod_apply hP]
    rfl
  have h2 : ∀ u : ℝ, (volume.restrict (Ioo (0:ℝ) b)) {v | u + v ∈ A} = ∫⁻ v, Ib v * F (u + v) := by
    intro u
    have hs : MeasurableSet {v : ℝ | u + v ∈ A} := (measurable_const_add u) hA
    have hind : ({v : ℝ | u + v ∈ A} ∩ Ioo (0:ℝ) b).indicator (fun _ => (1:ℝ≥0∞))
        = fun v => Ib v * F (u + v) := by
      funext v
      simp only [hF, hIb, Set.indicator_apply, mem_inter_iff, mem_setOf_eq, mul_ite, mul_one,
        mul_zero]
      split_ifs <;> simp_all
    rw [Measure.restrict_apply hs, ← hind, lintegral_indicator_const (hs.inter measurableSet_Ioo) 1,
      one_mul]
  have h3 : unifSum a b A = ∫⁻ u, Ia u * ∫⁻ v, Ib v * F (u + v) := by
    rw [h1]
    simp_rw [h2]
    rw [← lintegral_indicator measurableSet_Ioo]
    congr 1
    funext u
    simp only [hIa, Set.indicator_apply]
    split_ifs <;> simp
  have h4 : ∀ u : ℝ, ∫⁻ v, Ib v * F (u + v) = ∫⁻ x, Ib (x - u) * F x := by
    intro u
    have hshift := lintegral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun x => Ib (x - u) * F x) u
    rw [← hshift]
    congr 1
    funext v
    congr 1 <;> ring_nf
  have h5 : unifSum a b A = ∫⁻ u, ∫⁻ x, Ia u * (Ib (x - u) * F x) := by
    rw [h3]
    congr 1
    funext u
    rw [h4 u, lintegral_const_mul' _ _ (hIale u)]
  have hum : Measurable (Function.uncurry fun u x => Ia u * (Ib (x - u) * F x)) :=
    (hIam.comp measurable_fst).mul
      ((hIbm.comp (measurable_snd.sub measurable_fst)).mul (hFm.comp measurable_snd))
  have h6 : unifSum a b A = ∫⁻ x, ∫⁻ u, Ia u * (Ib (x - u) * F x) := by
    rw [h5]
    exact lintegral_lintegral_swap hum.aemeasurable
  have h7 : ∀ x : ℝ, ∫⁻ u, Ia u * (Ib (x - u) * F x) = ENNReal.ofReal (convDens a b x) * F x := by
    intro x
    have hre : ∀ u : ℝ, Ia u * (Ib (x - u) * F x) = (Ia u * Ib (x - u)) * F x := by
      intro u; ring
    simp_rw [hre]
    rw [lintegral_mul_const' _ _ (hFle x), inner_convDens a b x]
  rw [h6]
  simp_rw [h7]
  rw [← lintegral_indicator hA]
  congr 1 with x
  by_cases hx : x ∈ A <;> simp [hF, hx]

theorem unifSum_eq_withDensity (a b : ℝ) :
    unifSum a b = volume.withDensity (fun x => ENNReal.ofReal (convDens a b x)) := by
  refine Measure.ext fun A hA => ?_
  rw [unifSum_apply a b hA, withDensity_apply _ hA]

/-! ### 3. The trapezoid at `λ = √2` -/

/-- The trapezoidal density: `0` outside `[0,1]`, rising on `[0, √2−1]`,
constant at `(2+√2)/2` on `[√2−1, 2−√2]`, falling on `[2−√2, 1]`.  The slope
is `1/(3√2−4)`, the reciprocal of the product of the two interval lengths. -/
noncomputable def trapDens (x : ℝ) : ℝ :=
  if x ≤ 0 then 0
  else if x ≤ Real.sqrt 2 - 1 then x / (3 * Real.sqrt 2 - 4)
  else if x ≤ 2 - Real.sqrt 2 then (2 + Real.sqrt 2) / 2
  else if x ≤ 1 then (1 - x) / (3 * Real.sqrt 2 - 4)
  else 0

lemma measurable_trapDens : Measurable trapDens := by
  unfold trapDens
  refine Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const ?_
  refine Measurable.ite (measurableSet_le measurable_id measurable_const) (by fun_prop) ?_
  refine Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const ?_
  exact Measurable.ite (measurableSet_le measurable_id measurable_const) (by fun_prop)
    measurable_const

lemma trapDens_nonneg (x : ℝ) : 0 ≤ trapDens x := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h1 : (1.41:ℝ) < Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
  have h2 : Real.sqrt 2 < 1.42 := by nlinarith [Real.sqrt_nonneg 2]
  have hden : (0:ℝ) < 3 * Real.sqrt 2 - 4 := by linarith
  unfold trapDens
  split_ifs with c1 c2 c3 c4
  · exact le_refl 0
  · exact div_nonneg (by linarith) hden.le
  · linarith
  · exact div_nonneg (by linarith) hden.le
  · exact le_refl 0

/-- At `a = 2 − √2`, `b = √2 − 1` the convolution profile is
`(3√2 − 4) · trapDens`, and `3√2 − 4 = (2 − √2)(√2 − 1)`. -/
theorem convDens_sqrt_two (x : ℝ) :
    convDens (2 - Real.sqrt 2) (Real.sqrt 2 - 1) x = (3 * Real.sqrt 2 - 4) * trapDens x := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h1 : (1.41:ℝ) < Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
  have h2 : Real.sqrt 2 < 1.42 := by nlinarith [Real.sqrt_nonneg 2]
  have hden : (0:ℝ) < 3 * Real.sqrt 2 - 4 := by linarith
  unfold convDens trapDens
  split_ifs with c1 c2 c3 c4
  · rw [min_eq_right (by linarith), max_eq_left (by linarith : x - (Real.sqrt 2 - 1) ≤ 0),
      sub_zero, max_eq_left (by linarith)]
    ring
  · rw [min_eq_right (by linarith), max_eq_left (by linarith : x - (Real.sqrt 2 - 1) ≤ 0),
      sub_zero, max_eq_right (by linarith)]
    field_simp
  · rw [min_eq_right (by linarith),
      max_eq_right (by linarith : (0:ℝ) ≤ x - (Real.sqrt 2 - 1)),
      show x - (x - (Real.sqrt 2 - 1)) = Real.sqrt 2 - 1 by ring,
      max_eq_right (by linarith)]
    nlinarith
  · rw [min_eq_left (by linarith), max_eq_right (by linarith : (0:ℝ) ≤ x - (Real.sqrt 2 - 1)),
      show 2 - Real.sqrt 2 - (x - (Real.sqrt 2 - 1)) = 1 - x by ring,
      max_eq_right (by linarith)]
    field_simp
  · rw [min_eq_left (by linarith), max_eq_right (by linarith : (0:ℝ) ≤ x - (Real.sqrt 2 - 1)),
      show 2 - Real.sqrt 2 - (x - (Real.sqrt 2 - 1)) = 1 - x by ring,
      max_eq_left (by linarith)]
    ring

lemma unif_univ {a : ℝ} (ha : 0 < a) : unif a univ = 1 := by
  rw [unif, Measure.smul_apply, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero,
    smul_eq_mul, ENNReal.inv_mul_cancel (by simpa using ha) ENNReal.ofReal_ne_top]

instance isProbabilityMeasure_unif {a : ℝ} [Fact (0 < a)] : IsProbabilityMeasure (unif a) :=
  ⟨unif_univ (Fact.out)⟩

/-- **The trapezoid law.**  The sum of independent uniforms on `(0, 2−√2)` and
`(0, √2−1)` has the trapezoidal density. -/
theorem trapezoid_law :
    Measure.map (fun p : ℝ × ℝ => p.1 + p.2)
        ((unif (2 - Real.sqrt 2)).prod (unif (Real.sqrt 2 - 1)))
      = volume.withDensity (fun x => ENNReal.ofReal (trapDens x)) := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h1 : (1.41:ℝ) < Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
  have h2 : Real.sqrt 2 < 1.42 := by nlinarith [Real.sqrt_nonneg 2]
  have hden : (0:ℝ) < 3 * Real.sqrt 2 - 4 := by linarith
  have hab : (2 - Real.sqrt 2) * (Real.sqrt 2 - 1) = 3 * Real.sqrt 2 - 4 := by nlinarith
  have hprod : ((unif (2 - Real.sqrt 2)).prod (unif (Real.sqrt 2 - 1)))
      = ((ENNReal.ofReal (2 - Real.sqrt 2))⁻¹ * (ENNReal.ofReal (Real.sqrt 2 - 1))⁻¹) •
          ((volume.restrict (Ioo 0 (2 - Real.sqrt 2))).prod
            (volume.restrict (Ioo 0 (Real.sqrt 2 - 1)))) := by
    rw [unif, unif, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  rw [hprod, Measure.map_smul, ← unifSum, unifSum_eq_withDensity]
  have hcd : (fun x => ENNReal.ofReal (convDens (2 - Real.sqrt 2) (Real.sqrt 2 - 1) x))
      = fun x => ENNReal.ofReal (3 * Real.sqrt 2 - 4) * ENNReal.ofReal (trapDens x) := by
    funext x
    rw [convDens_sqrt_two x, ENNReal.ofReal_mul hden.le]
  rw [hcd]
  have hwd : volume.withDensity
      (fun x => ENNReal.ofReal (3 * Real.sqrt 2 - 4) * ENNReal.ofReal (trapDens x))
      = ENNReal.ofReal (3 * Real.sqrt 2 - 4) •
          volume.withDensity (fun x => ENNReal.ofReal (trapDens x)) := by
    rw [← withDensity_smul _ (measurable_trapDens.ennreal_ofReal)]
    rfl
  rw [hwd, smul_smul]
  have hmul : (ENNReal.ofReal (2 - Real.sqrt 2))⁻¹ * (ENNReal.ofReal (Real.sqrt 2 - 1))⁻¹ *
      ENNReal.ofReal (3 * Real.sqrt 2 - 4) = 1 := by
    rw [← ENNReal.mul_inv (Or.inl (by simpa using (by linarith : (0:ℝ) < 2 - Real.sqrt 2)))
        (Or.inl ENNReal.ofReal_ne_top),
      ← ENNReal.ofReal_mul (by linarith), hab,
      ENNReal.inv_mul_cancel (by simpa using hden) ENNReal.ofReal_ne_top]
  rw [hmul, one_smul]

instance isProbabilityMeasure_trapDens :
    IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (trapDens x))) := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h1 : (1.41:ℝ) < Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
  have h2 : Real.sqrt 2 < 1.42 := by nlinarith [Real.sqrt_nonneg 2]
  haveI : Fact (0 < 2 - Real.sqrt 2) := ⟨by linarith⟩
  haveI : Fact (0 < Real.sqrt 2 - 1) := ⟨by linarith⟩
  rw [← trapezoid_law]
  exact Measure.isProbabilityMeasure_map (measurable_fst.add measurable_snd).aemeasurable

/-- **The trapezoid, packaged.**  On any space carrying two variables whose
joint law is the product of the two uniforms, the law of their sum is the
trapezoid.  (That the even and odd parts of the backward series at `λ = √2`
do have that joint law is the step this file does not formalise; see the
scruples at the head of the file.) -/
theorem trapezoid_of_split {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {E O : Ω → ℝ} (hE : Measurable E) (hO : Measurable O)
    (hEO : Measure.map (fun w => (E w, O w)) μ
      = (unif (2 - Real.sqrt 2)).prod (unif (Real.sqrt 2 - 1))) :
    Measure.map (fun w => E w + O w) μ
      = volume.withDensity (fun x => ENNReal.ofReal (trapDens x)) := by
  have hcomp : (fun w => E w + O w) = (fun p : ℝ × ℝ => p.1 + p.2) ∘ (fun w => (E w, O w)) := rfl
  rw [hcomp, ← Measure.map_map (measurable_fst.add measurable_snd) (hE.prodMk hO), hEO,
    trapezoid_law]

end Trapezoid
end KnotGame
