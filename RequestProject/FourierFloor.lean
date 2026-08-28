import RequestProject.Lucas
import RequestProject.Basic

/-!
# T29a — the Fourier floor at the golden ratio (paper `sec:conjugate`)

The backward form of the game (Remark `rem:overlap`) is the iterated function
system `{r x, r x + (1-r)}`, whose invariant measure is the Bernoulli
convolution `ν_r`.  Its Fourier transform is the classical cosine product

  `|ν̂_r(ξ)| = ∏_{j≥0} |cos(π (1-r) r^j ξ)|`,

and the paper evaluates it along the frequencies `ξ_N = λ^N/(1-r)`, where
every argument becomes `π λ^{N-j}`, so that

  `|ν̂_r(ξ_N)| = ∏_{m ≤ N} |cos(π λ^m)| → ∏_{m ∈ ℤ} |cos(π λ^m)|`.

This file proves, at `λ = φ`:

* **(i)** the algebraic identity `(1-r) r^j ξ_N = λ^{N-j}` and the resulting
  identification of the two products, for any `λ > 1` (`cosProd_xi`);
* **(ii)** the distance bound `‖φ^m‖ ≤ φ^{-m}` — this is
  `RequestProject.Lucas`, via the Lucas trace identity;
* **(iii)** that the two-sided product `∏_{m ∈ ℤ} |cos(π φ^m)|` converges to a
  **positive** limit (`multipliable_goldenFac`, `goldenFourierFloor_pos`);
* **(iv)** that `|ν̂_{r(φ)}(ξ_N)| → ∏_{m ∈ ℤ} |cos(π φ^m)|` as `N → ∞`
  (`tendsto_cosProd_xi_golden`).

## Conventions (SCRUPLES)

* **The measure `ν_r` is not constructed.**  `cosProd rr ξ` is *defined* to be
  the cosine product `∏_{j≥0}|cos(π (1-rr) rr^j ξ)|`, which is the classical
  closed form of `|ν̂_{rr}(ξ)|` for the Bernoulli convolution; the statements
  below are about that product.  Nothing here asserts the identification with
  a Fourier transform of a measure, which is not part of the commission.
* **Rendering of the product (commission: "record the choice").**  The
  two-sided product is rendered as Mathlib's unconditional `∏' m : ℤ`
  (`tprod`), and its convergence as `Multipliable`.  Convergence is obtained
  by the log-summability route: all factors are positive, the logarithms are
  summable over `ℤ`, and `Real.multipliable_of_summable_log` then gives
  `Multipliable`, with `∏' = exp (∑' log)`, which is manifestly positive.
  The summability of the logarithms comes from the explicit bound
  `|log|cos(π φ^m)|| ≤ π² (φ^{-2})^{|m|}` for `|m|` large, itself a
  consequence of (ii) for `m ≥ 0` and of `φ^m → 0` for `m ≤ 0`.
* The limit (iv) is stated for the partial products
  `∏' j : ℕ, |cos(π φ^{N-j})|`, which by (i) is exactly `cosProd (r φ) (ξ_N)`,
  and is the paper's `∏_{m ≤ N}|cos(π λ^m)|`.
* Positivity of the individual factors rests on the irrationality of `φ^m`
  for `m ≠ 0` (`RequestProject.Lucas`), which forbids `φ^m ∈ ℤ + 1/2`.
-/

namespace KnotGame
namespace Fourier

open Real Filter Topology
open scoped Real

set_option maxHeartbeats 1000000

/-! ## (i) The algebraic identity -/

/-- The frequency `ξ_N = λ^N / (1 - r)` of the paper. -/
noncomputable def xi (lam : ℝ) (N : ℕ) : ℝ := lam ^ N / (1 - r lam)

/-- **T29a(i)**: along `ξ_N`, the `j`-th argument of the cosine product is
`λ^{N-j}`. -/
theorem xi_scaling {lam : ℝ} (h : 1 < lam) (N j : ℕ) :
    (1 - r lam) * r lam ^ j * xi lam N = lam ^ ((N : ℤ) - j) := by
  have hlam0 : (0 : ℝ) < lam := lt_trans zero_lt_one h
  have hg : (1 : ℝ) - lam⁻¹ ≠ 0 := by
    have h1 : lam⁻¹ < 1 := r_lt_one lam h
    linarith
  show (1 - lam⁻¹) * lam⁻¹ ^ j * (lam ^ N / (1 - lam⁻¹)) = lam ^ ((N : ℤ) - j)
  rw [zpow_sub₀ (ne_of_gt hlam0), zpow_natCast, zpow_natCast,
    mul_comm (1 - lam⁻¹) (lam⁻¹ ^ j), mul_assoc, mul_div_assoc',
    mul_comm (1 - lam⁻¹) (lam ^ N), mul_div_assoc, div_self hg, mul_one, inv_pow,
    mul_comm, div_eq_mul_inv]

/-- The cosine product `∏_{j≥0} |cos(π (1-rr) rr^j ξ)|`, the classical closed
form of `|ν̂_{rr}(ξ)|` for the Bernoulli convolution with ratio `rr`. -/
noncomputable def cosProd (rr xi : ℝ) : ℝ :=
  ∏' j : ℕ, |Real.cos (π * ((1 - rr) * rr ^ j * xi))|

/-- The two-sided factor `|cos(π λ^m)|`. -/
noncomputable def cosFac (lam : ℝ) (m : ℤ) : ℝ := |Real.cos (π * lam ^ m)|

/-- **T29a(i)**, product form: at the frequency `ξ_N` the transform's product
is the product of the factors `|cos(π λ^m)|` over `m = N, N-1, N-2, …`. -/
theorem cosProd_xi {lam : ℝ} (h : 1 < lam) (N : ℕ) :
    cosProd (r lam) (xi lam N) = ∏' j : ℕ, cosFac lam ((N : ℤ) - j) := by
  refine tprod_congr (fun j => ?_)
  rw [cosFac, xi_scaling h N j]

/-! ## The golden factors -/

/-- The factor `|cos(π φ^m)|` at the golden ratio. -/
noncomputable def goldenFac (m : ℤ) : ℝ := cosFac Real.goldenRatio m

lemma goldenFac_le_one (m : ℤ) : goldenFac m ≤ 1 := by
  simpa [goldenFac, cosFac] using Real.abs_cos_le_one (π * Real.goldenRatio ^ m)

lemma goldenFac_nonneg (m : ℤ) : 0 ≤ goldenFac m := abs_nonneg _

/-- Every nonzero power of `φ` is irrational. -/
lemma irrational_goldenRatio_zpow {m : ℤ} (hm : m ≠ 0) :
    Irrational (Real.goldenRatio ^ m) := by
  rcases lt_or_gt_of_ne hm with hneg | hpos
  · have hk : ∃ k : ℕ, -m = (k : ℤ) + 1 := ⟨(-m - 1).toNat, by omega⟩
    obtain ⟨k, hk⟩ := hk
    have : Real.goldenRatio ^ m = (Real.goldenRatio ^ (k + 1 : ℕ))⁻¹ := by
      have : m = -((k : ℤ) + 1) := by omega
      rw [this, zpow_neg]
      norm_cast
    rw [this]
    exact (irrational_goldenRatio_pow_succ k).inv
  · have hk : ∃ k : ℕ, m = (k : ℤ) + 1 := ⟨(m - 1).toNat, by omega⟩
    obtain ⟨k, hk⟩ := hk
    have : Real.goldenRatio ^ m = Real.goldenRatio ^ (k + 1 : ℕ) := by
      rw [hk]; norm_cast
    rw [this]
    exact irrational_goldenRatio_pow_succ k

/-- `cos (π x) = 0` exactly when `x` is a half-integer. -/
lemma cos_pi_mul_eq_zero_iff (x : ℝ) :
    Real.cos (π * x) = 0 ↔ ∃ n : ℤ, x = n + 1 / 2 := by
  rw [Real.cos_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hpi : (0 : ℝ) < π := Real.pi_pos
    field_simp at hn
    nlinarith [hn, hpi]
  · rintro ⟨n, rfl⟩
    exact ⟨n, by ring⟩

/-- **Every factor is positive.** -/
lemma goldenFac_pos (m : ℤ) : 0 < goldenFac m := by
  rw [goldenFac, cosFac, abs_pos]
  intro hzero
  obtain ⟨n, hn⟩ := (cos_pi_mul_eq_zero_iff _).mp hzero
  by_cases hm : m = 0
  · subst hm
    rw [zpow_zero] at hn
    have : (2 : ℝ) * n = 1 := by linarith
    have : (2 : ℤ) * n = 1 := by exact_mod_cast this
    omega
  · have hirr := irrational_goldenRatio_zpow hm
    exact hirr.ne_rat ((n : ℚ) + 1 / 2) (by rw [hn]; push_cast; ring)

/-! ## The quantitative bound -/

/-- Notation for the conjugate modulus `c(φ) = φ⁻¹`. -/
noncomputable def gc : ℝ := Real.goldenRatio⁻¹

lemma gc_eq : gc = Real.goldenRatio⁻¹ := rfl

lemma gc_pos : 0 < gc := goldenRatio_inv_pos
lemma gc_lt_one : gc < 1 := goldenRatio_inv_lt_one

lemma gc_sq_pos : 0 < gc ^ 2 := pow_pos gc_pos 2
lemma gc_sq_lt_one : gc ^ 2 < 1 := by nlinarith [gc_pos, gc_lt_one]

/-- Each power of `φ` is within `c^{|m|}` of an integer: for `m ≥ 0` this is
the Lucas trace identity (T29a(ii)), for `m < 0` it is `φ^m → 0`. -/
lemma exists_int_close (m : ℤ) :
    ∃ n : ℤ, |Real.goldenRatio ^ m - (n : ℝ)| ≤ gc ^ m.natAbs := by
  rcases le_or_gt 0 m with hm | hm
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    refine ⟨lucas k, ?_⟩
    have hn : ((k : ℤ)).natAbs = k := by omega
    rw [zpow_natCast, hn, abs_goldenRatio_pow_sub_lucas k, gc_eq]
  · refine ⟨0, ?_⟩
    have hzp : Real.goldenRatio ^ m = gc ^ m.natAbs := by
      have hm' : Real.goldenRatio ^ m = Real.goldenRatio ^ (-(m.natAbs : ℤ)) := by
        congr 1
        omega
      rw [hm', zpow_neg, ← inv_zpow, zpow_natCast, gc_eq]
    rw [hzp, Int.cast_zero, sub_zero, abs_of_pos (pow_pos gc_pos _)]

/-- `|cos (π x)|` is unchanged by an integer shift of `x`. -/
lemma abs_cos_pi_sub_int (x : ℝ) (n : ℤ) :
    |Real.cos (π * x)| = |Real.cos (π * (x - n))| := by
  have h : π * (x - n) = π * x - n * π := by ring
  rw [h, Real.cos_sub, Real.sin_int_mul_pi, Real.cos_int_mul_pi, mul_zero, add_zero,
    abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, mul_one]

/-- `1 - |cos (π d)| ≤ π² d² / 2`. -/
lemma one_sub_abs_cos_le (d : ℝ) :
    1 - |Real.cos (π * d)| ≤ π ^ 2 * d ^ 2 / 2 := by
  have h1 : Real.cos (π * d) ≤ |Real.cos (π * d)| := le_abs_self _
  have h2 : 1 - (π * d) ^ 2 / 2 ≤ Real.cos (π * d) := Real.one_sub_sq_div_two_le_cos
  nlinarith [h1, h2]

/-- The deficit of a golden factor. -/
lemma one_sub_goldenFac_le (m : ℤ) :
    1 - goldenFac m ≤ π ^ 2 * (gc ^ 2) ^ m.natAbs / 2 := by
  obtain ⟨n, hn⟩ := exists_int_close m
  have hshift : goldenFac m = |Real.cos (π * (Real.goldenRatio ^ m - n))| := by
    rw [goldenFac, cosFac]
    exact abs_cos_pi_sub_int _ n
  have hb := one_sub_abs_cos_le (Real.goldenRatio ^ m - n)
  rw [← hshift] at hb
  refine le_trans hb ?_
  have hsq : (Real.goldenRatio ^ m - (n : ℝ)) ^ 2 ≤ (gc ^ m.natAbs) ^ 2 := by
    have h0 : (0 : ℝ) ≤ gc ^ m.natAbs := le_of_lt (pow_pos gc_pos _)
    nlinarith [abs_nonneg (Real.goldenRatio ^ m - (n : ℝ)), sq_abs
      (Real.goldenRatio ^ m - (n : ℝ)), hn]
  have hpow : (gc ^ m.natAbs) ^ 2 = (gc ^ 2) ^ m.natAbs := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have hpi : (0 : ℝ) < π ^ 2 := by positivity
  rw [← hpow]
  nlinarith [hsq, hpi]

/-- If `y ∈ [1/2, 1]` then `|log y| ≤ 2 (1 - y)`. -/
lemma abs_log_le_of_mem (y : ℝ) (h1 : 1 / 2 ≤ y) (h2 : y ≤ 1) :
    |Real.log y| ≤ 2 * (1 - y) := by
  have hy : 0 < y := by linarith
  have hlog : Real.log y ≤ 0 := Real.log_nonpos (by linarith) h2
  rw [abs_of_nonpos hlog]
  have h3 : Real.log y⁻¹ ≤ y⁻¹ - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_inv] at h3
  have h4 : y⁻¹ - 1 = (1 - y) / y := by field_simp
  rw [h4] at h3
  have h5 : (1 - y) / y ≤ 2 * (1 - y) := by
    rw [div_le_iff₀ hy]
    nlinarith
  linarith

/-- **The log bound.**  Once `π² c^{2|m|} ≤ 1`, the logarithm of the golden
factor is bounded by `π² c^{2|m|}`. -/
lemma abs_log_goldenFac_le {m : ℤ} (h : π ^ 2 * (gc ^ 2) ^ m.natAbs ≤ 1) :
    |Real.log (goldenFac m)| ≤ π ^ 2 * (gc ^ 2) ^ m.natAbs := by
  have hdef := one_sub_goldenFac_le m
  have hhalf : 1 / 2 ≤ goldenFac m := by linarith
  have hle := abs_log_le_of_mem _ hhalf (goldenFac_le_one m)
  linarith

/-! ## Summability of the logarithms -/

lemma summable_geom_bound : Summable (fun n : ℕ => π ^ 2 * (gc ^ 2) ^ n) :=
  (summable_geometric_of_lt_one (le_of_lt gc_sq_pos) gc_sq_lt_one).mul_left _

/-- Beyond a fixed index the log bound applies. -/
lemma exists_threshold : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → π ^ 2 * (gc ^ 2) ^ n ≤ 1 := by
  have htend : Tendsto (fun n : ℕ => π ^ 2 * (gc ^ 2) ^ n) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ => (gc ^ 2) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt gc_sq_pos) gc_sq_lt_one
    simpa using h0.const_mul (π ^ 2)
  have h := htend.eventually_le_const (show (0:ℝ) < 1 by norm_num)
  rw [eventually_atTop] at h
  obtain ⟨n₀, hn₀⟩ := h
  exact ⟨n₀, hn₀⟩

lemma summable_log_goldenFac_nat : Summable (fun n : ℕ => Real.log (goldenFac n)) := by
  obtain ⟨n₀, hn₀⟩ := exists_threshold
  rw [← summable_nat_add_iff n₀]
  refine Summable.of_norm_bounded (g := fun n : ℕ => π ^ 2 * (gc ^ 2) ^ (n + n₀))
    ((summable_nat_add_iff n₀).mpr summable_geom_bound) (fun n => ?_)
  have hnat : ((n + n₀ : ℕ) : ℤ).natAbs = n + n₀ := by omega
  have h := abs_log_goldenFac_le (m := ((n + n₀ : ℕ) : ℤ)) (by rw [hnat]; exact hn₀ _ (by omega))
  rw [hnat] at h
  rw [Real.norm_eq_abs]
  exact h

lemma summable_log_goldenFac_neg :
    Summable (fun n : ℕ => Real.log (goldenFac (-((n : ℤ) + 1)))) := by
  obtain ⟨n₀, hn₀⟩ := exists_threshold
  rw [← summable_nat_add_iff n₀]
  refine Summable.of_norm_bounded (g := fun n : ℕ => π ^ 2 * (gc ^ 2) ^ (n + n₀ + 1))
    ((summable_nat_add_iff (n₀ + 1)).mpr summable_geom_bound) (fun n => ?_)
  have hnat : (-(((n + n₀ : ℕ) : ℤ) + 1)).natAbs = n + n₀ + 1 := by omega
  have h := abs_log_goldenFac_le (m := -(((n + n₀ : ℕ) : ℤ) + 1))
    (by rw [hnat]; exact hn₀ _ (by omega))
  rw [hnat] at h
  rw [Real.norm_eq_abs]
  exact h

/-- The logarithms of the golden factors are summable over `ℤ`. -/
theorem summable_log_goldenFac : Summable (fun m : ℤ => Real.log (goldenFac m)) :=
  Summable.of_nat_of_neg_add_one summable_log_goldenFac_nat summable_log_goldenFac_neg

/-! ## (iii) Convergence and positivity of the two-sided product -/

/-- **T29a(iii)**, convergence: the two-sided product `∏_{m ∈ ℤ}|cos(π φ^m)|`
converges (unconditionally). -/
theorem multipliable_goldenFac : Multipliable goldenFac :=
  Real.multipliable_of_summable_log goldenFac_pos summable_log_goldenFac

/-- The value of the two-sided product is the exponential of the sum of the
logarithms. -/
theorem tprod_goldenFac_eq_exp :
    ∏' m : ℤ, goldenFac m = Real.exp (∑' m : ℤ, Real.log (goldenFac m)) :=
  (Real.rexp_tsum_eq_tprod goldenFac_pos summable_log_goldenFac).symm

/-- **T29a(iii)**, positivity: the Fourier floor at the golden ratio is
strictly positive. -/
theorem goldenFourierFloor_pos : 0 < ∏' m : ℤ, goldenFac m := by
  rw [tprod_goldenFac_eq_exp]
  exact Real.exp_pos _

/-! ## (iv) The limit along the frequencies `ξ_N` -/

private lemma summable_log_shift (N : ℕ) :
    Summable (fun j : ℕ => Real.log (goldenFac ((N : ℤ) - j))) :=
  summable_log_goldenFac.comp_injective (i := fun j : ℕ => (N : ℤ) - j)
    (fun a b hab => by simp only at hab; omega)

private lemma tsum_split (N : ℕ) :
    ∑' m : ℤ, Real.log (goldenFac m)
      = ∑' n : ℕ, Real.log (goldenFac ((n : ℤ) + N + 1))
        + ∑' j : ℕ, Real.log (goldenFac ((N : ℤ) - j)) := by
  have hGsum : Summable (fun m : ℤ => Real.log (goldenFac (m + ((N : ℤ) + 1)))) :=
    summable_log_goldenFac.comp_injective (i := fun m : ℤ => m + ((N : ℤ) + 1))
      (fun a b hab => by simpa using hab)
  have h1 : Summable (fun n : ℕ => Real.log (goldenFac ((n : ℤ) + ((N : ℤ) + 1)))) :=
    hGsum.comp_injective (i := fun n : ℕ => (n : ℤ)) (fun a b hab => by simpa using hab)
  have h2 : Summable (fun n : ℕ => Real.log (goldenFac (-((n : ℤ) + 1) + ((N : ℤ) + 1)))) :=
    hGsum.comp_injective (i := fun n : ℕ => -((n : ℤ) + 1))
      (fun a b hab => by simp only at hab; omega)
  have hsplit := tsum_of_nat_of_neg_add_one
    (f := fun m : ℤ => Real.log (goldenFac (m + ((N : ℤ) + 1)))) h1 h2
  have hfull := Equiv.tsum_eq (Equiv.addRight ((N : ℤ) + 1))
    (fun m : ℤ => Real.log (goldenFac m))
  simp only [Equiv.coe_addRight] at hfull
  rw [hfull] at hsplit
  have e1 : ∑' n : ℕ, Real.log (goldenFac ((n : ℤ) + ((N : ℤ) + 1)))
      = ∑' n : ℕ, Real.log (goldenFac ((n : ℤ) + N + 1)) :=
    tsum_congr (fun n => by
      rw [show ((n : ℤ) + ((N : ℤ) + 1)) = (n : ℤ) + N + 1 from by ring])
  have e2 : ∑' n : ℕ, Real.log (goldenFac (-((n : ℤ) + 1) + ((N : ℤ) + 1)))
      = ∑' j : ℕ, Real.log (goldenFac ((N : ℤ) - j)) :=
    tsum_congr (fun n => by
      rw [show (-((n : ℤ) + 1) + ((N : ℤ) + 1)) = (N : ℤ) - n from by ring])
  rw [hsplit]
  simp only [e1, e2]

/-- The tail of the log-sum beyond `N` tends to `0`. -/
private lemma tendsto_tail_zero :
    Tendsto (fun N : ℕ => ∑' n : ℕ, Real.log (goldenFac ((n : ℤ) + N + 1))) atTop (𝓝 0) := by
  have h := tendsto_sum_nat_add (fun k : ℕ => Real.log (goldenFac ((k : ℤ) + 1)))
  refine h.congr (fun N => ?_)
  exact tsum_congr (fun k =>
    by rw [show (((k + N : ℕ) : ℤ) + 1) = (k : ℤ) + N + 1 from by push_cast; ring])

/-- The log-sums of the truncated products converge to the log-sum of the
two-sided product. -/
theorem tendsto_log_partial :
    Tendsto (fun N : ℕ => ∑' j : ℕ, Real.log (goldenFac ((N : ℤ) - j))) atTop
      (𝓝 (∑' m : ℤ, Real.log (goldenFac m))) := by
  have hrw : ∀ N : ℕ, ∑' j : ℕ, Real.log (goldenFac ((N : ℤ) - j))
      = (∑' m : ℤ, Real.log (goldenFac m))
        - ∑' n : ℕ, Real.log (goldenFac ((n : ℤ) + N + 1)) := by
    intro N
    rw [tsum_split N]
    ring
  simp only [hrw]
  have hc : Tendsto (fun _ : ℕ => ∑' m : ℤ, Real.log (goldenFac m)) atTop
      (𝓝 (∑' m : ℤ, Real.log (goldenFac m))) := tendsto_const_nhds
  simpa using hc.sub tendsto_tail_zero

/-- **T29a(iv)**: the truncated products `∏_{m ≤ N}|cos(π φ^m)|` converge to
the two-sided product. -/
theorem tendsto_tprod_partial :
    Tendsto (fun N : ℕ => ∏' j : ℕ, goldenFac ((N : ℤ) - j)) atTop
      (𝓝 (∏' m : ℤ, goldenFac m)) := by
  have hexp : ∀ N : ℕ, ∏' j : ℕ, goldenFac ((N : ℤ) - j)
      = Real.exp (∑' j : ℕ, Real.log (goldenFac ((N : ℤ) - j))) :=
    fun N => (Real.rexp_tsum_eq_tprod (fun j => goldenFac_pos _) (summable_log_shift N)).symm
  simp only [hexp, tprod_goldenFac_eq_exp]
  exact (Real.continuous_exp.tendsto _).comp tendsto_log_partial

/-- **T29a(iv)**, in the form of the paper: the transform of the backward
system at the frequencies `ξ_N = φ^N/(1-r)` converges to the Fourier floor
`∏_{m ∈ ℤ}|cos(π φ^m)| > 0`. -/
theorem tendsto_cosProd_xi_golden :
    Tendsto (fun N : ℕ => cosProd (r Real.goldenRatio) (xi Real.goldenRatio N)) atTop
      (𝓝 (∏' m : ℤ, goldenFac m)) := by
  have hrw : ∀ N : ℕ, cosProd (r Real.goldenRatio) (xi Real.goldenRatio N)
      = ∏' j : ℕ, goldenFac ((N : ℤ) - j) :=
    fun N => cosProd_xi Real.one_lt_goldenRatio N
  simp only [hrw]
  exact tendsto_tprod_partial

end Fourier
end KnotGame
