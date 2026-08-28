import RequestProject.FourierReflect

/-!
# A certified rational enclosure of the golden Fourier floor (round 9, T29b)

`RequestProject.FourierFloor` proves that the two-sided product

  `∏_{m ∈ ℤ} |cos (π φ^m)|`

converges to a strictly positive limit (T29a(iii)), and
`RequestProject.FourierReflect` identifies it with the square of the one-sided
product over the negative exponents.  This file pins the value down between
explicit rationals:

  `66/10^4 ≤ ∏_{m ∈ ℤ} |cos (π φ^m)| ≤ 67/10^4`

(the measured value is `6.6135 × 10^{-3}`), which is the optional target T29b.

The route is entirely elementary and every numerical step is a kernel
computation with exact rationals:

* an alternating-series Taylor bound for `cos` (`cos_taylor_err`), valid
  whenever `x^2 ≤ 2`, together with the monotonicity of `cos` on `[0, π]`,
  turns a rational enclosure of the argument into a rational enclosure of the
  cosine (`cos_enclosure`);
* `φ⁻¹` and `π` are enclosed to nine and six decimals, giving rational
  enclosures of the twelve arguments `π φ^{-k}`, `k = 1, …, 12` — the first
  two factors coincide because `φ^{-1} + φ^{-2} = 1` (`goldenFac_neg_one_eq`);
* the tail `∏_{k ≥ 13}` is controlled by the log bound already proved in
  `FourierFloor` (`abs_log_goldenFac_le`), which gives
  `1 - 6·10^{-5} ≤ ∏_{k ≥ 13} ≤ 1`.

No new axiom, no `native_decide`: the arithmetic is `norm_num` over `ℚ`.
-/

namespace KnotGame
namespace Fourier

open Real Finset
open scoped Real

set_option maxHeartbeats 1000000

/-! ## 1. An alternating-series Taylor bound for the cosine -/

/-- The degree-8 Taylor polynomial of `cos` approximates `cos x` to within
`x^10/10!`, for every `x ≥ 0` with `x^2 ≤ 2` (so that the terms of the
alternating series are decreasing). -/
theorem cos_taylor_err (x : ℝ) (hx0 : 0 ≤ x) (hx2 : x ^ 2 ≤ 2) :
    |Real.cos x - (1 - x^2/2 + x^4/24 - x^6/720 + x^8/40320)| ≤ x^10/3628800 := by
  set f : ℕ → ℝ := fun i => x ^ (2 * i) / (Nat.factorial (2 * i)) with hf
  have hanti : Antitone f := by
    refine antitone_nat_of_succ_le (fun i => ?_)
    have hfac : (Nat.factorial (2 * (i+1)) : ℝ) = (2*i+2) * (2*i+1) * Nat.factorial (2*i) := by
      have h : 2 * (i+1) = (2*i+1) + 1 := by ring
      rw [h, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
    have hpos : (0:ℝ) < Nat.factorial (2*i) := by positivity
    have hx : x ^ (2 * (i+1)) = x ^ (2*i) * x^2 := by
      rw [← pow_add]; ring_nf
    simp only [hf, hx, hfac]
    rw [div_le_div_iff₀ (by positivity) hpos]
    have h1 : (0:ℝ) ≤ x ^ (2*i) := by positivity
    have h2 : (2:ℝ) ≤ (2*i+2)*(2*i+1) := by nlinarith [Nat.cast_nonneg (α := ℝ) i]
    have h3 : (0:ℝ) ≤ x ^ (2*i) * (Nat.factorial (2*i) : ℝ) := mul_nonneg h1 hpos.le
    nlinarith [mul_nonneg h3 (sub_nonneg.2 (le_trans hx2 h2))]
  have hsum : Summable f := by
    have h := Real.summable_pow_div_factorial x
    exact h.comp_injective (fun a b h => by omega)
  have herr := alternating_series_error_bound f hanti hsum 5
  have hcos : Real.cos x = ∑' i : ℕ, (-1:ℝ) ^ i * f i := by
    rw [Real.cos_eq_tsum]
    exact tsum_congr (fun i => by rw [hf]; ring)
  rw [← hcos] at herr
  have hsum5 : ∑ i ∈ range 5, (-1:ℝ) ^ i * f i
      = 1 - x^2/2 + x^4/24 - x^6/720 + x^8/40320 := by
    simp [hf, Finset.sum_range_succ, Nat.factorial]
    ring
  have hf5 : f 5 = x^10/3628800 := by simp [hf, Nat.factorial]
  rw [hsum5, hf5] at herr
  exact herr

/-- From a rational enclosure `[a, b]` of the argument to a rational
enclosure `[lo, hi]` of its cosine.  `cos` is decreasing on `[0, π]`, so the
lower Taylor bound at `b` and the upper Taylor bound at `a` bracket it. -/
theorem cos_enclosure {x a b lo hi : ℝ} (ha0 : 0 ≤ a) (hax : a ≤ x) (hxb : x ≤ b)
    (hb2 : b ^ 2 ≤ 2)
    (hlo : lo ≤ 1 - b^2/2 + b^4/24 - b^6/720 + b^8/40320 - b^10/3628800)
    (hhi : 1 - a^2/2 + a^4/24 - a^6/720 + a^8/40320 + a^10/3628800 ≤ hi) :
    lo ≤ Real.cos x ∧ Real.cos x ≤ hi := by
  have hb0 : 0 ≤ b := le_trans ha0 (le_trans hax hxb)
  have ha2 : a ^ 2 ≤ 2 := by nlinarith
  have hpi : (3.141592 : ℝ) < π := Real.pi_gt_d6
  have hbpi : b ≤ π := by nlinarith
  have h1 : Real.cos b ≤ Real.cos x :=
    Real.cos_le_cos_of_nonneg_of_le_pi (le_trans ha0 hax) hbpi hxb
  have h2 : Real.cos x ≤ Real.cos a :=
    Real.cos_le_cos_of_nonneg_of_le_pi ha0 (le_trans hxb hbpi) hax
  have e1 := abs_le.1 (cos_taylor_err b hb0 hb2)
  have e2 := abs_le.1 (cos_taylor_err a ha0 ha2)
  exact ⟨by linarith [e1.1], by linarith [e2.2]⟩

/-! ## 2. Rational enclosures of `φ⁻¹` and of the arguments `π φ^{-k}` -/

lemma gc_lb : (618033988/10^9 : ℝ) ≤ gc := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5n : (0:ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hlo : (2236067977/10^9 : ℝ) ≤ Real.sqrt 5 := by nlinarith
  have hinv : gc = (Real.sqrt 5 - 1)/2 := by
    rw [gc_eq, Real.inv_goldenRatio, Real.goldenConj]; ring
  rw [hinv]; linarith

lemma gc_ub : gc ≤ (618033989/10^9 : ℝ) := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5n : (0:ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hhi : Real.sqrt 5 ≤ (2236067978/10^9 : ℝ) := by nlinarith
  have hinv : gc = (Real.sqrt 5 - 1)/2 := by
    rw [gc_eq, Real.inv_goldenRatio, Real.goldenConj]; ring
  rw [hinv]; linarith

/-- The argument `π φ^{-k}` lies between the two indicated rationals. -/
lemma pi_gc_pow_bounds (k : ℕ) :
    (3141592/10^6 : ℝ) * (618033988/10^9)^k ≤ π * gc ^ k ∧
      π * gc ^ k ≤ (3141593/10^6 : ℝ) * (618033989/10^9)^k := by
  have hpl : (3141592/10^6 : ℝ) ≤ π := by
    have := Real.pi_gt_d6; norm_num at this ⊢; linarith
  have hpu : π ≤ (3141593/10^6 : ℝ) := by
    have := Real.pi_lt_d6; norm_num at this ⊢; linarith
  have hlo : ((618033988/10^9 : ℝ))^k ≤ gc ^ k :=
    pow_le_pow_left₀ (by norm_num) gc_lb k
  have hhi : gc ^ k ≤ ((618033989/10^9 : ℝ))^k :=
    pow_le_pow_left₀ gc_pos.le gc_ub k
  have h1 : (0:ℝ) ≤ ((618033988/10^9 : ℝ))^k := by positivity
  have h2 : (0:ℝ) ≤ gc ^ k := pow_nonneg gc_pos.le k
  constructor
  · exact mul_le_mul hpl hlo h1 (by linarith)
  · exact mul_le_mul hpu hhi h2 (by norm_num)

/-! ## 3. The twelve leading factors -/

/-- The factor at the exponent `-k` is `|cos (π φ^{-k})| = |cos (π c^k)|`. -/
lemma goldenFac_neg_pow (k : ℕ) : goldenFac (-(k:ℤ)) = |Real.cos (π * gc ^ k)| := by
  have h : Real.goldenRatio ^ (-(k:ℤ)) = gc ^ k := by
    rw [zpow_neg, ← inv_zpow, zpow_natCast, gc_eq]
  rw [goldenFac, cosFac, h]

/-- Because `c + c² = 1`, the first two factors coincide. -/
lemma goldenFac_neg_one_eq : goldenFac (-1) = goldenFac (-2) := by
  have hsq : gc ^ 2 = 1 - gc := by
    have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have hinv : gc = (Real.sqrt 5 - 1)/2 := by
      rw [gc_eq, Real.inv_goldenRatio, Real.goldenConj]; ring
    rw [hinv]
    linear_combination h5 / 4
  have h1 : goldenFac (-(1:ℤ)) = |Real.cos (π * gc ^ 1)| := goldenFac_neg_pow 1
  have h2 : goldenFac (-(2:ℤ)) = |Real.cos (π * gc ^ 2)| := goldenFac_neg_pow 2
  have harg : π * gc ^ 1 = π - π * gc ^ 2 := by rw [hsq]; ring
  rw [h1, h2, harg, Real.cos_pi_sub, abs_neg]

/-- The workhorse: a rational enclosure of a single factor `|cos (π c^k)|`,
given rational bounds `a ≤ π c^k ≤ b` certified by `pi_gc_pow_bounds`. -/
lemma goldenFac_enclosure {k : ℕ} {a b lo hi : ℝ} (ha0 : 0 ≤ a) (hlo0 : 0 ≤ lo)
    (ha : a ≤ (3141592/10^6 : ℝ) * (618033988/10^9)^k)
    (hb : ((3141593/10^6 : ℝ) * (618033989/10^9)^k) ≤ b)
    (hb2 : b ^ 2 ≤ 2)
    (hlo : lo ≤ 1 - b^2/2 + b^4/24 - b^6/720 + b^8/40320 - b^10/3628800)
    (hhi : 1 - a^2/2 + a^4/24 - a^6/720 + a^8/40320 + a^10/3628800 ≤ hi) :
    lo ≤ goldenFac (-(k:ℤ)) ∧ goldenFac (-(k:ℤ)) ≤ hi := by
  obtain ⟨hA, hB⟩ := pi_gc_pow_bounds k
  obtain ⟨h1, h2⟩ := cos_enclosure (x := π * gc ^ k) ha0 (le_trans ha hA)
    (le_trans hB hb) hb2 hlo hhi
  have habs : |Real.cos (π * gc ^ k)| = Real.cos (π * gc ^ k) :=
    abs_of_nonneg (le_trans hlo0 h1)
  rw [goldenFac_neg_pow k, habs]
  exact ⟨h1, h2⟩


/-! ### The eleven distinct factor enclosures

For `k = 2, …, 12` the argument `π c^k` is at most `1.2 < √2`, so the Taylor
bound applies; each pair of rational bounds below is verified by `norm_num`
over `ℚ`.  The factor at `k = 1` equals the one at `k = 2`
(`goldenFac_neg_one_eq`).
-/

lemma fac2 : (362374/10^6 : ℝ) ≤ goldenFac (-2) ∧ goldenFac (-2) ≤ 362379/10^6 :=
  goldenFac_enclosure (k := 2) (a := 1199981/10^6) (b := 1199982/10^6)
    (lo := 362374/10^6) (hi := 362379/10^6)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

lemma fac3 : (737368/10^6 : ℝ) ≤ goldenFac (-3) ∧ goldenFac (-3) ≤ 737370/10^6 :=
  goldenFac_enclosure (k := 3) (a := 741629/10^6) (b := 741630/10^6)
    (lo := 737368/10^6) (hi := 737370/10^6)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

lemma fac4 : (896782/10^6 : ℝ) ≤ goldenFac (-4) ∧ goldenFac (-4) ≤ 896783/10^6 :=
  goldenFac_enclosure (k := 4) (a := 458352/10^6) (b := 458353/10^6)
    (lo := 896782/10^6) (hi := 896783/10^6)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

lemma fac5 : (960144/10^6 : ℝ) ≤ goldenFac (-5) ∧ goldenFac (-5) ≤ 960145/10^6 :=
  goldenFac_enclosure (k := 5) (a := 283277/10^6) (b := 283278/10^6)
    (lo := 960144/10^6) (hi := 960145/10^6)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

lemma fac6 : (984713/10^6 : ℝ) ≤ goldenFac (-6) ∧ goldenFac (-6) ≤ 984714/10^6 :=
  goldenFac_enclosure (k := 6) (a := 175074/10^6) (b := 175075/10^6)
    (lo := 984713/10^6) (hi := 984714/10^6)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

lemma fac7 : (994151/10^6 : ℝ) ≤ goldenFac (-7) ∧ goldenFac (-7) ≤ 994152/10^6 :=
  goldenFac_enclosure (k := 7) (a := 108202/10^6) (b := 108203/10^6)
    (lo := 994151/10^6) (hi := 994152/10^6)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

lemma fac8 : (997764/10^6 : ℝ) ≤ goldenFac (-8) ∧ goldenFac (-8) ≤ 997765/10^6 :=
  goldenFac_enclosure (k := 8) (a := 66872/10^6) (b := 66873/10^6)
    (lo := 997764/10^6) (hi := 997765/10^6)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

lemma fac9 : (999146/10^6 : ℝ) ≤ goldenFac (-9) ∧ goldenFac (-9) ≤ 999147/10^6 :=
  goldenFac_enclosure (k := 9) (a := 41329/10^6) (b := 41330/10^6)
    (lo := 999146/10^6) (hi := 999147/10^6)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

lemma fac10 : (999673/10^6 : ℝ) ≤ goldenFac (-10) ∧ goldenFac (-10) ≤ 999674/10^6 :=
  goldenFac_enclosure (k := 10) (a := 25543/10^6) (b := 25544/10^6)
    (lo := 999673/10^6) (hi := 999674/10^6)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

lemma fac11 : (999875/10^6 : ℝ) ≤ goldenFac (-11) ∧ goldenFac (-11) ≤ 999876/10^6 :=
  goldenFac_enclosure (k := 11) (a := 15786/10^6) (b := 15787/10^6)
    (lo := 999875/10^6) (hi := 999876/10^6)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

lemma fac12 : (999952/10^6 : ℝ) ≤ goldenFac (-12) ∧ goldenFac (-12) ≤ 999953/10^6 :=
  goldenFac_enclosure (k := 12) (a := 9756/10^6) (b := 9757/10^6)
    (lo := 999952/10^6) (hi := 999953/10^6)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

lemma fac1 : (362374/10^6 : ℝ) ≤ goldenFac (-1) ∧ goldenFac (-1) ≤ 362379/10^6 := by
  rw [goldenFac_neg_one_eq]; exact fac2

/-! ## 4. The tail of the product, and the assembly

Beyond the twelfth factor the log bound of `FourierFloor` applies, and the
geometric series it produces is smaller than `6·10^{-5}`; so the tail product
lies in `[1 - 6·10^{-5}, 1]`.
-/

lemma pi_sq_gc_pow_le_one (n : ℕ) (hn : 3 ≤ n) : π ^ 2 * (gc ^ 2) ^ n ≤ 1 := by
  have h0 : (0:ℝ) ≤ gc ^ 2 := sq_nonneg gc
  have hg2 : gc ^ 2 ≤ 382/1000 := by nlinarith [gc_ub, gc_pos]
  have h1 : (gc ^ 2) ^ n ≤ (gc ^ 2) ^ 3 := pow_le_pow_of_le_one h0 (by nlinarith) hn
  have h2 : (gc ^ 2) ^ 3 ≤ ((382/1000 : ℝ)) ^ 3 := pow_le_pow_left₀ h0 hg2 3
  have hpi : π ≤ 3141593/10^6 := by have := Real.pi_lt_d6; norm_num at this ⊢; linarith
  have hpi2 : π ^ 2 ≤ ((3141593/10^6 : ℝ)) ^ 2 := by nlinarith [Real.pi_pos]
  have hpow0 : (0:ℝ) ≤ (gc ^ 2) ^ n := pow_nonneg h0 n
  calc π ^ 2 * (gc ^ 2) ^ n ≤ ((3141593/10^6 : ℝ)) ^ 2 * ((382/1000 : ℝ)) ^ 3 := by
        apply mul_le_mul hpi2 (le_trans h1 h2) hpow0 (by norm_num)
    _ ≤ 1 := by norm_num

lemma tail_log_bound (i : ℕ) :
    |Real.log (goldenFac (-(((i + 12 : ℕ) : ℤ) + 1)))| ≤ π ^ 2 * (gc ^ 2) ^ (i + 13) := by
  have hnat : (-(((i + 12 : ℕ) : ℤ) + 1)).natAbs = i + 13 := by
    push_cast
    omega
  have hle : π ^ 2 * (gc ^ 2) ^ (i + 13) ≤ 1 := pi_sq_gc_pow_le_one (i + 13) (by omega)
  have h := abs_log_goldenFac_le (m := -(((i + 12 : ℕ) : ℤ) + 1)) (by rw [hnat]; exact hle)
  rwa [hnat] at h

lemma tail_summable :
    Summable (fun i : ℕ => Real.log (goldenFac (-(((i + 12 : ℕ) : ℤ) + 1)))) :=
  (summable_nat_add_iff 12).2 summable_log_goldenFac_neg

lemma tail_abs_le :
    |∑' i : ℕ, Real.log (goldenFac (-(((i + 12 : ℕ) : ℤ) + 1)))| ≤ 6/10^5 := by
  have h0 : (0:ℝ) ≤ gc ^ 2 := sq_nonneg gc
  have hg2 : gc ^ 2 ≤ 3819661/10^7 := by nlinarith [gc_ub, gc_pos]
  have hlt : gc ^ 2 < 1 := gc_sq_lt_one
  have hgeom : Summable (fun i : ℕ => π ^ 2 * (gc ^ 2) ^ (i + 13)) := by
    have := (summable_geometric_of_lt_one h0 hlt).mul_left (π ^ 2 * (gc ^ 2) ^ 13)
    refine this.congr (fun i => ?_)
    rw [pow_add]
    ring
  have habs : Summable (fun i : ℕ => |Real.log (goldenFac (-(((i + 12 : ℕ) : ℤ) + 1)))|) :=
    Summable.of_nonneg_of_le (fun i => abs_nonneg _) tail_log_bound hgeom
  have hstep : |∑' i : ℕ, Real.log (goldenFac (-(((i + 12 : ℕ) : ℤ) + 1)))|
      ≤ ∑' i : ℕ, |Real.log (goldenFac (-(((i + 12 : ℕ) : ℤ) + 1)))| := by
    simpa [Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm (f := fun i : ℕ => Real.log (goldenFac (-(((i + 12 : ℕ) : ℤ) + 1))))
        (by simpa [Real.norm_eq_abs] using habs)
  have hcmp : ∑' i : ℕ, |Real.log (goldenFac (-(((i + 12 : ℕ) : ℤ) + 1)))|
      ≤ ∑' i : ℕ, π ^ 2 * (gc ^ 2) ^ (i + 13) :=
    Summable.tsum_le_tsum tail_log_bound habs hgeom
  have hval : ∑' i : ℕ, π ^ 2 * (gc ^ 2) ^ (i + 13)
      = π ^ 2 * (gc ^ 2) ^ 13 * (1 - gc ^ 2)⁻¹ := by
    have : ∀ i : ℕ, π ^ 2 * (gc ^ 2) ^ (i + 13) = (π ^ 2 * (gc ^ 2) ^ 13) * (gc ^ 2) ^ i := by
      intro i; rw [pow_add]; ring
    rw [tsum_congr this, tsum_mul_left, tsum_geometric_of_lt_one h0 hlt]
  have hbound : π ^ 2 * (gc ^ 2) ^ 13 * (1 - gc ^ 2)⁻¹ ≤ 6/10^5 := by
    have hA : π ^ 2 ≤ ((3141593/10^6 : ℝ)) ^ 2 := by
      have hpi : π ≤ 3141593/10^6 := by have := Real.pi_lt_d6; norm_num at this ⊢; linarith
      nlinarith [Real.pi_pos]
    have hB : (gc ^ 2) ^ 13 ≤ ((3819661/10^7 : ℝ)) ^ 13 := pow_le_pow_left₀ h0 hg2 13
    have hden : (618/1000 : ℝ) ≤ 1 - gc ^ 2 := by nlinarith [gc_ub, gc_pos]
    have hC : (1 - gc ^ 2)⁻¹ ≤ (1000/618 : ℝ) := by
      rw [show (1000/618 : ℝ) = ((618/1000 : ℝ))⁻¹ by norm_num]
      exact inv_anti₀ (by norm_num) hden
    have h1 : (0:ℝ) ≤ (gc ^ 2) ^ 13 := pow_nonneg h0 13
    have h2 : (0:ℝ) ≤ (1 - gc ^ 2)⁻¹ := by positivity
    calc π ^ 2 * (gc ^ 2) ^ 13 * (1 - gc ^ 2)⁻¹
        ≤ ((3141593/10^6 : ℝ)) ^ 2 * ((3819661/10^7 : ℝ)) ^ 13 * (1000/618 : ℝ) := by
          apply mul_le_mul _ hC h2 (by positivity)
          exact mul_le_mul hA hB h1 (by positivity)
      _ ≤ 6/10^5 := by norm_num
  rw [hval] at hcmp
  linarith


lemma tail_nonpos : ∑' i : ℕ, Real.log (goldenFac (-(((i + 12 : ℕ) : ℤ) + 1))) ≤ 0 :=
  tsum_nonpos (fun _ => Real.log_nonpos (goldenFac_nonneg _) (goldenFac_le_one _))

lemma tprod_neg_split :
    ∏' k : ℕ, goldenFac (-((k:ℤ)+1))
      = (∏ k ∈ range 12, goldenFac (-((k:ℤ)+1))) *
        Real.exp (∑' i : ℕ, Real.log (goldenFac (-(((i + 12 : ℕ) : ℤ) + 1)))) := by
  have hQ : ∏' k : ℕ, goldenFac (-((k:ℤ)+1))
      = Real.exp (∑' k : ℕ, Real.log (goldenFac (-((k:ℤ)+1)))) :=
    (Real.rexp_tsum_eq_tprod (fun k => goldenFac_pos _) summable_log_goldenFac_neg).symm
  rw [hQ, ← Summable.sum_add_tsum_nat_add 12 summable_log_goldenFac_neg, Real.exp_add]
  congr 1
  rw [Real.exp_sum]
  exact Finset.prod_congr rfl (fun k _ => Real.exp_log (goldenFac_pos _))

lemma partial_prod_expand :
    ∏ k ∈ range 12, goldenFac (-((k:ℤ)+1))
      = goldenFac (-1) * goldenFac (-2) * goldenFac (-3) * goldenFac (-4) *
        goldenFac (-5) * goldenFac (-6) * goldenFac (-7) * goldenFac (-8) *
        goldenFac (-9) * goldenFac (-10) * goldenFac (-11) * goldenFac (-12) := by
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  norm_num

lemma partial_prod_le : ∏ k ∈ range 12, goldenFac (-((k:ℤ)+1)) ≤ 813281/10^7 := by
  rw [partial_prod_expand]
  have h : goldenFac (-1) * goldenFac (-2) * goldenFac (-3) * goldenFac (-4) *
        goldenFac (-5) * goldenFac (-6) * goldenFac (-7) * goldenFac (-8) *
        goldenFac (-9) * goldenFac (-10) * goldenFac (-11) * goldenFac (-12)
      ≤ (362379/10^6 : ℝ) * (362379/10^6) * (737370/10^6) * (896783/10^6) *
        (960145/10^6) * (984714/10^6) * (994152/10^6) * (997765/10^6) *
        (999147/10^6) * (999674/10^6) * (999876/10^6) * (999953/10^6) := by
    gcongr <;>
      first
        | exact goldenFac_nonneg _
        | linarith [fac1.2, fac2.2, fac3.2, fac4.2, fac5.2, fac6.2, fac7.2, fac8.2,
            fac9.2, fac10.2, fac11.2, fac12.2]
  refine le_trans h ?_
  norm_num

lemma le_partial_prod : (813248/10^7 : ℝ) ≤ ∏ k ∈ range 12, goldenFac (-((k:ℤ)+1)) := by
  rw [partial_prod_expand]
  have h : (362374/10^6 : ℝ) * (362374/10^6) * (737368/10^6) * (896782/10^6) *
        (960144/10^6) * (984713/10^6) * (994151/10^6) * (997764/10^6) *
        (999146/10^6) * (999673/10^6) * (999875/10^6) * (999952/10^6)
      ≤ goldenFac (-1) * goldenFac (-2) * goldenFac (-3) * goldenFac (-4) *
        goldenFac (-5) * goldenFac (-6) * goldenFac (-7) * goldenFac (-8) *
        goldenFac (-9) * goldenFac (-10) * goldenFac (-11) * goldenFac (-12) := by
    gcongr <;>
      first
        | positivity
        | ((repeat' apply mul_nonneg) <;> exact goldenFac_nonneg _)
        | linarith [fac1.1, fac2.1, fac3.1, fac4.1, fac5.1, fac6.1, fac7.1, fac8.1,
            fac9.1, fac10.1, fac11.1, fac12.1]
  refine le_trans ?_ h
  norm_num

/-- The one-sided product lies between two explicit rationals. -/
theorem tprod_neg_enclosure :
    (813199/10^7 : ℝ) ≤ ∏' k : ℕ, goldenFac (-((k:ℤ)+1)) ∧
      ∏' k : ℕ, goldenFac (-((k:ℤ)+1)) ≤ 813281/10^7 := by
  set T := ∑' i : ℕ, Real.log (goldenFac (-(((i + 12 : ℕ) : ℤ) + 1))) with hT
  have habs := tail_abs_le
  rw [← hT] at habs
  have hTle : |T| ≤ 6/10^5 := habs
  have hlow : -(6/10^5 : ℝ) ≤ T := (abs_le.1 hTle).1
  have hexp_lo : (1 : ℝ) - 6/10^5 ≤ Real.exp T := by
    have := Real.add_one_le_exp T
    linarith
  have hexp_hi : Real.exp T ≤ 1 := by
    rw [show (1:ℝ) = Real.exp 0 by simp]
    exact Real.exp_le_exp.2 tail_nonpos
  have hexp_pos : 0 < Real.exp T := Real.exp_pos T
  have hsplit := tprod_neg_split
  rw [← hT] at hsplit
  constructor
  · rw [hsplit]
    have h1 : (813248/10^7 : ℝ) * (1 - 6/10^5) ≤
        (∏ k ∈ range 12, goldenFac (-((k:ℤ)+1))) * Real.exp T := by
      have hp0 : (0:ℝ) ≤ ∏ k ∈ range 12, goldenFac (-((k:ℤ)+1)) :=
        le_trans (by norm_num) le_partial_prod
      apply mul_le_mul le_partial_prod hexp_lo (by norm_num) hp0
    refine le_trans ?_ h1
    norm_num
  · rw [hsplit]
    have h2 : (∏ k ∈ range 12, goldenFac (-((k:ℤ)+1))) * Real.exp T
        ≤ (813281/10^7 : ℝ) * 1 := by
      apply mul_le_mul partial_prod_le hexp_hi hexp_pos.le (by norm_num)
    simpa using h2

/-- **T29b**: a certified rational enclosure of the golden Fourier floor. -/
theorem goldenFourierFloor_enclosure :
    (66/10^4 : ℝ) ≤ ∏' m : ℤ, goldenFac m ∧ ∏' m : ℤ, goldenFac m ≤ 67/10^4 := by
  obtain ⟨hlo, hhi⟩ := tprod_neg_enclosure
  rw [goldenFourierFloor_eq_sq]
  constructor
  · nlinarith [hlo]
  · nlinarith [hlo, hhi]

end Fourier
end KnotGame
