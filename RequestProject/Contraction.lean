import RequestProject.CountingOperator

/-!
# T40 — the normalised counting operator and its spectral gap (paper `prop:gap`)

The counting operator of `RequestProject.CountingOperator` is

  `(T h)(y) = (1/λ) [ h (y/λ) + h ((y + λ - 1)/λ) ]`,

with `T 1 = (2/λ)·1`.  Normalising by that eigenvalue, `P = (λ/2)·T`, gives the
Markov operator of the backward pair of contractions with equal weights,

  `(P h)(y) = (1/2) [ h (r y) + h (r y + 1 - r) ]`,   `r = 1/λ`.

Proved here:

* `P_one` — `P 1 = 1`;
* `P_eq_smul_T` — `P h = (λ/2) · T h`, the normalisation;
* `lipschitz_contraction` — if `h` is `LipschitzWith K` then `P h` is
  `LipschitzWith (r·K)`: the operator contracts the Lipschitz seminorm by `r`;
* `tendsto_const` — for Lipschitz `h` the iterates `P^[m] h` converge uniformly
  on `[0,1]` to a constant, at the geometric rate `r^m`;
* `const_eq_integral_of_invariant` — the identification of that constant: if a
  probability measure `ν` carried by `[0,1]` is invariant for `P` in the sense
  that `∫ (P φ) dν = ∫ φ dν` for every Lipschitz `φ` (`InvariantOn`), then the
  constant is `∫ h dν`.  Integrability of the iterates is not assumed but
  proved (`integrable_of_lipBound`, `integrable_iterate`), and the `m`-fold
  invariance is derived from the one-step form (`integral_iterate_eq`); the
  round-14 statement with both taken as hypotheses survives as
  `const_eq_integral_of_iterate_invariant`.

## Conventions (SCRUPLES)

* **Which formulation of the contraction.**  As the commission asks, the
  Lipschitz formulation is the statement: `lipschitz_contraction` is about
  `LipschitzWith`, and no differentiability is assumed anywhere.  The
  derivative identity `(Ph)'(y) = (r/2)[h'(ry) + h'(ry+1-r)]` of the paper is
  used only as the idea of the proof.  The working form inside the file is the
  equivalent explicit inequality `|h x - h y| ≤ K |x - y|` with a **real**
  constant (`LipBound`), because the iteration multiplies constants by `r`,
  which is real; `lipschitz_contraction` and `lipschitz_contraction_iterate`
  convert to and from `LipschitzWith`.
* **Which route to the limit.**  The recommended nested-interval route: the
  values of `P^[m] h` on `[0,1]` all lie within `r^m·K` of each other because
  `P` maps `[0,1]` into itself branchwise, so the sequence of midpoint values
  `P^[m] h (1/2)` is geometrically Cauchy and everything on `[0,1]` is trapped
  near its limit.  No Cauchy estimate in a function norm is needed, and no
  completeness of a space of functions.
* **The limit constant is not identified with `∫ h dν_r`.**  The Bernoulli
  convolution `ν_r` is nowhere constructed in this project, so — exactly as
  round 13 did for the trapezoid — the identification is a hypothesis:
  `const_eq_integral_of_invariant` takes the invariance of `ν` as an explicit
  assumption and concludes.  Constructing `ν_r` is deferred.
* `P` is defined on all of `ℝ`; the contraction estimate is global, while the
  convergence statement is on `[0,1]`, where it must be: on the whole line a
  nonconstant Lipschitz function stays nonconstant under `P`.
-/

namespace KnotGame
namespace Contraction

open MeasureTheory Set Filter Topology

variable {lam : ℝ}

/-! ### The normalised operator -/

/-- The normalised counting operator `(P h)(y) = (1/2)[h(ry) + h(ry + 1 - r)]`,
`r = 1/λ`: the Markov operator of the backward pair of contractions with equal
weights. -/
noncomputable def P (lam : ℝ) (h : ℝ → ℝ) (y : ℝ) : ℝ :=
  (1 / 2) * (h (r lam * y) + h (r lam * y + 1 - r lam))

/-- **T40(a).**  `P 1 = 1`. -/
@[simp] theorem P_one (lam : ℝ) (y : ℝ) : P lam (fun _ => 1) y = 1 := by
  simp [P]
  norm_num

/-- `P` is the counting operator normalised by its eigenvalue: `P = (λ/2)·T`. -/
theorem P_eq_smul_T (hlam : 1 < lam) (h : ℝ → ℝ) (y : ℝ) :
    P lam h y = (lam / 2) * CountingOperator.T lam h y := by
  have h0 : lam ≠ 0 := ne_of_gt (lt_trans zero_lt_one hlam)
  have e1 : r lam * y = y / lam := by rw [r]; field_simp
  have e2 : r lam * y + 1 - r lam = (y + lam - 1) / lam := by rw [r]; field_simp
  rw [P, CountingOperator.T, e2, e1]
  field_simp

/-! ### The contraction -/

/-- The explicit Lipschitz bound with a real constant, the working form of the
contraction inside this file. -/
def LipBound (K : ℝ) (h : ℝ → ℝ) : Prop := ∀ x y : ℝ, |h x - h y| ≤ K * |x - y|

lemma LipBound.nonneg {K : ℝ} {h : ℝ → ℝ} (hK : LipBound K h) : 0 ≤ K := by
  have := hK 1 0
  have h1 : |(1 : ℝ) - 0| = 1 := by norm_num
  rw [h1, mul_one] at this
  exact le_trans (abs_nonneg _) this

lemma lipBound_of_lipschitzWith {K : NNReal} {h : ℝ → ℝ} (hh : LipschitzWith K h) :
    LipBound (K : ℝ) h := by
  intro x y
  have := hh.dist_le_mul x y
  simpa [Real.dist_eq] using this

lemma lipschitzWith_of_lipBound {K : ℝ} {h : ℝ → ℝ} (hK : LipBound K h) :
    LipschitzWith (Real.toNNReal K) h := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  have hKn : 0 ≤ K := hK.nonneg
  have : |h x - h y| ≤ K * |x - y| := hK x y
  simpa [Real.dist_eq, Real.coe_toNNReal _ hKn] using this

/-- The contraction, in the working form: `P` multiplies a Lipschitz bound
by `r`. -/
theorem lipBound_P (hlam : 1 < lam) {K : ℝ} {h : ℝ → ℝ} (hK : LipBound K h) :
    LipBound (r lam * K) (P lam h) := by
  have hr0 : 0 < r lam := by
    rw [r]; exact inv_pos.2 (lt_trans zero_lt_one hlam)
  intro y z
  have e : P lam h y - P lam h z =
      (1 / 2) * ((h (r lam * y) - h (r lam * z)) +
        (h (r lam * y + 1 - r lam) - h (r lam * z + 1 - r lam))) := by
    simp only [P]; ring
  have b1 : |h (r lam * y) - h (r lam * z)| ≤ K * (r lam * |y - z|) := by
    refine le_trans (hK _ _) ?_
    have : |r lam * y - r lam * z| = r lam * |y - z| := by
      rw [← mul_sub, abs_mul, abs_of_pos hr0]
    rw [this]
  have b2 : |h (r lam * y + 1 - r lam) - h (r lam * z + 1 - r lam)| ≤
      K * (r lam * |y - z|) := by
    refine le_trans (hK _ _) ?_
    have : |(r lam * y + 1 - r lam) - (r lam * z + 1 - r lam)| = r lam * |y - z| := by
      have : (r lam * y + 1 - r lam) - (r lam * z + 1 - r lam) = r lam * (y - z) := by ring
      rw [this, abs_mul, abs_of_pos hr0]
    rw [this]
  rw [e, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2)]
  have := abs_add_le (h (r lam * y) - h (r lam * z))
    (h (r lam * y + 1 - r lam) - h (r lam * z + 1 - r lam))
  nlinarith [abs_nonneg (y - z)]

/-- **T40(b).**  If `h` is `LipschitzWith K` then `P h` is
`LipschitzWith (r·K)`: the normalised counting operator contracts the Lipschitz
seminorm by the factor `r = 1/λ`. -/
theorem lipschitz_contraction (hlam : 1 < lam) {K : NNReal} {h : ℝ → ℝ}
    (hh : LipschitzWith K h) :
    LipschitzWith (Real.toNNReal (r lam) * K) (P lam h) := by
  have hr0 : 0 < r lam := by rw [r]; exact inv_pos.2 (lt_trans zero_lt_one hlam)
  have hb := lipBound_P hlam (lipBound_of_lipschitzWith hh)
  have := lipschitzWith_of_lipBound hb
  rwa [Real.toNNReal_mul (le_of_lt hr0), Real.toNNReal_coe] at this

/-- The iterated contraction, in the working form. -/
theorem lipBound_iterate (hlam : 1 < lam) :
    ∀ (m : ℕ) {K : ℝ} {h : ℝ → ℝ}, LipBound K h → LipBound ((r lam) ^ m * K) ((P lam)^[m] h)
  | 0, _, _, hK => by simpa using hK
  | (m + 1), K, h, hK => by
      have hstep := lipBound_iterate hlam m (lipBound_P hlam hK)
      have : (r lam) ^ m * (r lam * K) = (r lam) ^ (m + 1) * K := by ring
      rw [Function.iterate_succ_apply, ← this]
      exact hstep

/-- The iterated contraction, in the `LipschitzWith` formulation. -/
theorem lipschitz_contraction_iterate (hlam : 1 < lam) (m : ℕ) {K : NNReal} {h : ℝ → ℝ}
    (hh : LipschitzWith K h) :
    LipschitzWith (Real.toNNReal ((r lam) ^ m) * K) ((P lam)^[m] h) := by
  have hr0 : 0 < (r lam) ^ m := by
    have : 0 < r lam := by rw [r]; exact inv_pos.2 (lt_trans zero_lt_one hlam)
    positivity
  have hb := lipBound_iterate hlam m (lipBound_of_lipschitzWith hh)
  have := lipschitzWith_of_lipBound hb
  rwa [Real.toNNReal_mul (le_of_lt hr0), Real.toNNReal_coe] at this

/-! ### Convergence to a constant -/

lemma r_lt_one (hlam : 1 < lam) : r lam < 1 := by
  rw [r]
  exact inv_lt_one_of_one_lt₀ hlam

lemma r_pos (hlam : 1 < lam) : 0 < r lam := by
  rw [r]; exact inv_pos.2 (lt_trans zero_lt_one hlam)

/-- The midpoint values of the iterates form a geometrically Cauchy sequence. -/
lemma dist_midpoint_succ (hlam : 1 < lam) {K : ℝ} {h : ℝ → ℝ} (hK : LipBound K h) (m : ℕ) :
    dist ((P lam)^[m] h (1/2)) ((P lam)^[m + 1] h (1/2)) ≤ K * (r lam) ^ m := by
  have hr0 := r_pos hlam
  have hr1 := r_lt_one hlam
  have hKn : 0 ≤ K := hK.nonneg
  have hit := lipBound_iterate hlam m hK
  have hval : (P lam)^[m + 1] h (1/2) =
      (1/2) * (((P lam)^[m] h) (r lam * (1/2)) + ((P lam)^[m] h) (r lam * (1/2) + 1 - r lam)) := by
    rw [Function.iterate_succ_apply']
    rfl
  have b1 : |((P lam)^[m] h) (r lam * (1/2)) - ((P lam)^[m] h) (1/2)| ≤ (r lam) ^ m * K * (1/2) := by
    refine le_trans (hit _ _) ?_
    have : |r lam * (1/2) - 1/2| ≤ 1/2 := by
      rw [abs_le]; constructor <;> nlinarith
    have hcoef : 0 ≤ (r lam) ^ m * K := by positivity
    exact mul_le_mul_of_nonneg_left this hcoef
  have b2 : |((P lam)^[m] h) (r lam * (1/2) + 1 - r lam) - ((P lam)^[m] h) (1/2)| ≤
      (r lam) ^ m * K * (1/2) := by
    refine le_trans (hit _ _) ?_
    have : |(r lam * (1/2) + 1 - r lam) - 1/2| ≤ 1/2 := by
      rw [abs_le]; constructor <;> nlinarith
    have hcoef : 0 ≤ (r lam) ^ m * K := by positivity
    exact mul_le_mul_of_nonneg_left this hcoef
  rw [Real.dist_eq, hval]
  have e : (P lam)^[m] h (1/2) -
      (1/2) * (((P lam)^[m] h) (r lam * (1/2)) + ((P lam)^[m] h) (r lam * (1/2) + 1 - r lam)) =
      (1/2) * ((((P lam)^[m] h) (1/2) - ((P lam)^[m] h) (r lam * (1/2))) +
        (((P lam)^[m] h) (1/2) - ((P lam)^[m] h) (r lam * (1/2) + 1 - r lam))) := by ring
  rw [e, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  have t1 : |((P lam)^[m] h) (1/2) - ((P lam)^[m] h) (r lam * (1/2))| ≤ (r lam) ^ m * K * (1/2) := by
    rw [abs_sub_comm]; exact b1
  have t2 : |((P lam)^[m] h) (1/2) - ((P lam)^[m] h) (r lam * (1/2) + 1 - r lam)| ≤
      (r lam) ^ m * K * (1/2) := by
    rw [abs_sub_comm]; exact b2
  have habs := abs_add_le (((P lam)^[m] h) (1/2) - ((P lam)^[m] h) (r lam * (1/2)))
    (((P lam)^[m] h) (1/2) - ((P lam)^[m] h) (r lam * (1/2) + 1 - r lam))
  have hpk : 0 ≤ (r lam) ^ m * K := by positivity
  linarith

/-- **T40(c).**  For Lipschitz `h` the iterates `P^[m] h` converge uniformly on
`[0,1]` to a constant, at the geometric rate `r^m`. -/
theorem tendsto_const (hlam : 1 < lam) {K : ℝ} {h : ℝ → ℝ} (hK : LipBound K h) :
    ∃ c : ℝ, ∀ (m : ℕ), ∀ y ∈ Icc (0:ℝ) 1,
      |(P lam)^[m] h y - c| ≤ (2 * K / (1 - r lam)) * (r lam) ^ m := by
  have hr0 := r_pos hlam
  have hr1 := r_lt_one hlam
  have hKn : 0 ≤ K := hK.nonneg
  set u : ℕ → ℝ := fun m => (P lam)^[m] h (1/2) with hu
  have hcauchy : CauchySeq u :=
    cauchySeq_of_le_geometric (r lam) K hr1 (fun m => dist_midpoint_succ hlam hK m)
  obtain ⟨c, hc⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨c, ?_⟩
  intro m y hy
  have hmid : dist (u m) c ≤ K * (r lam) ^ m / (1 - r lam) :=
    dist_le_of_le_geometric_of_tendsto (r lam) K hr1
      (fun n => dist_midpoint_succ hlam hK n) hc m
  have hit := lipBound_iterate hlam m hK
  have hpt : |(P lam)^[m] h y - u m| ≤ (r lam) ^ m * K * 1 := by
    refine le_trans (hit y (1/2)) ?_
    have hb : |y - 1/2| ≤ 1 := by
      rw [abs_le]; constructor <;> [linarith [hy.1, hy.2]; linarith [hy.1, hy.2]]
    have hcoef : 0 ≤ (r lam) ^ m * K := by positivity
    exact mul_le_mul_of_nonneg_left hb hcoef
  have hden : 0 < 1 - r lam := by linarith
  have hpow : 0 < (r lam) ^ m := by positivity
  have hmid' : |u m - c| ≤ K * (r lam) ^ m / (1 - r lam) := by
    rwa [Real.dist_eq] at hmid
  have : |(P lam)^[m] h y - c| ≤ |(P lam)^[m] h y - u m| + |u m - c| := by
    have := abs_add_le ((P lam)^[m] h y - u m) (u m - c)
    simpa using this
  have hfin : |(P lam)^[m] h y - u m| + |u m - c| ≤ (2 * K / (1 - r lam)) * (r lam) ^ m := by
    have h1 : (r lam) ^ m * K * 1 = K * (r lam) ^ m := by ring
    have h2 : K * (r lam) ^ m ≤ K * (r lam) ^ m / (1 - r lam) := by
      rw [le_div_iff₀ hden]
      nlinarith [mul_nonneg hKn (le_of_lt hpow)]
    have h3 : (2 * K / (1 - r lam)) * (r lam) ^ m =
        K * (r lam) ^ m / (1 - r lam) + K * (r lam) ^ m / (1 - r lam) := by
      field_simp; ring
    rw [h3]
    have := hpt
    rw [h1] at this
    linarith [le_trans this h2, hmid']
  linarith

/-- The uniform-convergence phrasing of `tendsto_const`. -/
theorem tendstoUniformlyOn_const (hlam : 1 < lam) {K : ℝ} {h : ℝ → ℝ} (hK : LipBound K h) :
    ∃ c : ℝ, TendstoUniformlyOn (fun m y => (P lam)^[m] h y) (fun _ => c) atTop (Icc (0:ℝ) 1) := by
  obtain ⟨c, hc⟩ := tendsto_const hlam hK
  refine ⟨c, ?_⟩
  have hr0 := r_pos hlam
  have hr1 := r_lt_one hlam
  have hKn : 0 ≤ K := hK.nonneg
  have hlim : Tendsto (fun m : ℕ => (2 * K / (1 - r lam)) * (r lam) ^ m) atTop (𝓝 0) := by
    have : Tendsto (fun m : ℕ => (r lam) ^ m) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt hr0) hr1
    simpa using this.const_mul (2 * K / (1 - r lam))
  rw [Metric.tendstoUniformlyOn_iff]
  intro eps heps
  filter_upwards [hlim.eventually (gt_mem_nhds heps)] with m hm y hy
  rw [Real.dist_eq]
  calc |c - (P lam)^[m] h y| = |(P lam)^[m] h y - c| := abs_sub_comm _ _
    _ ≤ (2 * K / (1 - r lam)) * (r lam) ^ m := hc m y hy
    _ < eps := hm

/-! ### Integrability of the iterates (T43(a)) -/

/-- A function with a Lipschitz bound is continuous. -/
lemma continuous_of_lipBound {K : ℝ} {h : ℝ → ℝ} (hK : LipBound K h) : Continuous h :=
  (lipschitzWith_of_lipBound hK).continuous

/-- A function with a Lipschitz bound is bounded on `[0,1]`, by its value at the
midpoint plus the constant. -/
lemma abs_le_of_lipBound_on_Icc {K : ℝ} {h : ℝ → ℝ} (hK : LipBound K h)
    {y : ℝ} (hy : y ∈ Icc (0:ℝ) 1) : |h y| ≤ |h (1/2)| + K := by
  have hKn := hK.nonneg
  have hd : |y - 1/2| ≤ 1 := by
    rw [abs_le]; constructor <;> [linarith [hy.1, hy.2]; linarith [hy.1, hy.2]]
  have hb : |h y - h (1/2)| ≤ K := le_trans (hK y (1/2)) (by nlinarith)
  have := abs_sub_abs_le_abs_sub (h y) (h (1/2))
  linarith

/-- **T43(a).**  A function with a Lipschitz bound is integrable against any
probability measure carried by `[0,1]`: it is continuous, hence measurable, and
bounded where the measure lives. -/
theorem integrable_of_lipBound {nu : Measure ℝ} [IsProbabilityMeasure nu]
    (hsupp : nu (Icc (0:ℝ) 1)ᶜ = 0) {K : ℝ} {h : ℝ → ℝ} (hK : LipBound K h) :
    Integrable h nu := by
  refine Integrable.of_bound (continuous_of_lipBound hK).aestronglyMeasurable
    (|h (1/2)| + K) ?_
  have hae : ∀ᵐ y ∂nu, y ∈ Icc (0:ℝ) 1 := by
    rw [Filter.eventually_iff, mem_ae_iff]
    exact hsupp
  filter_upwards [hae] with y hy
  simpa [Real.norm_eq_abs] using abs_le_of_lipBound_on_Icc hK hy

/-- Every iterate of a Lipschitz function is integrable: no integrability
hypothesis is needed. -/
theorem integrable_iterate (hlam : 1 < lam) {nu : Measure ℝ} [IsProbabilityMeasure nu]
    (hsupp : nu (Icc (0:ℝ) 1)ᶜ = 0) {K : ℝ} {h : ℝ → ℝ} (hK : LipBound K h) (m : ℕ) :
    Integrable ((P lam)^[m] h) nu :=
  integrable_of_lipBound hsupp (lipBound_iterate hlam m hK)

/-! ### One-step invariance and its iterates (T43(b)) -/

/-- The regularity class the invariance hypothesis quantifies over: the
functions carrying some Lipschitz bound.  It is closed under `P`
(`lipBound_P`), which is exactly what the induction below needs. -/
def Lip (h : ℝ → ℝ) : Prop := ∃ K : ℝ, LipBound K h

lemma Lip.of_lipBound {K : ℝ} {h : ℝ → ℝ} (hK : LipBound K h) : Lip h := ⟨K, hK⟩

/-- **The invariance hypothesis in the shape a construction supplies**: one step,
quantified over Lipschitz test functions. -/
def InvariantOn (lam : ℝ) (nu : Measure ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, Lip φ → ∫ y, P lam φ y ∂nu = ∫ y, φ y ∂nu

/-- **T43(b).**  One-step invariance against Lipschitz test functions gives the
`m`-fold form.  The induction applies invariance to `P^[m] h`, not to `h`, which
is why the hypothesis has to be quantified over test functions. -/
theorem integral_iterate_eq (hlam : 1 < lam) {nu : Measure ℝ}
    (hinv : InvariantOn lam nu) {K : ℝ} {h : ℝ → ℝ} (hK : LipBound K h) :
    ∀ m : ℕ, ∫ y, ((P lam)^[m] h) y ∂nu = ∫ y, h y ∂nu := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply',
        hinv _ (Lip.of_lipBound (lipBound_iterate hlam m hK))]
      exact ih

/-! ### Identifying the constant, given an invariant measure -/

/-- **The identification of the limit constant, from the `m`-fold hypotheses.**
This is round 14's statement, kept as the general form; the usable version is
`const_eq_integral_of_invariant` below, which supplies both of its hypotheses
from one-step invariance. -/
theorem const_eq_integral_of_iterate_invariant (hlam : 1 < lam) {K : ℝ} {h : ℝ → ℝ}
    (hK : LipBound K h) {c : ℝ}
    (hc : ∀ (m : ℕ), ∀ y ∈ Icc (0:ℝ) 1,
      |(P lam)^[m] h y - c| ≤ (2 * K / (1 - r lam)) * (r lam) ^ m)
    {nu : Measure ℝ} [IsProbabilityMeasure nu] (hsupp : nu (Icc (0:ℝ) 1)ᶜ = 0)
    (hint : ∀ m : ℕ, Integrable ((P lam)^[m] h) nu)
    (hinv : ∀ m : ℕ, ∫ y, ((P lam)^[m] h) y ∂nu = ∫ y, h y ∂nu) :
    ∫ y, h y ∂nu = c := by
  have hr0 := r_pos hlam
  have hr1 := r_lt_one hlam
  have hKn : 0 ≤ K := hK.nonneg
  have hden : 0 < 1 - r lam := by linarith
  have hae : ∀ᵐ y ∂nu, y ∈ Icc (0:ℝ) 1 := by
    rw [Filter.eventually_iff, mem_ae_iff]
    exact hsupp
  have key : ∀ m : ℕ, |∫ y, h y ∂nu - c| ≤ (2 * K / (1 - r lam)) * (r lam) ^ m := by
    intro m
    have hsub : Integrable (fun y => ((P lam)^[m] h) y - c) nu :=
      (hint m).sub (integrable_const c)
    have hsplit : ∫ y, ((P lam)^[m] h) y ∂nu - c = ∫ y, (((P lam)^[m] h) y - c) ∂nu := by
      rw [integral_sub (hint m) (integrable_const c)]
      simp
    rw [← hinv m, hsplit]
    calc |∫ y, (((P lam)^[m] h) y - c) ∂nu| ≤ ∫ y, |((P lam)^[m] h) y - c| ∂nu := by
          simpa [Real.norm_eq_abs] using
            (norm_integral_le_integral_norm (μ := nu) (fun y => ((P lam)^[m] h) y - c))
      _ ≤ ∫ _y, (2 * K / (1 - r lam)) * (r lam) ^ m ∂nu := by
          refine integral_mono_ae hsub.abs (integrable_const _) ?_
          filter_upwards [hae] with y hy
          exact hc m y hy
      _ = (2 * K / (1 - r lam)) * (r lam) ^ m := by
          simp
  have hlim : Tendsto (fun m : ℕ => (2 * K / (1 - r lam)) * (r lam) ^ m) atTop (𝓝 0) := by
    have : Tendsto (fun m : ℕ => (r lam) ^ m) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt hr0) hr1
    simpa using this.const_mul (2 * K / (1 - r lam))
  have hle : |∫ y, h y ∂nu - c| ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall key)
  have : ∫ y, h y ∂nu - c = 0 := by
    have := abs_nonneg (∫ y, h y ∂nu - c)
    have habs : |∫ y, h y ∂nu - c| = 0 := le_antisymm hle this
    exact abs_eq_zero.1 habs
  linarith

/-- **T43.**  The identification of the limit constant, from the hypothesis a
construction of the invariant measure actually supplies: `nu` is a probability
measure carried by `[0,1]` which is invariant for `P` when tested against
Lipschitz functions.  Integrability is not assumed — it is proved
(`integrable_iterate`) — and the `m`-fold invariance is derived
(`integral_iterate_eq`). -/
theorem const_eq_integral_of_invariant (hlam : 1 < lam) {K : ℝ} {h : ℝ → ℝ}
    (hK : LipBound K h) {c : ℝ}
    (hc : ∀ (m : ℕ), ∀ y ∈ Icc (0:ℝ) 1,
      |(P lam)^[m] h y - c| ≤ (2 * K / (1 - r lam)) * (r lam) ^ m)
    {nu : Measure ℝ} [IsProbabilityMeasure nu] (hsupp : nu (Icc (0:ℝ) 1)ᶜ = 0)
    (hinv : InvariantOn lam nu) :
    ∫ y, h y ∂nu = c :=
  const_eq_integral_of_iterate_invariant hlam hK hc hsupp
    (fun m => integrable_iterate hlam hsupp hK m)
    (integral_iterate_eq hlam hinv hK)

/-- **Uniqueness of the invariant measure, on Lipschitz test functions.**  Two
probability measures carried by `[0,1]` and invariant for `P` integrate every
Lipschitz function alike: both integrals are the limit constant of the
iterates. -/
theorem integral_eq_of_invariant (hlam : 1 < lam) {K : ℝ} {h : ℝ → ℝ} (hK : LipBound K h)
    {nu1 nu2 : Measure ℝ} [IsProbabilityMeasure nu1] [IsProbabilityMeasure nu2]
    (hs1 : nu1 (Icc (0:ℝ) 1)ᶜ = 0) (hi1 : InvariantOn lam nu1)
    (hs2 : nu2 (Icc (0:ℝ) 1)ᶜ = 0) (hi2 : InvariantOn lam nu2) :
    ∫ y, h y ∂nu1 = ∫ y, h y ∂nu2 := by
  obtain ⟨c, hc⟩ := tendsto_const hlam hK
  rw [const_eq_integral_of_invariant hlam hK hc hs1 hi1,
    const_eq_integral_of_invariant hlam hK hc hs2 hi2]

/-- **T43, packaged.**  For a Lipschitz `h` and an invariant probability measure
carried by `[0,1]`, the iterates converge uniformly on `[0,1]` to `∫ h dnu`, at
the rate `r^m`. -/
theorem tendsto_integral_of_invariant (hlam : 1 < lam) {K : ℝ} {h : ℝ → ℝ}
    (hK : LipBound K h) {nu : Measure ℝ} [IsProbabilityMeasure nu]
    (hsupp : nu (Icc (0:ℝ) 1)ᶜ = 0) (hinv : InvariantOn lam nu) :
    ∀ (m : ℕ), ∀ y ∈ Icc (0:ℝ) 1,
      |(P lam)^[m] h y - ∫ z, h z ∂nu| ≤ (2 * K / (1 - r lam)) * (r lam) ^ m := by
  obtain ⟨c, hc⟩ := tendsto_const hlam hK
  rw [const_eq_integral_of_invariant hlam hK hc hsupp hinv]
  exact hc

end Contraction
end KnotGame
