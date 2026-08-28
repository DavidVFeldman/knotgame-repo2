import RequestProject.KindTree

/-!
# T38 — the kind set at `λ = 3/2` is null and of dimension at most `log 2 / log 3`

The paper's `prop:kinddim` reads, at `λ = 3/2`:

> `K_{3/2}` has exactly `2^n` cylinders of length `3^{-n}` at every level `n`;
> hence it has Lebesgue measure zero and Hausdorff and box dimension exactly
> `log 2 / log 3`.

The cylinder count is round 8's `KindTree.card_kindWords_three_halves`.  This
file turns the count into the measure and dimension statements.

* `cval w` is the base-three value of a word of moves under the paper's coding
  `L, M, R ↦ 0, 1, 2`, and `cyl w` the closed cylinder it names, an interval of
  length `3^{-|w|}`.
* `E n` is the union of the level-`n` cylinders of the survival tree of `1/2`
  and `K` — the paper's `K_{3/2}` — is their intersection over all `n`.
* `volume_K` : `K` is Lebesgue null.
* `dimH_K_le` : `dimH K ≤ log 2 / log 3`.

## Conventions (SCRUPLES)

* Cylinders are taken **closed**, `[cval w, cval w + 3^{-|w|}]`; this only makes
  `K` larger, so both statements are the stronger reading.  With closed
  cylinders `K` is exactly the set of points all of whose base-three prefixes
  code a surviving word, endpoints included.
* Nothing here uses, or asserts, self-similarity; `E (n+1) ⊆ E n` is proved
  from the tree structure (`E_succ_subset`).
-/

namespace KnotGame
namespace KindDim

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

/-! ### Base-three coding of words -/

/-- The base-three digit of a move: `L, M, R ↦ 0, 1, 2`. -/
def dig : Move → ℕ
  | Move.L => 0
  | Move.M => 1
  | Move.R => 2

lemma dig_le_two (m : Move) : dig m ≤ 2 := by cases m <;> simp [dig]

/-- The base-three value of a word of moves. -/
noncomputable def cval : List Move → ℝ
  | [] => 0
  | m :: w => ((dig m : ℝ) + cval w) / 3

@[simp] lemma cval_nil : cval [] = 0 := rfl

@[simp] lemma cval_cons (m : Move) (w : List Move) :
    cval (m :: w) = ((dig m : ℝ) + cval w) / 3 := rfl

lemma cval_nonneg : ∀ w : List Move, 0 ≤ cval w
  | [] => le_refl 0
  | m :: w => by
      have := cval_nonneg w
      have : (0:ℝ) ≤ (dig m : ℝ) := by positivity
      simp only [cval_cons]
      have hw := cval_nonneg w
      linarith

/-- A word of length `n` names an interval `[cval w, cval w + 3^{-n}]` inside
`[0,1]`. -/
lemma cval_add_le_one : ∀ w : List Move, cval w + (1/3 : ℝ) ^ w.length ≤ 1
  | [] => by norm_num
  | m :: w => by
      have hw := cval_add_le_one w
      have hd : (dig m : ℝ) ≤ 2 := by exact_mod_cast dig_le_two m
      simp only [cval_cons, List.length_cons, pow_succ]
      nlinarith [cval_nonneg w]

/-- The closed base-three cylinder named by a word. -/
def cyl (w : List Move) : Set ℝ := Icc (cval w) (cval w + (1/3 : ℝ) ^ w.length)

lemma cyl_subset_Icc (w : List Move) : cyl w ⊆ Icc (0:ℝ) 1 := by
  intro x hx
  exact ⟨le_trans (cval_nonneg w) hx.1, le_trans hx.2 (cval_add_le_one w)⟩

/-- Appending a letter refines the cylinder. -/
lemma cval_append_singleton : ∀ (w : List Move) (m : Move),
    cval (w ++ [m]) = cval w + (dig m : ℝ) * (1/3 : ℝ) ^ (w.length + 1)
  | [], m => by simp [cval]; ring
  | a :: w, m => by
      have := cval_append_singleton w m
      simp only [List.cons_append, cval_cons, this, List.length_cons]
      ring

lemma cyl_append_subset (w : List Move) (m : Move) : cyl (w ++ [m]) ⊆ cyl w := by
  intro x hx
  have hd : (dig m : ℝ) ≤ 2 := by exact_mod_cast dig_le_two m
  have hd0 : (0:ℝ) ≤ (dig m : ℝ) := by positivity
  have hlen : (w ++ [m]).length = w.length + 1 := by simp
  have hpow : (0:ℝ) < (1/3 : ℝ) ^ (w.length + 1) := by positivity
  rw [cyl, hlen, cval_append_singleton] at hx
  refine ⟨by nlinarith [hx.1], ?_⟩
  have : cval w + (dig m : ℝ) * (1/3:ℝ)^(w.length+1) + (1/3:ℝ)^(w.length+1)
      ≤ cval w + (1/3:ℝ)^w.length := by
    have : ((dig m : ℝ) + 1) * (1/3:ℝ)^(w.length+1) ≤ 3 * (1/3:ℝ)^(w.length+1) := by
      nlinarith
    rw [pow_succ] at this ⊢
    nlinarith
  linarith [hx.2]

/-! ### The kind set -/

/-- The union of the level-`n` cylinders of the survival tree of `1/2` at
`λ = 3/2`. -/
noncomputable def E (n : ℕ) : Set ℝ :=
  ⋃ w ∈ KindTree.kindWords (3/2 : ℝ) (1/2 : ℝ) n, cyl w

/-- The kind set `K_{3/2}` of the paper: the points of `[0,1]` all of whose
base-three prefixes code a word survived by a knot at `1/2`. -/
noncomputable def K : Set ℝ := ⋂ n, E n

lemma K_subset_E (n : ℕ) : K ⊆ E n := Set.iInter_subset _ n

lemma E_succ_subset (n : ℕ) : E (n + 1) ⊆ E n := by
  intro x hx
  simp only [E, Set.mem_iUnion] at hx ⊢
  obtain ⟨w, hw, hxw⟩ := hx
  rw [KindTree.mem_kindWords] at hw
  obtain ⟨hlen, hsurv⟩ := hw
  -- split off the last letter
  obtain ⟨v, m, rfl⟩ : ∃ (v : List Move) (m : Move), w = v ++ [m] := by
    rcases List.eq_nil_or_concat w with h | ⟨v, m, h⟩
    · subst h; simp at hlen
    · exact ⟨v, m, by simpa using h⟩
  refine ⟨v, ?_, cyl_append_subset v m hxw⟩
  rw [KindTree.mem_kindWords]
  rw [survivesWord_append] at hsurv
  refine ⟨by simpa using hlen, hsurv.1⟩

/-! ### `K` is Lebesgue null -/

lemma volume_cyl (w : List Move) :
    volume (cyl w) = ENNReal.ofReal ((1/3 : ℝ) ^ w.length) := by
  rw [cyl, Real.volume_Icc, add_sub_cancel_left]

lemma ediam_cyl (w : List Move) :
    Metric.ediam (cyl w) = ENNReal.ofReal ((1/3 : ℝ) ^ w.length) := by
  rw [cyl, Real.ediam_Icc, add_sub_cancel_left]

lemma volume_E_le (n : ℕ) : volume (E n) ≤ ENNReal.ofReal ((2/3 : ℝ) ^ n) := by
  have h := measure_biUnion_finset_le (μ := (volume : Measure ℝ))
    (KindTree.kindWords (3/2 : ℝ) (1/2 : ℝ) n) cyl
  refine le_trans h ?_
  have hterm : ∀ w ∈ KindTree.kindWords (3/2 : ℝ) (1/2 : ℝ) n,
      volume (cyl w) = ENNReal.ofReal ((1/3 : ℝ) ^ n) := by
    intro w hw
    rw [volume_cyl, (KindTree.mem_kindWords.mp hw).1]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const,
    KindTree.card_kindWords_three_halves n, nsmul_eq_mul]
  rw [show ((2:ℝ)/3) ^ n = (2:ℝ)^n * (1/3:ℝ)^n by rw [← mul_pow]; norm_num]
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
  simp

/-- **Paper `prop:kinddim`, the null statement.**  The kind set at `λ = 3/2`
has Lebesgue measure zero. -/
theorem volume_K : volume K = 0 := by
  refine le_antisymm ?_ (zero_le _)
  have htend : Tendsto (fun n : ℕ => ENNReal.ofReal ((2/3 : ℝ) ^ n)) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => ((2/3 : ℝ)) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have h2 := (ENNReal.continuous_ofReal.tendsto 0).comp h
    rwa [ENNReal.ofReal_zero] at h2
  refine ge_of_tendsto htend (Eventually.of_forall fun n => ?_)
  exact le_trans (measure_mono (K_subset_E n)) (volume_E_le n)

/-! ### The Hausdorff dimension -/

/-- The exponent `log 2 / log 3`. -/
noncomputable def dexp : ℝ := Real.log 2 / Real.log 3

lemma dexp_pos : 0 < dexp := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  exact div_pos h2 h3

lemma dexp_lt_one : dexp < 1 := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlt : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  rw [dexp, div_lt_one h3]
  exact hlt

/-- The defining property of the exponent: a cylinder of length `3^{-n}` has
`dexp`-content `2^{-n}`. -/
lemma rpow_third_dexp : ((1:ℝ)/3) ^ dexp = 1/2 := by
  have h3 : (0:ℝ) < 1/3 := by norm_num
  rw [Real.rpow_def_of_pos h3]
  have hl3 : Real.log ((1:ℝ)/3) = -Real.log 3 := by
    rw [one_div, Real.log_inv]
  have hne : Real.log 3 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rw [hl3]
  have hkey : -Real.log 3 * dexp = -Real.log 2 := by
    rw [dexp]; field_simp
  rw [hkey, Real.exp_neg, Real.exp_log (by norm_num)]
  norm_num

lemma rpow_pow_third_dexp (n : ℕ) : (((1:ℝ)/3) ^ n) ^ dexp = (1/2 : ℝ) ^ n := by
  rw [← Real.rpow_natCast ((1:ℝ)/3) n, ← Real.rpow_mul (by norm_num), mul_comm,
    Real.rpow_mul (by norm_num), rpow_third_dexp, Real.rpow_natCast]

/-- **Paper `prop:kinddim`, the dimension bound.**  The kind set at `λ = 3/2`
has Hausdorff dimension at most `log 2 / log 3`. -/
theorem dimH_K_le : dimH K ≤ ENNReal.ofReal dexp := by
  have hr : Tendsto (fun n : ℕ => ENNReal.ofReal ((1/3 : ℝ) ^ n)) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => ((1/3 : ℝ)) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have h2 := (ENNReal.continuous_ofReal.tendsto 0).comp h
    rwa [ENNReal.ofReal_zero] at h2
  have hdiam : ∀ (n : ℕ) (i : {w // w ∈ KindTree.kindWords (3/2 : ℝ) (1/2 : ℝ) n}),
      Metric.ediam (cyl i.1) = ENNReal.ofReal ((1/3 : ℝ) ^ n) := by
    intro n i
    rw [ediam_cyl, (KindTree.mem_kindWords.mp i.2).1]
  have ht : ∀ᶠ n in atTop, ∀ i : {w // w ∈ KindTree.kindWords (3/2 : ℝ) (1/2 : ℝ) n},
      Metric.ediam (cyl i.1) ≤ ENNReal.ofReal ((1/3 : ℝ) ^ n) := by
    filter_upwards with n i using le_of_eq (hdiam n i)
  have hst : ∀ᶠ n in atTop,
      K ⊆ ⋃ i : {w // w ∈ KindTree.kindWords (3/2 : ℝ) (1/2 : ℝ) n}, cyl i.1 := by
    filter_upwards with n
    intro x hx
    have hxE := K_subset_E n hx
    simp only [E, Set.mem_iUnion] at hxE
    obtain ⟨w, hw, hxw⟩ := hxE
    exact Set.mem_iUnion.mpr ⟨⟨w, hw⟩, hxw⟩
  have hle := Measure.hausdorffMeasure_le_liminf_sum (X := ℝ)
    (ι := fun n : ℕ => {w // w ∈ KindTree.kindWords (3/2 : ℝ) (1/2 : ℝ) n})
    dexp K (fun n => ENNReal.ofReal ((1/3 : ℝ) ^ n)) hr (fun n i => cyl i.1) ht hst
  have hsum : ∀ n : ℕ,
      ∑ i : {w // w ∈ KindTree.kindWords (3/2 : ℝ) (1/2 : ℝ) n},
        Metric.ediam (cyl i.1) ^ dexp = 1 := by
    intro n
    have hterm : ∀ i : {w // w ∈ KindTree.kindWords (3/2 : ℝ) (1/2 : ℝ) n},
        Metric.ediam (cyl i.1) ^ dexp = ENNReal.ofReal ((1/2 : ℝ) ^ n) := by
      intro i
      rw [hdiam n i, ENNReal.ofReal_rpow_of_nonneg (by positivity) (le_of_lt dexp_pos),
        rpow_pow_third_dexp]
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_const, Finset.card_univ,
      Fintype.card_coe, KindTree.card_kindWords_three_halves n, nsmul_eq_mul]
    rw [ENNReal.ofReal_pow (by norm_num),
      show ENNReal.ofReal ((1:ℝ)/2) = (2 : ℝ≥0∞)⁻¹ by
        rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
        norm_num,
      ← ENNReal.inv_pow,
      show (((2:ℕ) ^ n : ℕ) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ n by push_cast; ring]
    exact ENNReal.mul_inv_cancel (by simp) (by simp)
  have hmeas : μH[dexp] K ≤ 1 := by
    refine le_trans hle ?_
    simp only [hsum]
    simp
  have hnt : μH[(dexp.toNNReal : ℝ)] K ≠ ∞ := by
    rw [Real.coe_toNNReal _ (le_of_lt dexp_pos)]
    exact ne_top_of_le_ne_top (by simp) hmeas
  exact dimH_le_of_hausdorffMeasure_ne_top hnt

end KindDim
end KnotGame
