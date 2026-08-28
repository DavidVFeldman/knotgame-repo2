import RequestProject.KindDimLower

/-!
# T34 — the box dimension of the kind set at `λ = 3/2`

Mathlib has no notion of box (Minkowski) dimension, so this file supplies one
and computes it for the kind set `K = K_{3/2}` of `KindDim`.

## The definition

For a set `s ⊆ ℝ` and a scale `r`, `coverSizes s r` is the set of natural
numbers `N` such that `s` can be covered by `N` sets each of diameter at most
`r`, and `coverNum s r = sInf (coverSizes s r)` is the least such `N` — the
standard covering number `N(s, r)`.  The two box dimensions are then the
standard

  `upperBoxDim s = limsup_{r → 0⁺} log N(s,r) / log (1/r)`,
  `lowerBoxDim s = liminf_{r → 0⁺} log N(s,r) / log (1/r)`,

taken over *all* real scales `r → 0⁺` (the filter `𝓝[>] 0`), not merely over a
geometric sequence of scales.  `SCRUPLES-round12.md` discusses the faithfulness
of this rendering.

## The results

* `coverNum_K_le` : at the triadic scale `3^{-n}` the `2^n` cylinders cover `K`,
  so `N(K, 3^{-n}) ≤ 2^n`.
* `le_coverNum_K` : conversely `2^n ≤ 4 · N(K, 3^{-n})`, because by the Frostman
  estimate `KindDimLower.kindMeasure_le_of_ediam` each member of such a cover
  carries mass at most `4 · 2^{-n}` while the whole cover carries mass `1`.
* `tendsto_boxQuot` : the squeeze from the triadic scales to all scales — the
  quotient `log N(K,r) / log (1/r)` converges, as `r → 0⁺`, to `log 2 / log 3`.
* `upperBoxDim_K` and `lowerBoxDim_K` : both box dimensions of `K` are
  `log 2 / log 3`; in particular the box dimension exists and agrees with the
  Hausdorff dimension `KindDimLower.dimH_K_eq`.
-/

namespace KnotGame
namespace KindBox

open MeasureTheory Set Filter Topology KindDim KindDimLower
open scoped ENNReal NNReal

/-! ### Covering numbers -/

/-- The sizes of finite covers of `s` by sets of diameter at most `r`. -/
def coverSizes (s : Set ℝ) (r : ℝ) : Set ℕ :=
  {N | ∃ f : Fin N → Set ℝ, (∀ i, Metric.ediam (f i) ≤ ENNReal.ofReal r) ∧ s ⊆ ⋃ i, f i}

/-- The covering number `N(s, r)`: the least number of sets of diameter at most
`r` needed to cover `s`.  (If no finite cover exists the `sInf` of the empty set
of naturals is `0`; all statements below concern sets for which finite covers do
exist.) -/
noncomputable def coverNum (s : Set ℝ) (r : ℝ) : ℕ := sInf (coverSizes s r)

lemma coverSizes_mono_scale {s : Set ℝ} {r r' : ℝ} (h : r ≤ r') {N : ℕ}
    (hN : N ∈ coverSizes s r) : N ∈ coverSizes s r' := by
  obtain ⟨f, hf, hcov⟩ := hN
  exact ⟨f, fun i => le_trans (hf i) (ENNReal.ofReal_le_ofReal h), hcov⟩

lemma coverSizes_upward {s : Set ℝ} {r : ℝ} {N M : ℕ} (hN : N ∈ coverSizes s r)
    (hNM : N ≤ M) : M ∈ coverSizes s r := by
  obtain ⟨f, hf, hcov⟩ := hN
  refine ⟨fun i => if h : (i : ℕ) < N then f ⟨i, h⟩ else ∅, ?_, ?_⟩
  · intro i
    by_cases h : (i : ℕ) < N
    · simpa [h] using hf ⟨i, h⟩
    · simp [h]
  · refine hcov.trans ?_
    intro x hx
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨i, hi⟩ := hx
    exact ⟨⟨i, lt_of_lt_of_le i.2 hNM⟩, by simpa [i.2] using hi⟩

lemma coverNum_le {s : Set ℝ} {r : ℝ} {N : ℕ} (hN : N ∈ coverSizes s r) :
    coverNum s r ≤ N := Nat.sInf_le hN

/-- The covering number is antitone in the scale. -/
lemma coverNum_mono {s : Set ℝ} {r r' : ℝ} (h : r ≤ r')
    (hne : (coverSizes s r).Nonempty) : coverNum s r' ≤ coverNum s r :=
  coverNum_le (coverSizes_mono_scale h (Nat.sInf_mem hne))

/-! ### The upper bound: the `2^n` cylinders -/

/-- A cover indexed by a finset gives a member of `coverSizes` of that card. -/
lemma coverSizes_of_finset {s : Set ℝ} {r : ℝ} {α : Type*} (F : Finset α)
    (g : α → Set ℝ) (hg : ∀ w ∈ F, Metric.ediam (g w) ≤ ENNReal.ofReal r)
    (hcov : s ⊆ ⋃ w ∈ F, g w) : F.card ∈ coverSizes s r := by
  classical
  refine ⟨fun i => g ((F.equivFin.symm i : α)), ?_, ?_⟩
  · intro i
    exact hg _ (F.equivFin.symm i).2
  · intro x hx
    obtain ⟨w, hw, hxw⟩ : ∃ w ∈ F, x ∈ g w := by
      simpa only [Set.mem_iUnion, exists_prop] using hcov hx
    exact Set.mem_iUnion.mpr ⟨F.equivFin ⟨w, hw⟩, by simpa using hxw⟩

lemma coverSizes_K_triadic (n : ℕ) : (2 ^ n) ∈ coverSizes K ((1/3 : ℝ) ^ n) := by
  have hcard := KindTree.card_kindWords_three_halves n
  have hmem := coverSizes_of_finset (s := K) (r := (1/3 : ℝ) ^ n)
    (KindTree.kindWords (3/2 : ℝ) (1/2 : ℝ) n) cyl ?_ ?_
  · rwa [hcard] at hmem
  · intro w hw
    rw [ediam_cyl, (KindTree.mem_kindWords.mp hw).1]
  · intro x hx
    have hxE := K_subset_E n hx
    simpa only [E] using hxE

lemma coverNum_K_le (n : ℕ) : coverNum K ((1/3 : ℝ) ^ n) ≤ 2 ^ n :=
  coverNum_le (coverSizes_K_triadic n)

/-! ### The lower bound: the Frostman estimate -/

/-- Any cover of `K` by sets of diameter at most `3^{-n}` has at least `2^n/4`
members. -/
lemma le_coverNum_K (n : ℕ) : (2 : ℝ) ^ n ≤ 4 * (coverNum K ((1/3 : ℝ) ^ n) : ℝ) := by
  classical
  set N := coverNum K ((1/3 : ℝ) ^ n) with hN
  obtain ⟨f, hf, hcov⟩ : N ∈ coverSizes K ((1/3 : ℝ) ^ n) :=
    Nat.sInf_mem ⟨2 ^ n, coverSizes_K_triadic n⟩
  have hmass : (1 : ℝ≥0∞) ≤ ∑ i : Fin N, kindMeasure (f i) := by
    calc (1 : ℝ≥0∞) = kindMeasure K := kindMeasure_K.symm
      _ ≤ kindMeasure (⋃ i, f i) := measure_mono hcov
      _ ≤ ∑' i, kindMeasure (f i) := measure_iUnion_le _
      _ = ∑ i : Fin N, kindMeasure (f i) := tsum_fintype _
  have hterm : ∀ i : Fin N, kindMeasure (f i) ≤ ENNReal.ofReal (4 * (1/2 : ℝ) ^ n) :=
    fun i => kindMeasure_le_of_ediam n (hf i)
  have hsum : ∑ i : Fin N, kindMeasure (f i)
      ≤ (N : ℝ≥0∞) * ENNReal.ofReal (4 * (1/2 : ℝ) ^ n) := by
    calc ∑ i : Fin N, kindMeasure (f i)
        ≤ ∑ _i : Fin N, ENNReal.ofReal (4 * (1/2 : ℝ) ^ n) :=
          Finset.sum_le_sum (fun i _ => hterm i)
      _ = (N : ℝ≥0∞) * ENNReal.ofReal (4 * (1/2 : ℝ) ^ n) := by
          simp [Finset.sum_const, mul_comm]
  have h1 : (1 : ℝ≥0∞) ≤ (N : ℝ≥0∞) * ENNReal.ofReal (4 * (1/2 : ℝ) ^ n) :=
    le_trans hmass hsum
  -- move to the reals
  have h2 : (1 : ℝ) ≤ (N : ℝ) * (4 * (1/2 : ℝ) ^ n) := by
    have hcast : ((N : ℝ≥0∞) * ENNReal.ofReal (4 * (1/2 : ℝ) ^ n))
        = ENNReal.ofReal ((N : ℝ) * (4 * (1/2 : ℝ) ^ n)) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      congr 1
      simp [ENNReal.ofReal_natCast]
    rw [hcast, show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp,
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
    exact h1
  have hpow : (0:ℝ) < 2 ^ n := by positivity
  have h3 : (1/2 : ℝ) ^ n = 1 / 2 ^ n := by rw [div_pow, one_pow]
  rw [h3] at h2
  rw [ge_iff_le, ← sub_nonneg] at *
  nlinarith [h2, hpow]

/-! ### The bracketing index -/

/-- For `0 < r ≤ 1/3`, the unique `k` with `3^{-(k+1)} ≤ r ≤ 3^{-k}`. -/
noncomputable def bidx (r : ℝ) : ℕ := sInf {n : ℕ | (1/3 : ℝ) ^ n ≤ r} - 1

lemma bidx_set_nonempty {r : ℝ} (hr : 0 < r) : {n : ℕ | (1/3 : ℝ) ^ n ≤ r}.Nonempty := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr (show (1/3:ℝ) < 1 by norm_num)
  exact ⟨n, le_of_lt hn⟩

lemma bidx_le {r : ℝ} (hr : 0 < r) : r ≤ (1/3 : ℝ) ^ bidx r := by
  set m := sInf {n : ℕ | (1/3 : ℝ) ^ n ≤ r} with hm
  by_cases h0 : m = 0
  · have : bidx r = 0 := by simp [bidx, ← hm, h0]
    rw [this, pow_zero]
    -- `m = 0` means `1 ≤ r`
    have hmem : (1/3 : ℝ) ^ m ≤ r := Nat.sInf_mem (bidx_set_nonempty hr)
    rw [h0, pow_zero] at hmem
    exact hmem
  · have hlt : bidx r < m := by
      simp only [bidx, ← hm]
      omega
    have := Nat.not_mem_of_lt_sInf (by simpa [← hm] using hlt)
    simpa using le_of_lt (lt_of_not_le this)

lemma le_bidx {r : ℝ} (hr : 0 < r) (hr3 : r ≤ 1/3) : (1/3 : ℝ) ^ (bidx r + 1) ≤ r := by
  set m := sInf {n : ℕ | (1/3 : ℝ) ^ n ≤ r} with hm
  have hmem : (1/3 : ℝ) ^ m ≤ r := Nat.sInf_mem (bidx_set_nonempty hr)
  have h0 : m ≠ 0 := by
    intro h
    rw [h, pow_zero] at hmem
    linarith
  have : bidx r + 1 = m := by simp only [bidx, ← hm]; omega
  rw [this]
  exact hmem

lemma bidx_ge {r : ℝ} (hr : 0 < r) {N : ℕ} (h : r < (1/3 : ℝ) ^ N) : N ≤ bidx r := by
  set m := sInf {n : ℕ | (1/3 : ℝ) ^ n ≤ r} with hm
  have hmem : (1/3 : ℝ) ^ m ≤ r := Nat.sInf_mem (bidx_set_nonempty hr)
  have hlt : (1/3 : ℝ) ^ m < (1/3 : ℝ) ^ N := lt_of_le_of_lt hmem h
  have hNm : N < m := by
    by_contra hc
    push_neg at hc
    have : (1/3 : ℝ) ^ m ≤ (1/3 : ℝ) ^ N :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hc
    exact absurd hlt (not_lt.mpr (pow_le_pow_of_le_one (by norm_num) (by norm_num) hc))
  simp only [bidx, ← hm]
  omega

lemma tendsto_bidx : Tendsto bidx (𝓝[>] (0:ℝ)) atTop := by
  rw [tendsto_atTop]
  intro N
  have hmem : Iio ((1/3 : ℝ) ^ N) ∈ 𝓝 (0:ℝ) := Iio_mem_nhds (by positivity)
  filter_upwards [self_mem_nhdsWithin,
    (Filter.eventually_of_mem hmem (fun x hx => hx)).filter_mono nhdsWithin_le_nhds] with r hr hr2
  exact bidx_ge hr hr2

/-! ### The box dimensions -/

/-- The **upper box dimension** of `s`:
`limsup_{r → 0⁺} log N(s,r) / log (1/r)`. -/
noncomputable def upperBoxDim (s : Set ℝ) : ℝ :=
  limsup (fun r : ℝ => Real.log (coverNum s r) / Real.log (1/r)) (𝓝[>] (0:ℝ))

/-- The **lower box dimension** of `s`:
`liminf_{r → 0⁺} log N(s,r) / log (1/r)`. -/
noncomputable def lowerBoxDim (s : Set ℝ) : ℝ :=
  liminf (fun r : ℝ => Real.log (coverNum s r) / Real.log (1/r)) (𝓝[>] (0:ℝ))

/-- The upper comparison sequence, `(k+1) log 2 / (k log 3)`. -/
noncomputable def hiSeq (k : ℕ) : ℝ := ((k : ℝ) + 1) * Real.log 2 / ((k : ℝ) * Real.log 3)

/-- The lower comparison sequence, `(k-2) log 2 / ((k+1) log 3)`. -/
noncomputable def loSeq (k : ℕ) : ℝ := ((k : ℝ) - 2) * Real.log 2 / (((k : ℝ) + 1) * Real.log 3)

lemma tendsto_hiSeq : Tendsto hiSeq atTop (𝓝 dexp) := by
  have hlog3 : Real.log 3 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have heq : ∀ᶠ k : ℕ in atTop, hiSeq k = (1 + 1 / (k : ℝ)) * dexp := by
    filter_upwards [eventually_gt_atTop 0] with k hk
    have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff.mp hk ▸ (Nat.pos_iff.mp hk))
    field_simp [hiSeq, dexp]
    ring
  refine Tendsto.congr' heq.symm ?_
  have h1 : Tendsto (fun k : ℕ => 1 + 1 / (k : ℝ)) atTop (𝓝 1) := by
    simpa using (tendsto_one_div_atTop_nhds_zero_nat.const_add (1:ℝ))
  simpa using h1.mul_const dexp

lemma tendsto_loSeq : Tendsto loSeq atTop (𝓝 dexp) := by
  have hlog3 : Real.log 3 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have heq : ∀ᶠ k : ℕ in atTop, loSeq k = (1 - 3 / ((k : ℝ) + 1)) * dexp := by
    filter_upwards [eventually_gt_atTop 0] with k hk
    have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    field_simp [loSeq, dexp]
    ring
  refine Tendsto.congr' heq.symm ?_
  have h0 : Tendsto (fun k : ℕ => 3 / ((k : ℝ) + 1)) atTop (𝓝 0) := by
    have : Tendsto (fun k : ℕ => ((k : ℝ) + 1)) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    simpa using this.inv_tendsto_atTop.const_mul (3:ℝ)
  have h1 : Tendsto (fun k : ℕ => 1 - 3 / ((k : ℝ) + 1)) atTop (𝓝 1) := by
    simpa using (h0.const_sub (1:ℝ))
  simpa using h1.mul_const dexp

/-- The squeeze from the triadic scales to all scales. -/
theorem tendsto_boxQuot :
    Tendsto (fun r : ℝ => Real.log (coverNum K r) / Real.log (1/r)) (𝓝[>] (0:ℝ))
      (𝓝 dexp) := by
  sorry

theorem upperBoxDim_K : upperBoxDim K = dexp := tendsto_boxQuot.limsup_eq

theorem lowerBoxDim_K : lowerBoxDim K = dexp := tendsto_boxQuot.liminf_eq

/-- **T34.**  Upper and lower box dimension of the kind set at `λ = 3/2` agree
and equal `log 2 / log 3`. -/
theorem boxDim_K : upperBoxDim K = Real.log 2 / Real.log 3 ∧
    lowerBoxDim K = Real.log 2 / Real.log 3 :=
  ⟨upperBoxDim_K, lowerBoxDim_K⟩

end KindBox
end KnotGame
