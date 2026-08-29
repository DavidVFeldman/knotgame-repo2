import RequestProject.KindDimLower

/-!
# T36 — the box dimension of the kind set at `λ = 3/2`

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
geometric sequence of scales.  `SCRUPLES-round13.md` discusses the
faithfulness of this rendering.

## The results

* `coverNum_K_le` : at the triadic scale `3^{-n}` the `2^n` cylinders cover `K`,
  so `N(K, 3^{-n}) ≤ 2^n`.
* `le_coverNum_K` : conversely `2^n ≤ 4 · N(K, 3^{-n})`, because by the Frostman
  estimate `KindLower.kindMeasure_le_of_ediam` each member of such a cover
  carries mass at most `4 · 2^{-n}` while the whole cover carries mass `1`.
* `tendsto_boxQuot` : the squeeze from the triadic scales to all scales — the
  quotient `log N(K,r) / log (1/r)` converges, as `r → 0⁺`, to `log 2 / log 3`.
* `upperBoxDim_K` and `lowerBoxDim_K` : both box dimensions of `K` are
  `log 2 / log 3`; in particular the box dimension exists and agrees with the
  Hausdorff dimension `KindLower.dimH_K_eq`.

## Repair note

This file is the round-13 repair of the round-12 `KindBox.lean` recorded in
`UNBUILT.md`.  The old file had never elaborated: it opened a namespace
`KindDimLower` that does not exist (the namespace of `KindDimLower.lean` is
`KnotGame.KindLower`), which made the whole `open` line fail and every name it
was to bring into scope unknown; the bracketing index was built on `sInf` with
a non-strict inequality and appealed to a nonexistent lemma; and the squeeze
`tendsto_boxQuot`, the mathematical heart of the file, was left unproved.
-/

namespace KnotGame
namespace KindBox

open MeasureTheory Set Filter Topology KindDim KindLower
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

lemma coverSizes_K_nonempty (n : ℕ) : (coverSizes K ((1/3 : ℝ) ^ n)).Nonempty :=
  ⟨2 ^ n, coverSizes_K_triadic n⟩

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
      simp [ENNReal.ofReal_natCast]
    rw [hcast, show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp,
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
    exact h1
  have hpow : (0:ℝ) < 2 ^ n := by positivity
  have h3 : (1/2 : ℝ) ^ n = 1 / 2 ^ n := by rw [div_pow, one_pow]
  rw [h3] at h2
  have h4 : (N : ℝ) * (4 * (1 / 2 ^ n)) = 4 * (N:ℝ) / 2 ^ n := by ring
  rw [h4, le_div_iff₀ hpow] at h2
  linarith

/-! ### The bracketing index -/

/-- For `0 < r ≤ 1/3`, the index `k = bidx r` brackets `r` triadically:
`3^{-(k+1)} < r ≤ 3^{-k}`. -/
noncomputable def bidx (r : ℝ) : ℕ := sInf {n : ℕ | (1/3 : ℝ) ^ n < r} - 1

lemma bidx_set_nonempty {r : ℝ} (hr : 0 < r) : {n : ℕ | (1/3 : ℝ) ^ n < r}.Nonempty :=
  exists_pow_lt_of_lt_one hr (by norm_num)

lemma sInf_pos_of_le_third {r : ℝ} (hr : 0 < r) (hr3 : r ≤ 1/3) :
    0 < sInf {n : ℕ | (1/3 : ℝ) ^ n < r} := by
  rcases Nat.eq_zero_or_pos (sInf {n : ℕ | (1/3 : ℝ) ^ n < r}) with h | h
  · exfalso
    have hmem : (1/3 : ℝ) ^ sInf {n : ℕ | (1/3 : ℝ) ^ n < r} < r :=
      Nat.sInf_mem (bidx_set_nonempty hr)
    rw [h, pow_zero] at hmem
    linarith
  · exact h

lemma bidx_succ_lt {r : ℝ} (hr : 0 < r) (hr3 : r ≤ 1/3) : (1/3 : ℝ) ^ (bidx r + 1) < r := by
  have hpos := sInf_pos_of_le_third (r := r) hr hr3
  have hmem : (1/3 : ℝ) ^ sInf {n : ℕ | (1/3 : ℝ) ^ n < r} < r :=
    Nat.sInf_mem (bidx_set_nonempty hr)
  have hEq : bidx r + 1 = sInf {n : ℕ | (1/3 : ℝ) ^ n < r} := by
    simp only [bidx]; omega
  rw [hEq]
  exact hmem

lemma le_bidx_pow {r : ℝ} (hr : 0 < r) (hr3 : r ≤ 1/3) : r ≤ (1/3 : ℝ) ^ bidx r := by
  by_contra hc
  push_neg at hc
  have hle : sInf {n : ℕ | (1/3 : ℝ) ^ n < r} ≤ bidx r := Nat.sInf_le hc
  have hpos := sInf_pos_of_le_third (r := r) hr hr3
  simp only [bidx] at hle
  omega

lemma bidx_ge {r : ℝ} (hr : 0 < r) {N : ℕ} (h : r < (1/3 : ℝ) ^ N) : N ≤ bidx r := by
  have hmem : (1/3 : ℝ) ^ sInf {n : ℕ | (1/3 : ℝ) ^ n < r} < r :=
    Nat.sInf_mem (bidx_set_nonempty hr)
  have hlt : N < sInf {n : ℕ | (1/3 : ℝ) ^ n < r} := by
    by_contra hc
    push_neg at hc
    have : (1/3 : ℝ) ^ N ≤ (1/3 : ℝ) ^ sInf {n : ℕ | (1/3 : ℝ) ^ n < r} :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hc
    linarith
  simp only [bidx]
  omega

lemma tendsto_bidx : Tendsto bidx (𝓝[>] (0:ℝ)) atTop := by
  rw [tendsto_atTop]
  intro N
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0:ℝ) < (1/3:ℝ) ^ N by positivity))]
    with r hr hr2
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
  have heq : (fun k : ℕ => (1 + 1 / (k : ℝ)) * dexp) =ᶠ[atTop] hiSeq := by
    filter_upwards [eventually_gt_atTop 0] with k hk
    have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
    rw [hiSeq, dexp]
    field_simp
  refine Tendsto.congr' heq ?_
  have h1 : Tendsto (fun k : ℕ => 1 + 1 / (k : ℝ)) atTop (𝓝 1) := by
    simpa using (tendsto_one_div_atTop_nhds_zero_nat.const_add (1:ℝ))
  simpa using h1.mul_const dexp

lemma tendsto_loSeq : Tendsto loSeq atTop (𝓝 dexp) := by
  have hlog3 : Real.log 3 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have heq : (fun k : ℕ => (1 - 3 / ((k : ℝ) + 1)) * dexp) =ᶠ[atTop] loSeq := by
    filter_upwards [eventually_gt_atTop 0] with k _
    have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    rw [loSeq, dexp]
    field_simp
    ring
  refine Tendsto.congr' heq ?_
  have h0 : Tendsto (fun k : ℕ => 3 / ((k : ℝ) + 1)) atTop (𝓝 0) := by
    have h : Tendsto (fun k : ℕ => ((k : ℝ) + 1)) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    simpa using h.inv_tendsto_atTop.const_mul (3:ℝ)
  have h1 : Tendsto (fun k : ℕ => 1 - 3 / ((k : ℝ) + 1)) atTop (𝓝 1) := by
    simpa using (h0.const_sub (1:ℝ))
  simpa using h1.mul_const dexp

/-! ### The scale-by-scale bracketing of the covering number -/

section Bracket

variable {r : ℝ}

lemma coverNum_K_le_bidx (hr : 0 < r) (hr3 : r ≤ 1/3) :
    coverNum K r ≤ 2 ^ (bidx r + 1) := by
  refine le_trans (coverNum_mono (le_of_lt (bidx_succ_lt hr hr3))
    (coverSizes_K_nonempty (bidx r + 1))) ?_
  exact coverNum_K_le _

lemma le_coverNum_K_bidx (hr : 0 < r) (hr3 : r ≤ 1/3) :
    (2 : ℝ) ^ bidx r ≤ 4 * (coverNum K r : ℝ) := by
  have hne : (coverSizes K r).Nonempty :=
    ⟨2 ^ (bidx r + 1), coverSizes_mono_scale (le_of_lt (bidx_succ_lt hr hr3))
      (coverSizes_K_triadic (bidx r + 1))⟩
  have hmono : coverNum K ((1/3 : ℝ) ^ bidx r) ≤ coverNum K r :=
    coverNum_mono (le_bidx_pow hr hr3) hne
  have := le_coverNum_K (bidx r)
  have hcast : (coverNum K ((1/3 : ℝ) ^ bidx r) : ℝ) ≤ (coverNum K r : ℝ) := by
    exact_mod_cast hmono
  linarith

lemma log_inv_lower (hr : 0 < r) (hr3 : r ≤ 1/3) :
    (bidx r : ℝ) * Real.log 3 ≤ Real.log (1/r) := by
  have h := le_bidx_pow hr hr3
  have hlog : Real.log r ≤ Real.log ((1/3 : ℝ) ^ bidx r) := Real.log_le_log hr h
  rw [Real.log_pow] at hlog
  have h13 : Real.log (1/3 : ℝ) = -Real.log 3 := by
    rw [one_div, Real.log_inv]
  rw [h13] at hlog
  rw [one_div, Real.log_inv]
  nlinarith [hlog]

lemma log_inv_upper (hr : 0 < r) (hr3 : r ≤ 1/3) :
    Real.log (1/r) ≤ ((bidx r : ℝ) + 1) * Real.log 3 := by
  have h := bidx_succ_lt hr hr3
  have hlog : Real.log ((1/3 : ℝ) ^ (bidx r + 1)) ≤ Real.log r :=
    Real.log_le_log (by positivity) (le_of_lt h)
  rw [Real.log_pow] at hlog
  have h13 : Real.log (1/3 : ℝ) = -Real.log 3 := by
    rw [one_div, Real.log_inv]
  rw [h13] at hlog
  rw [one_div, Real.log_inv]
  push_cast at hlog
  nlinarith [hlog]

lemma log_coverNum_le (hr : 0 < r) (hr3 : r ≤ 1/3) :
    Real.log (coverNum K r) ≤ ((bidx r : ℝ) + 1) * Real.log 2 := by
  rcases Nat.eq_zero_or_pos (coverNum K r) with h0 | hpos
  · rw [h0]
    have : Real.log ((0:ℕ) : ℝ) = 0 := by norm_num
    rw [this]
    have : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  · have hle : (coverNum K r : ℝ) ≤ (2:ℝ) ^ (bidx r + 1) := by
      exact_mod_cast coverNum_K_le_bidx hr hr3
    have := Real.log_le_log (by exact_mod_cast hpos) hle
    rwa [Real.log_pow, show ((bidx r + 1 : ℕ) : ℝ) = (bidx r : ℝ) + 1 by push_cast; ring] at this

lemma le_log_coverNum (hr : 0 < r) (hr3 : r ≤ 1/3) :
    ((bidx r : ℝ) - 2) * Real.log 2 ≤ Real.log (coverNum K r) := by
  have hmain := le_coverNum_K_bidx hr hr3
  have hquart : (2:ℝ) ^ bidx r / 4 ≤ (coverNum K r : ℝ) := by linarith
  have hposq : (0:ℝ) < (2:ℝ) ^ bidx r / 4 := by positivity
  have hlog := Real.log_le_log hposq hquart
  have hcalc : Real.log ((2:ℝ) ^ bidx r / 4) = (bidx r : ℝ) * Real.log 2 - 2 * Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_pow]
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast; ring
    rw [h4]
  rw [hcalc] at hlog
  nlinarith [hlog]

lemma boxQuot_le_hiSeq (hr : 0 < r) (hr3 : r ≤ 1/3) (hk : 3 ≤ bidx r) :
    Real.log (coverNum K r) / Real.log (1/r) ≤ hiSeq (bidx r) := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hkR : (3:ℝ) ≤ (bidx r : ℝ) := by exact_mod_cast hk
  have hden : 0 < (bidx r : ℝ) * Real.log 3 := by nlinarith
  have hd : 0 < Real.log (1/r) := lt_of_lt_of_le hden (log_inv_lower hr hr3)
  rw [hiSeq, div_le_div_iff₀ hd hden]
  have h1 := log_coverNum_le hr hr3
  have h2 := log_inv_lower hr hr3
  have hB : 0 ≤ ((bidx r : ℝ) + 1) * Real.log 2 := by positivity
  calc Real.log (coverNum K r) * ((bidx r : ℝ) * Real.log 3)
      ≤ (((bidx r : ℝ) + 1) * Real.log 2) * ((bidx r : ℝ) * Real.log 3) :=
        mul_le_mul_of_nonneg_right h1 hden.le
    _ ≤ (((bidx r : ℝ) + 1) * Real.log 2) * Real.log (1/r) :=
        mul_le_mul_of_nonneg_left h2 hB

lemma loSeq_le_boxQuot (hr : 0 < r) (hr3 : r ≤ 1/3) (hk : 3 ≤ bidx r) :
    loSeq (bidx r) ≤ Real.log (coverNum K r) / Real.log (1/r) := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hkR : (3:ℝ) ≤ (bidx r : ℝ) := by exact_mod_cast hk
  have hden : 0 < (bidx r : ℝ) * Real.log 3 := by nlinarith
  have hd : 0 < Real.log (1/r) := lt_of_lt_of_le hden (log_inv_lower hr hr3)
  have hden' : 0 < ((bidx r : ℝ) + 1) * Real.log 3 := by nlinarith
  rw [loSeq, div_le_div_iff₀ hden' hd]
  have h1 := le_log_coverNum hr hr3
  have h2 := log_inv_upper hr hr3
  have hA : 0 ≤ ((bidx r : ℝ) - 2) * Real.log 2 := by nlinarith
  calc ((bidx r : ℝ) - 2) * Real.log 2 * Real.log (1/r)
      ≤ ((bidx r : ℝ) - 2) * Real.log 2 * (((bidx r : ℝ) + 1) * Real.log 3) :=
        mul_le_mul_of_nonneg_left h2 hA
    _ ≤ Real.log (coverNum K r) * (((bidx r : ℝ) + 1) * Real.log 3) :=
        mul_le_mul_of_nonneg_right h1 hden'.le

end Bracket

/-- The squeeze from the triadic scales to all scales. -/
theorem tendsto_boxQuot :
    Tendsto (fun r : ℝ => Real.log (coverNum K r) / Real.log (1/r)) (𝓝[>] (0:ℝ))
      (𝓝 dexp) := by
  have hev : ∀ᶠ r in 𝓝[>] (0:ℝ), 0 < r ∧ r ≤ 1/3 ∧ 3 ≤ bidx r := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0:ℝ) < 1/3 by norm_num)),
      tendsto_bidx.eventually_ge_atTop 3] with r hr hr3 hk
    exact ⟨hr, le_of_lt hr3, hk⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun r : ℝ => loSeq (bidx r)) (h := fun r : ℝ => hiSeq (bidx r))
    (tendsto_loSeq.comp tendsto_bidx) (tendsto_hiSeq.comp tendsto_bidx) ?_ ?_
  · filter_upwards [hev] with r ⟨hr, hr3, hk⟩
    exact loSeq_le_boxQuot hr hr3 hk
  · filter_upwards [hev] with r ⟨hr, hr3, hk⟩
    exact boxQuot_le_hiSeq hr hr3 hk

theorem upperBoxDim_K : upperBoxDim K = dexp := tendsto_boxQuot.limsup_eq

theorem lowerBoxDim_K : lowerBoxDim K = dexp := tendsto_boxQuot.liminf_eq

/-- **T36.**  Upper and lower box dimension of the kind set at `λ = 3/2` agree
and equal `log 2 / log 3`. -/
theorem boxDim_K : upperBoxDim K = Real.log 2 / Real.log 3 ∧
    lowerBoxDim K = Real.log 2 / Real.log 3 :=
  ⟨upperBoxDim_K, lowerBoxDim_K⟩

end KindBox
end KnotGame
