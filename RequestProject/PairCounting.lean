import RequestProject.Transversality

/-!
# Pair counting on the transversality window (round 3, Target T10)

This file formalises the pair-counting proposition of the transversality note
on the window certified by Target T9.

For a branch word `ε ∈ {0,1}^m` the endpoint of the corresponding knot orbit is

  `Φ_ε(λ) = λ^m (1/2 − (λ−1) ∑_{j=1}^m ε_j λ^{-j})`,

written here as `Phi m e l` with the negative powers cleared.  The note's
Lemma (embedding) says that for two branch words whose first disagreement is at
index `k`,

  `|Φ_ε(λ) − Φ_ε'(λ)| = (λ−1) λ^{m−k} |g(1/λ)|`

for an explicit `g ∈ 𝓑₀₁` (`Phi_sub_abs`), and the proposition converts
δ-transversality of `𝓑₀₁` into a Lebesgue-measure bound for the set of
parameters at which two endpoints are `ρ`-close (`volume_close_le`).

The window is `I = [1000/667, 2]`, the image of the T9 window
`[1/2, 667/1000]` under `x ↦ 1/x`, and `δ = 1/1000` is the constant certified
by T9.

The route to the measure bound is a *diameter* bound, which is why no
change-of-variables theorem appears: transversality forces the set
`{x : |g(x)| ≤ ρ'}` to have diameter at most `2ρ'/δ` (`sub_le_of_transversal`),
the map `λ ↦ 1/λ` is 4-Lipschitz backwards on `I`, and a set of diameter `L` has
outer measure at most `L`.
-/

namespace KnotGame
namespace Transversality

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-! ### Local consequences of a negative derivative -/

/-- If `f` has a negative derivative at `p`, then `f` takes a value smaller than
`f p` somewhere immediately to the right of `p`. -/
lemma exists_lt_of_hasDerivAt_neg {f : ℝ → ℝ} {p d u : ℝ}
    (h : HasDerivAt f d p) (hd : d < 0) (hu : p < u) : ∃ t ∈ Set.Ioo p u, f t < f p := by
  rw [hasDerivAt_iff_tendsto_slope] at h
  have hmono : 𝓝[>] p ≤ 𝓝[≠] p := nhdsWithin_mono _ (fun x hx => ne_of_gt hx)
  have h1 : ∀ᶠ t in 𝓝[>] p, slope f p t < 0 :=
    Filter.Eventually.filter_mono hmono (h.eventually_lt_const hd)
  have h2 : ∀ᶠ t in 𝓝[>] p, t ∈ Set.Ioo p u := Ioo_mem_nhdsGT hu
  obtain ⟨t, ht1, ht2⟩ := ((h1.and h2).and self_mem_nhdsWithin).exists
  refine ⟨t, ht1.2, ?_⟩
  have hslope : slope f p t < 0 := ht1.1
  rw [slope_def_field] at hslope
  have hpt : 0 < t - p := sub_pos.mpr ht2
  have h4 := (div_lt_iff₀ hpt).mp hslope
  linarith

/-- If `f` has a negative derivative at `p`, then `f` takes a value larger than
`f p` somewhere immediately to the left of `p`. -/
lemma exists_gt_of_hasDerivAt_neg {f : ℝ → ℝ} {p d l : ℝ}
    (h : HasDerivAt f d p) (hd : d < 0) (hl : l < p) : ∃ t ∈ Set.Ioo l p, f p < f t := by
  rw [hasDerivAt_iff_tendsto_slope] at h
  have hmono : 𝓝[<] p ≤ 𝓝[≠] p := nhdsWithin_mono _ (fun x hx => ne_of_lt hx)
  have h1 : ∀ᶠ t in 𝓝[<] p, slope f p t < 0 :=
    Filter.Eventually.filter_mono hmono (h.eventually_lt_const hd)
  have h2 : ∀ᶠ t in 𝓝[<] p, t ∈ Set.Ioo l p := Ioo_mem_nhdsLT hl
  obtain ⟨t, ht1, ht2⟩ := ((h1.and h2).and self_mem_nhdsWithin).exists
  refine ⟨t, ht1.2, ?_⟩
  have hslope : slope f p t < 0 := ht1.1
  rw [slope_def_field] at hslope
  have hpt : t - p < 0 := sub_neg.mpr ht2
  have h4 := (div_lt_iff_of_neg hpt).mp hslope
  linarith

/-! ### The abstract transversality width bound -/

/-- **No escape from the band.**  If `f' < −δ` wherever `|f| ≤ δ`, then `f`
cannot leave the band `[−δ, δ]` between a point where `f ≤ δ` and a later point
where `f ≥ −δ`. -/
lemma abs_le_of_transversal {f f' : ℝ → ℝ} {a b δ : ℝ} (hδ : 0 < δ)
    (hderiv : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (htrans : ∀ t ∈ Icc a b, |f t| ≤ δ → f' t < -δ)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b)
    (hfx : f x ≤ δ) (hfy : -δ ≤ f y) : ∀ t ∈ Icc x y, |f t| ≤ δ := by
  have hsub : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hy.2
  have hcont : ContinuousOn f (Icc a b) :=
    fun t ht => ((hderiv t ht).continuousAt).continuousWithinAt
  intro t0 ht0
  by_contra hcon
  rw [not_le] at hcon
  have ht0ab : t0 ∈ Icc a b := hsub ht0
  rcases lt_abs.mp hcon with hup | hdn
  · -- `f t0 > δ`: look at the last time before `t0` at which `f ≤ δ`
    set S : Set ℝ := Icc x t0 ∩ f ⁻¹' Iic δ with hS
    have hIsub : Icc x t0 ⊆ Icc a b := Icc_subset_Icc hx.1 ht0ab.2
    have hxS : x ∈ S := ⟨⟨le_refl x, ht0.1⟩, hfx⟩
    have hScl : IsClosed S :=
      (hcont.mono hIsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have hScomp : IsCompact S := isCompact_Icc.of_isClosed_subset hScl inter_subset_left
    have hpS : sSup S ∈ S := hScomp.sSup_mem ⟨x, hxS⟩
    set p := sSup S with hp
    have hpmem : p ∈ Icc x t0 := hpS.1
    have hfp : f p ≤ δ := hpS.2
    have hplt : p < t0 := lt_of_le_of_ne hpmem.2 (by intro h; rw [h] at hfp; linarith)
    have hbdd : BddAbove S := hScomp.bddAbove
    have hupper : ∀ t, p < t → t ≤ t0 → δ < f t := by
      intro t h1 h2
      by_contra hle
      exact absurd (le_csSup hbdd ⟨⟨le_trans hpmem.1 h1.le, h2⟩, not_lt.mp hle⟩) (not_le.mpr h1)
    have hpge : -δ ≤ f p := by
      by_contra hlt
      push_neg at hlt
      obtain ⟨s, hs, hfs⟩ := intermediate_value_Ioo hplt.le
        (hcont.mono ((Icc_subset_Icc hpmem.1 le_rfl).trans hIsub)) ⟨by linarith, hup⟩
      linarith [hupper s hs.1 hs.2.le]
    have hpab : p ∈ Icc a b := hIsub hpmem
    have hd : f' p < -δ := htrans p hpab (abs_le.mpr ⟨hpge, hfp⟩)
    obtain ⟨t, ht, hft⟩ := exists_lt_of_hasDerivAt_neg (hderiv p hpab) (by linarith) hplt
    linarith [hupper t ht.1 ht.2.le]
  · -- `f t0 < −δ`: look at the first time after `t0` at which `f ≥ −δ`
    have hft0 : f t0 < -δ := by linarith
    set S : Set ℝ := Icc t0 y ∩ f ⁻¹' Ici (-δ) with hS
    have hIsub : Icc t0 y ⊆ Icc a b := Icc_subset_Icc ht0ab.1 hy.2
    have hyS : y ∈ S := ⟨⟨ht0.2, le_refl y⟩, hfy⟩
    have hScl : IsClosed S :=
      (hcont.mono hIsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hScomp : IsCompact S := isCompact_Icc.of_isClosed_subset hScl inter_subset_left
    have hqS : sInf S ∈ S := hScomp.sInf_mem ⟨y, hyS⟩
    set q := sInf S with hq
    have hqmem : q ∈ Icc t0 y := hqS.1
    have hfq : -δ ≤ f q := hqS.2
    have hqgt : t0 < q := lt_of_le_of_ne hqmem.1 (by intro h; rw [← h] at hfq; linarith)
    have hbdd : BddBelow S := hScomp.bddBelow
    have hlower : ∀ t, t0 ≤ t → t < q → f t < -δ := by
      intro t h1 h2
      by_contra hle
      exact absurd (csInf_le hbdd ⟨⟨h1, le_trans h2.le hqmem.2⟩, not_lt.mp hle⟩) (not_le.mpr h2)
    have hqle : f q ≤ δ := by
      by_contra hlt
      push_neg at hlt
      obtain ⟨s, hs, hfs⟩ := intermediate_value_Ioo hqgt.le
        (hcont.mono ((Icc_subset_Icc le_rfl hqmem.2).trans hIsub)) ⟨hft0, by linarith⟩
      linarith [hlower s hs.1.le hs.2]
    have hqab : q ∈ Icc a b := hIsub hqmem
    have hd : f' q < -δ := htrans q hqab (abs_le.mpr ⟨hfq, hqle⟩)
    obtain ⟨t, ht, hft⟩ := exists_gt_of_hasDerivAt_neg (hderiv q hqab) (by linarith) hqgt
    linarith [hlower t ht.1.le ht.2]

/-- **The width bound, ordered form.**  Under δ-transversality on `[a,b]`, two
points at which `|f| ≤ ρ ≤ δ` are at distance at most `2ρ/δ`. -/
lemma sub_le_of_transversal {f f' : ℝ → ℝ} {a b δ ρ : ℝ} (hδ : 0 < δ) (hρδ : ρ ≤ δ)
    (hderiv : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (htrans : ∀ t ∈ Icc a b, |f t| ≤ δ → f' t < -δ)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≤ y)
    (hfx : |f x| ≤ ρ) (hfy : |f y| ≤ ρ) : y - x ≤ 2 * ρ / δ := by
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · have : 0 ≤ ρ := le_trans (abs_nonneg _) hfx
    simp only [sub_self]
    positivity
  · have hb := abs_le_of_transversal hδ hderiv htrans hx hy (le_trans (abs_le.mp hfx).2 hρδ)
      (le_trans (neg_le_neg hρδ) (abs_le.mp hfy).1)
    have hsub : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hy.2
    have hcont : ContinuousOn f (Icc x y) :=
      fun t ht => ((hderiv t (hsub ht)).continuousAt).continuousWithinAt
    obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope f f' hlt hcont
      (fun t ht => hderiv t (hsub (Ioo_subset_Icc_self ht)))
    have hξd : f' ξ < -δ := htrans ξ (hsub (Ioo_subset_Icc_self hξ)) (hb ξ (Ioo_subset_Icc_self hξ))
    have hyx : 0 < y - x := sub_pos.mpr hlt
    rw [hslope] at hξd
    have h0 := (div_lt_iff₀ hyx).mp hξd
    have h1 : f x ≤ ρ := (abs_le.mp hfx).2
    have h2 : -ρ ≤ f y := (abs_le.mp hfy).1
    rw [le_div_iff₀ hδ]
    nlinarith

/-- **The width bound.** -/
lemma abs_sub_le_of_transversal {f f' : ℝ → ℝ} {a b δ ρ : ℝ} (hδ : 0 < δ) (hρδ : ρ ≤ δ)
    (hderiv : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (htrans : ∀ t ∈ Icc a b, |f t| ≤ δ → f' t < -δ)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b)
    (hfx : |f x| ≤ ρ) (hfy : |f y| ≤ ρ) : |x - y| ≤ 2 * ρ / δ := by
  rcases le_total x y with h | h
  · rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    exact sub_le_of_transversal hδ hρδ hderiv htrans hx hy h hfx hfy
  · rw [abs_of_nonneg (by linarith)]
    exact sub_le_of_transversal hδ hρδ hderiv htrans hy hx h hfy hfx

/-! ### The width bound on the certified window -/

/-- Two points of `[1/2, 667/1000]` at which a member of `𝓑₀₁` is at most `ρ`
in modulus, `ρ ≤ 1/1000`, are at distance at most `2000 ρ`. -/
lemma abs_sub_le_of_gval_le (c : ℕ → ℤ) (hc0 : c 0 = 1)
    (hc : ∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) {x y ρ : ℝ} (hρδ : ρ ≤ 1 / 1000)
    (hx : x ∈ Icc (1/2 : ℝ) (667/1000)) (hy : y ∈ Icc (1/2 : ℝ) (667/1000))
    (hgx : |gval c x| ≤ ρ) (hgy : |gval c y| ≤ ρ) : |x - y| ≤ 2000 * ρ := by
  have hcabs : ∀ i, |(c i : ℝ)| ≤ 1 := by
    intro i
    rcases hc i with h | h | h <;> rw [h] <;> norm_num
  have hderiv : ∀ t ∈ Icc (1/2 : ℝ) (667/1000), HasDerivAt (gval c) (gder c t) t := by
    intro t ht
    refine hasDerivAt_gval c hcabs ?_
    rw [abs_lt]
    constructor <;> [linarith [ht.1]; linarith [ht.2]]
  have htrans : ∀ t ∈ Icc (1/2 : ℝ) (667/1000), |gval c t| ≤ 1/1000 → gder c t < -(1/1000) :=
    fun t ht hg => transversality c hc0 hc ht.1 ht.2 hg
  have := abs_sub_le_of_transversal (δ := 1/1000) (by norm_num) hρδ hderiv htrans hx hy hgx hgy
  calc |x - y| ≤ 2 * ρ / (1/1000) := this
    _ = 2000 * ρ := by ring

/-! ### The endpoint family and its difference class -/

/-- The bit `ε_j ∈ {0,1}` of a branch word. -/
def bit (e : ℕ → Bool) (j : ℕ) : ℤ := if e j then 1 else 0

/-- The coefficient `ε_j − ε'_j ∈ {−1,0,1}` of a difference of branch words. -/
def dif (e e' : ℕ → Bool) (j : ℕ) : ℤ := bit e j - bit e' j

/-- The endpoint of the orbit of `1/2` along the branch word `e` of length `m`:
`Φ_ε(λ) = λ^m (1/2 − (λ−1) ∑_{j=1}^m ε_j λ^{-j})`, with the negative powers
cleared. -/
noncomputable def Phi (m : ℕ) (e : ℕ → Bool) (l : ℝ) : ℝ :=
  l ^ m / 2 - (l - 1) * ∑ j ∈ Finset.Icc 1 m, (bit e j : ℝ) * l ^ (m - j)

/-- The member of `𝓑₀₁` attached to a pair of branch words of length `m` whose
first disagreement is at index `k`: normalised so that its constant term is `1`
and it has degree at most `m − k`. -/
def pcoef (e e' : ℕ → Bool) (k m : ℕ) : ℕ → ℤ :=
  fun i => if k + i ≤ m then dif e e' k * dif e e' (k + i) else 0

lemma dif_mul_self (e e' : ℕ → Bool) {k : ℕ} (hdiff : e k ≠ e' k) :
    dif e e' k * dif e e' k = 1 := by
  simp only [dif, bit]
  cases he : e k <;> cases he' : e' k <;> simp_all

lemma pcoef_zero (e e' : ℕ → Bool) {k m : ℕ} (hkm : k ≤ m) (hdiff : e k ≠ e' k) :
    pcoef e e' k m 0 = 1 := by
  simp [pcoef, hkm, dif_mul_self e e' hdiff]

lemma pcoef_mem (e e' : ℕ → Bool) (k m : ℕ) (i : ℕ) :
    pcoef e e' k m i = -1 ∨ pcoef e e' k m i = 0 ∨ pcoef e e' k m i = 1 := by
  simp only [pcoef, dif, bit]
  split
  · cases e k <;> cases e' k <;> cases e (k+i) <;> cases e' (k+i) <;> simp
  · exact Or.inr (Or.inl rfl)

lemma pcoef_eq_zero_of_lt (e e' : ℕ → Bool) {k m i : ℕ} (hi : m - k < i) (hkm : k ≤ m) :
    pcoef e e' k m i = 0 := by
  have : ¬ (k + i ≤ m) := by omega
  simp [pcoef, this]

/-- `gval` of the attached member of `𝓑₀₁` is a finite sum. -/
lemma gval_pcoef (e e' : ℕ → Bool) {k m : ℕ} (hkm : k ≤ m) (x : ℝ) :
    gval (pcoef e e' k m) x
      = ∑ i ∈ Finset.range (m - k + 1), (pcoef e e' k m i : ℝ) * x ^ i := by
  rw [gval, tsum_eq_sum (s := Finset.range (m - k + 1))]
  intro i hi
  rw [pcoef_eq_zero_of_lt e e' (by simpa [Nat.lt_succ_iff] using (Finset.mem_range.not.mp hi)) hkm]
  simp

/-- **The embedding lemma.**  The difference of two endpoints is `(λ−1)λ^{m−k}`
times the value at `1/λ` of an explicit member of `𝓑₀₁`. -/
lemma Phi_sub_eq (m k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m) (e e' : ℕ → Bool)
    (hagree : ∀ j, j < k → e j = e' j) (hdiff : e k ≠ e' k) (l : ℝ) (hl : 0 < l) :
    Phi m e l - Phi m e' l
      = -((l - 1) * l ^ (m - k) * (dif e e' k : ℝ)) * gval (pcoef e e' k m) (1 / l) := by
  have hsqR : ((dif e e' k : ℝ)) * ((dif e e' k : ℝ)) = 1 := by
    exact_mod_cast congrArg (Int.cast (R := ℝ)) (dif_mul_self e e' hdiff)
  have hstep1 : Phi m e l - Phi m e' l
      = -(l - 1) * ∑ j ∈ Finset.Icc 1 m, (dif e e' j : ℝ) * l ^ (m - j) := by
    simp only [Phi, dif, Int.cast_sub, sub_mul, Finset.sum_sub_distrib]
    ring
  have hstep2 : ∑ j ∈ Finset.Icc 1 m, (dif e e' j : ℝ) * l ^ (m - j)
      = ∑ j ∈ Finset.Icc k m, (dif e e' j : ℝ) * l ^ (m - j) := by
    rw [← Finset.sum_subset (Finset.Icc_subset_Icc_left hk)]
    intro j hj hj'
    have hjk : j < k := by
      simp only [Finset.mem_Icc] at hj hj'
      omega
    simp [dif, bit, hagree j hjk]
  have hstep3 : ∑ j ∈ Finset.Icc k m, (dif e e' j : ℝ) * l ^ (m - j)
      = l ^ (m - k) * (dif e e' k : ℝ) *
          ∑ i ∈ Finset.range (m - k + 1), (pcoef e e' k m i : ℝ) * (1 / l) ^ i := by
    have hIcc : Finset.Icc k m = Finset.Ico k (m+1) := by
      rw [← Finset.Ico_succ_right_eq_Icc]; rfl
    rw [hIcc, Finset.sum_Ico_eq_sum_range]
    have hlen : m + 1 - k = m - k + 1 := by omega
    rw [hlen, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hik : i ≤ m - k := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hi
    have hkim : k + i ≤ m := by omega
    have hpow : l ^ (m - k) * (1 / l) ^ i = l ^ (m - (k + i)) := by
      have h1 : m - k = (m - (k + i)) + i := by omega
      rw [h1, pow_add, one_div, inv_pow]
      field_simp
    have hc : (pcoef e e' k m i : ℤ) = dif e e' k * dif e e' (k + i) := by
      simp [pcoef, hkim]
    rw [hc]
    push_cast
    calc (dif e e' (k+i) : ℝ) * l ^ (m - (k+i))
        = (dif e e' k : ℝ) * ((dif e e' k : ℝ) * (dif e e' (k+i) : ℝ)) * (l ^ (m-k) * (1/l)^i) := by
          rw [hpow, ← mul_assoc, hsqR, one_mul]
      _ = l ^ (m - k) * (dif e e' k : ℝ) *
            ((dif e e' k : ℝ) * (dif e e' (k+i) : ℝ) * (1/l)^i) := by ring
  rw [hstep1, hstep2, hstep3, gval_pcoef e e' hkm]
  ring

/-- **The embedding lemma, in modulus.** -/
lemma Phi_sub_abs (m k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m) (e e' : ℕ → Bool)
    (hagree : ∀ j, j < k → e j = e' j) (hdiff : e k ≠ e' k) (l : ℝ) (hl : 1 < l) :
    |Phi m e l - Phi m e' l| = (l - 1) * l ^ (m - k) * |gval (pcoef e e' k m) (1 / l)| := by
  rw [Phi_sub_eq m k hk hkm e e' hagree hdiff l (by linarith)]
  rw [abs_mul, abs_neg, abs_mul, abs_mul]
  have h1 : |l - 1| = l - 1 := abs_of_pos (by linarith)
  have h2 : |l ^ (m - k)| = l ^ (m - k) := abs_of_pos (by positivity)
  have h3 : |(dif e e' k : ℝ)| = 1 := by
    have := dif_mul_self e e' hdiff
    have : ((dif e e' k : ℝ)) * ((dif e e' k : ℝ)) = 1 := by
      exact_mod_cast congrArg (Int.cast (R := ℝ)) this
    nlinarith [abs_nonneg ((dif e e' k : ℝ)), sq_abs ((dif e e' k : ℝ))]
  rw [h1, h2, h3, mul_one]

/-! ### From a diameter bound to a measure bound -/

/-- A set of diameter at most `L` has Lebesgue measure at most `L`. -/
lemma volume_le_of_width {A : Set ℝ} {L : ℝ} (hbdd : BddBelow A)
    (h : ∀ x ∈ A, ∀ y ∈ A, |x - y| ≤ L) : volume A ≤ ENNReal.ofReal L := by
  rcases A.eq_empty_or_nonempty with rfl | hne
  · simp
  · have hsub : A ⊆ Icc (sInf A) (sInf A + L) := by
      intro x hx
      refine ⟨csInf_le hbdd hx, ?_⟩
      have : x - L ≤ sInf A := le_csInf hne (fun y hy => by
        have := h x hx y hy
        cases abs_le.mp this with
        | intro h1 h2 => linarith)
      linarith
    calc volume A ≤ volume (Icc (sInf A) (sInf A + L)) := measure_mono hsub
      _ = ENNReal.ofReal L := by rw [Real.volume_Icc]; ring_nf

/-! ### The parameter window -/

/-- The parameter window `I = [1000/667, 2]`, the image of the window
`[1/2, 667/1000]` certified by T9 under `x ↦ 1/x`. -/
def Iwin : Set ℝ := Icc (1000/667 : ℝ) 2

lemma inv_mem_window {l : ℝ} (hl : l ∈ Iwin) : 1 / l ∈ Icc (1/2 : ℝ) (667/1000) := by
  obtain ⟨h1, h2⟩ := hl
  have hl0 : (0:ℝ) < l := by linarith
  constructor
  · rw [le_div_iff₀ hl0]; linarith
  · rw [div_le_iff₀ hl0]; nlinarith

/-! ### The pair-counting bound for one pair -/

/-- **T10, one pair.**  For two branch words of length `m` whose first
disagreement is at index `k`, the set of parameters in `I = [1000/667, 2]` at
which the two orbit endpoints are `ρ`-close has Lebesgue measure at most
`8ρ λ₀^{k−m} / (δ(λ₀−1))` with `λ₀ = 1000/667` and `δ = 1/1000`. -/
theorem volume_close_le (m k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m) (e e' : ℕ → Bool)
    (hagree : ∀ j, j < k → e j = e' j) (hdiff : e k ≠ e' k) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    volume {l ∈ Iwin | |Phi m e l - Phi m e' l| ≤ ρ}
      ≤ ENNReal.ofReal (8000 * ρ / ((1000/667 - 1) * (1000/667 : ℝ) ^ (m - k))) := by
  set c := pcoef e e' k m with hc
  set D : ℝ := (1000/667 - 1) * (1000/667 : ℝ) ^ (m - k) with hD
  have hDpos : 0 < D := by rw [hD]; positivity
  set r : ℝ := ρ / D with hr
  have hrnn : 0 ≤ r := div_nonneg hρ hDpos.le
  have hAsub : {l ∈ Iwin | |Phi m e l - Phi m e' l| ≤ ρ} ⊆ Iwin := fun l hl => hl.1
  have hbdd : BddBelow {l ∈ Iwin | |Phi m e l - Phi m e' l| ≤ ρ} :=
    ⟨1000/667, fun l hl => hl.1.1⟩
  have hEq : 8000 * ρ / D = 8000 * r := by rw [hr]; ring
  rcases le_or_gt r (1/1000) with hsmall | hbig
  · -- the transversality regime
    have hgsmall : ∀ l ∈ {l ∈ Iwin | |Phi m e l - Phi m e' l| ≤ ρ}, |gval c (1 / l)| ≤ r := by
      rintro l ⟨hlI, hlρ⟩
      obtain ⟨h1, h2⟩ := hlI
      have hl1 : (1:ℝ) < l := by linarith
      have habs := Phi_sub_abs m k hk hkm e e' hagree hdiff l hl1
      rw [habs] at hlρ
      have hpow : D ≤ (l - 1) * l ^ (m - k) := by
        rw [hD]
        have : (1000/667 : ℝ) ^ (m - k) ≤ l ^ (m - k) :=
          pow_le_pow_left₀ (by norm_num) h1 _
        have hp0 : (0:ℝ) < (1000/667 : ℝ) ^ (m - k) := by positivity
        nlinarith
      have hfac : 0 < (l - 1) * l ^ (m - k) := lt_of_lt_of_le hDpos hpow
      have := (le_div_iff₀ hfac).mpr (by linarith [hlρ] : |gval c (1/l)| * ((l-1) * l ^ (m-k)) ≤ ρ)
      calc |gval c (1/l)| ≤ ρ / ((l - 1) * l ^ (m - k)) := this
        _ ≤ ρ / D := by
            apply div_le_div_of_nonneg_left hρ hDpos hpow
        _ = r := rfl
    have hwidth : ∀ x ∈ {l ∈ Iwin | |Phi m e l - Phi m e' l| ≤ ρ},
        ∀ y ∈ {l ∈ Iwin | |Phi m e l - Phi m e' l| ≤ ρ}, |x - y| ≤ 8000 * r := by
      intro x hx y hy
      have hxw := inv_mem_window hx.1
      have hyw := inv_mem_window hy.1
      have hxy : |1/x - 1/y| ≤ 2000 * r :=
        abs_sub_le_of_gval_le c (pcoef_zero e e' hkm hdiff) (pcoef_mem e e' k m) hsmall
          hxw hyw (hgsmall x hx) (hgsmall y hy)
      have hx0 : (0:ℝ) < x := by have := hx.1.1; linarith
      have hy0 : (0:ℝ) < y := by have := hy.1.1; linarith
      have hx2 : x ≤ 2 := hx.1.2
      have hy2 : y ≤ 2 := hy.1.2
      have habsxy : |x - y| = |1/x - 1/y| * (x * y) := by
        have hkey : x - y = (1/x - 1/y) * (-(x * y)) := by field_simp; ring
        rw [hkey, abs_mul, abs_neg, abs_of_pos (show (0:ℝ) < x * y by positivity)]
      rw [habsxy]
      have h4 : x * y ≤ 4 := by nlinarith
      calc |1/x - 1/y| * (x * y) ≤ (2000 * r) * 4 :=
            mul_le_mul hxy h4 (by positivity) (by linarith)
        _ = 8000 * r := by ring
    calc volume {l ∈ Iwin | |Phi m e l - Phi m e' l| ≤ ρ}
        ≤ ENNReal.ofReal (8000 * r) := volume_le_of_width hbdd hwidth
      _ = ENNReal.ofReal (8000 * ρ / D) := by rw [hEq]
  · -- the trivial regime: the bound already exceeds the length of the window
    have h1 : volume {l ∈ Iwin | |Phi m e l - Phi m e' l| ≤ ρ} ≤ volume Iwin :=
      measure_mono hAsub
    have h2 : volume Iwin = ENNReal.ofReal (2 - 1000/667) := by
      rw [Iwin, Real.volume_Icc]
    refine le_trans h1 (le_trans (le_of_eq h2) (ENNReal.ofReal_le_ofReal ?_))
    rw [hEq]
    nlinarith

/-! ### Branch words of a fixed length -/

/-- A branch word of length `m`, as a total function on `ℕ` (`false` outside
range). -/
def wfun (m : ℕ) (w : Fin m → Bool) (i : ℕ) : Bool := if h : i < m then w ⟨i, h⟩ else false

/-- A branch word of length `m`, as a function on `Fin m`, read as a function on
the indices `1, …, m`. -/
def wext (m : ℕ) (w : Fin m → Bool) : ℕ → Bool :=
  fun j => if j = 0 then false else wfun m w (j - 1)

lemma wext_pos {m j : ℕ} (w : Fin m → Bool) (h1 : 1 ≤ j) (h : j - 1 < m) :
    wext m w j = w ⟨j - 1, h⟩ := by
  unfold wext wfun
  rw [if_neg (by omega), dif_pos h]

open scoped Classical in
/-- The index (`0`-based) of the first disagreement of two branch words. -/
noncomputable def dIdx (m : ℕ) (a b : Fin m → Bool) : ℕ :=
  sInf {j | ∃ h : j < m, a ⟨j, h⟩ ≠ b ⟨j, h⟩}

lemma dIdx_mem {m : ℕ} {a b : Fin m → Bool} (hab : a ≠ b) :
    ∃ h : dIdx m a b < m, a ⟨dIdx m a b, h⟩ ≠ b ⟨dIdx m a b, h⟩ := by
  have hne : {j | ∃ h : j < m, a ⟨j, h⟩ ≠ b ⟨j, h⟩}.Nonempty := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hab
    exact ⟨i.val, i.isLt, by simpa using hi⟩
  exact Nat.sInf_mem hne

lemma dIdx_lt {m : ℕ} {a b : Fin m → Bool} (hab : a ≠ b) : dIdx m a b < m := (dIdx_mem hab).1

lemma dIdx_min {m : ℕ} {a b : Fin m → Bool} {j : ℕ} (hj : j < dIdx m a b) (h : j < m) :
    a ⟨j, h⟩ = b ⟨j, h⟩ := by
  have hnm := Nat.notMem_of_lt_sInf hj
  simp only [Set.mem_setOf_eq, not_exists] at hnm
  by_contra hc
  exact hnm h hc

/-- Two distinct branch words, extended to `ℕ`, agree below their first
disagreement. -/
lemma wext_agree {m : ℕ} {a b : Fin m → Bool} (hab : a ≠ b) :
    ∀ j, j < dIdx m a b + 1 → wext m a j = wext m b j := by
  intro j hj
  rcases Nat.eq_zero_or_pos j with rfl | hj1
  · simp [wext]
  · have hlt := dIdx_lt hab
    have hij : j - 1 < dIdx m a b := by omega
    have hjm : j - 1 < m := by omega
    rw [wext_pos a hj1 hjm, wext_pos b hj1 hjm]
    exact dIdx_min hij hjm

/-- Two distinct branch words, extended to `ℕ`, disagree at their first
disagreement. -/
lemma wext_diff {m : ℕ} {a b : Fin m → Bool} (hab : a ≠ b) :
    wext m a (dIdx m a b + 1) ≠ wext m b (dIdx m a b + 1) := by
  obtain ⟨hlt, hne⟩ := dIdx_mem hab
  have h1 : 1 ≤ dIdx m a b + 1 := by omega
  have h2 : dIdx m a b + 1 - 1 < m := by omega
  rw [wext_pos a h1 h2, wext_pos b h1 h2]
  simpa using hne

open scoped Classical in
/-- The number of pairs of distinct branch words whose first disagreement is at a
given index is at most `2^m · 2^{m-k}`. -/
lemma fiber_card_le (m i : ℕ) (hi : i < m) :
    ((Finset.univ : Finset ((Fin m → Bool) × (Fin m → Bool))).filter
      (fun p => p.1 ≠ p.2 ∧ dIdx m p.1 p.2 = i)).card ≤ 2 ^ m * 2 ^ (m - (i+1)) := by
  have hcard : Fintype.card ((Fin m → Bool) × (Fin (m - (i+1)) → Bool))
      = 2 ^ m * 2 ^ (m - (i+1)) := by simp
  rw [← hcard, ← Finset.card_univ]
  refine Finset.card_le_card_of_injOn
    (fun p => (p.1, fun j : Fin (m - (i+1)) => p.2 ⟨i + 1 + j.val, by omega⟩))
    (fun p _ => Finset.mem_univ _) ?_
  intro p hp q hq heq
  obtain ⟨-, hp1, hp2⟩ := Finset.mem_filter.mp hp
  obtain ⟨-, hq1, hq2⟩ := Finset.mem_filter.mp hq
  have heq2 : (p.1, fun j : Fin (m - (i+1)) => p.2 ⟨i + 1 + j.val, by omega⟩)
      = (q.1, fun j : Fin (m - (i+1)) => q.2 ⟨i + 1 + j.val, by omega⟩) := heq
  rw [Prod.mk.injEq] at heq2
  obtain ⟨h1, htail⟩ := heq2
  have h2 : p.2 = q.2 := by
    funext j
    rcases lt_trichotomy j.val i with hlt | heqi | hgt
    · have hpj := dIdx_min (a := p.1) (b := p.2) (by rw [hp2]; exact hlt) j.isLt
      have hqj := dIdx_min (a := q.1) (b := q.2) (by rw [hq2]; exact hlt) j.isLt
      have hh : p.1 j = q.1 j := by rw [h1]
      have e1 : (⟨j.val, j.isLt⟩ : Fin m) = j := rfl
      rw [e1] at hpj hqj
      rw [← hpj, ← hqj, hh]
    · obtain ⟨hlt1, hne1⟩ := dIdx_mem hp1
      obtain ⟨hlt2, hne2⟩ := dIdx_mem hq1
      have ej : (⟨dIdx m p.1 p.2, hlt1⟩ : Fin m) = j := by apply Fin.ext; simp only []; omega
      have ej' : (⟨dIdx m q.1 q.2, hlt2⟩ : Fin m) = j := by apply Fin.ext; simp only []; omega
      rw [ej] at hne1
      rw [ej'] at hne2
      have hh : p.1 j = q.1 j := by rw [h1]
      revert hne1 hne2
      rw [hh]
      cases q.1 j <;> cases p.2 j <;> cases q.2 j <;> simp
    · set t : Fin (m - (i+1)) := ⟨j.val - (i+1), by omega⟩ with ht
      have hidx : (⟨i + 1 + t.val, by omega⟩ : Fin m) = j := by
        apply Fin.ext
        simp only [ht]
        omega
      have hc := congrFun htail t
      rw [hidx] at hc
      exact hc
  exact Prod.ext h1 h2

/-! ### The geometric estimate -/

/-- The left endpoint `λ₀ = 1000/667` of the parameter window. -/
noncomputable def lam0 : ℝ := 1000/667

lemma lam0_lt_two : lam0 < 2 := by rw [lam0]; norm_num

lemma one_lt_lam0 : 1 < lam0 := by rw [lam0]; norm_num

/-- The geometric sum that turns the per-pair bound, summed over the pairs whose
first disagreement is at each index, into the pair-counting constant. -/
lemma geom_bound (m : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∑ i ∈ Finset.range m,
        ((2:ℝ) ^ m * 2 ^ (m - (i+1))) * (8000 * ρ / ((lam0 - 1) * lam0 ^ (m - (i+1))))
      ≤ 8000 * lam0 / ((lam0 - 1) * (2 - lam0)) * ρ * (4 / lam0) ^ m := by
  have hl1 : 1 < lam0 := one_lt_lam0
  have hl2 : lam0 < 2 := lam0_lt_two
  have hl0 : 0 < lam0 := by linarith
  set q : ℝ := 2 / lam0 with hq
  have hq1 : 1 < q := by rw [hq, lt_div_iff₀ hl0]; linarith
  have hterm : ∀ i ∈ Finset.range m,
      ((2:ℝ) ^ m * 2 ^ (m - (i+1))) * (8000 * ρ / ((lam0 - 1) * lam0 ^ (m - (i+1))))
        = (8000 * ρ / (lam0 - 1)) * 2 ^ m * q ^ (m - 1 - i) := by
    intro i hi
    have hmi : m - (i + 1) = m - 1 - i := by omega
    rw [hmi, hq, div_pow]
    have hp : (0:ℝ) < lam0 ^ (m - 1 - i) := by positivity
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hrefl : ∑ i ∈ Finset.range m, q ^ (m - 1 - i) = ∑ i ∈ Finset.range m, q ^ i :=
    Finset.sum_range_reflect (fun i => q ^ i) m
  rw [hrefl, geom_sum_eq (by linarith) m]
  have hA : 0 ≤ (8000 * ρ / (lam0 - 1)) * 2 ^ m := by
    have : 0 < lam0 - 1 := by linarith
    positivity
  have hgeo : (q ^ m - 1) / (q - 1) ≤ q ^ m / (q - 1) := by
    gcongr
    · linarith
    · linarith
  have hqpow : (2:ℝ) ^ m * q ^ m = (4 / lam0) ^ m := by
    rw [← mul_pow, hq]; ring_nf
  calc (8000 * ρ / (lam0 - 1)) * 2 ^ m * ((q ^ m - 1) / (q - 1))
      ≤ (8000 * ρ / (lam0 - 1)) * 2 ^ m * (q ^ m / (q - 1)) :=
        mul_le_mul_of_nonneg_left hgeo hA
    _ = 8000 * lam0 / ((lam0 - 1) * (2 - lam0)) * ρ * (4 / lam0) ^ m := by
        rw [hq, show (2:ℝ)/lam0 - 1 = (2 - lam0)/lam0 by field_simp, ← hqpow, hq]
        field_simp

/-! ### The pair-counting bound, summed over all pairs -/

open scoped Classical in
/-- The per-pair bound, as a function of the first-disagreement index. -/
noncomputable def pairBound (m : ℕ) (ρ : ℝ) (i : ℕ) : ℝ :=
  8000 * ρ / ((lam0 - 1) * lam0 ^ (m - (i+1)))

lemma pairBound_nonneg (m : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) (i : ℕ) : 0 ≤ pairBound m ρ i := by
  have h1 : (0:ℝ) < lam0 - 1 := by have := one_lt_lam0; linarith
  have h2 : (0:ℝ) < lam0 ^ (m - (i+1)) := by
    have := one_lt_lam0; positivity
  rw [pairBound]
  positivity

open scoped Classical in
/-- Summing the per-pair bound over all ordered pairs of distinct branch words of
length `m`. -/
lemma sum_pairBound_le (m : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∑ p ∈ (Finset.univ : Finset ((Fin m → Bool) × (Fin m → Bool))).filter (fun p => p.1 ≠ p.2),
        pairBound m ρ (dIdx m p.1 p.2)
      ≤ 8000 * lam0 / ((lam0 - 1) * (2 - lam0)) * ρ * (4 / lam0) ^ m := by
  set P := (Finset.univ : Finset ((Fin m → Bool) × (Fin m → Bool))).filter (fun p => p.1 ≠ p.2)
    with hP
  have hmaps : ∀ p ∈ P, dIdx m p.1 p.2 ∈ Finset.range m := by
    intro p hp
    have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    exact Finset.mem_range.mpr (dIdx_lt hne)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun p => pairBound m ρ (dIdx m p.1 p.2))]
  refine le_trans (Finset.sum_le_sum ?_) (geom_bound m hρ)
  intro i hi
  have him : i < m := Finset.mem_range.mp hi
  have hfib : P.filter (fun p => dIdx m p.1 p.2 = i)
      = (Finset.univ : Finset ((Fin m → Bool) × (Fin m → Bool))).filter
          (fun p => p.1 ≠ p.2 ∧ dIdx m p.1 p.2 = i) := by
    rw [hP, Finset.filter_filter]
  have hconst : ∑ p ∈ P.filter (fun p => dIdx m p.1 p.2 = i), pairBound m ρ (dIdx m p.1 p.2)
      = (P.filter (fun p => dIdx m p.1 p.2 = i)).card * pairBound m ρ i := by
    rw [Finset.sum_congr rfl (fun p hp => by rw [(Finset.mem_filter.mp hp).2]),
      Finset.sum_const, nsmul_eq_mul]
  rw [hconst]
  have hcard : ((P.filter (fun p => dIdx m p.1 p.2 = i)).card : ℝ) ≤ (2:ℝ) ^ m * 2 ^ (m - (i+1)) := by
    rw [hfib]
    exact_mod_cast Nat.cast_le.mpr (fiber_card_le m i him)
  have := mul_le_mul_of_nonneg_right hcard (pairBound_nonneg m hρ i)
  simpa [pairBound] using this

open scoped Classical in
/-- **T10, summed over pairs.**  On the window `I = [1000/667, 2]`, the total
parameter measure on which some ordered pair of distinct length-`m` branch words
has `ρ`-close endpoints is at most
`8λ₀ ρ (4/λ₀)^m / (δ(λ₀−1)(2−λ₀))` with `λ₀ = 1000/667`, `δ = 1/1000`.
(The note states the bound for unordered pairs; the constant here is twice
that one.) -/
theorem sum_volume_close_le (m : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∑ p ∈ (Finset.univ : Finset ((Fin m → Bool) × (Fin m → Bool))).filter (fun p => p.1 ≠ p.2),
        volume {l ∈ Iwin | |Phi m (wext m p.1) l - Phi m (wext m p.2) l| ≤ ρ}
      ≤ ENNReal.ofReal (8000 * lam0 / ((lam0 - 1) * (2 - lam0)) * ρ * (4 / lam0) ^ m) := by
  set P := (Finset.univ : Finset ((Fin m → Bool) × (Fin m → Bool))).filter (fun p => p.1 ≠ p.2)
    with hP
  have hstep : ∀ p ∈ P, volume {l ∈ Iwin | |Phi m (wext m p.1) l - Phi m (wext m p.2) l| ≤ ρ}
      ≤ ENNReal.ofReal (pairBound m ρ (dIdx m p.1 p.2)) := by
    intro p hp
    have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    have hlt : dIdx m p.1 p.2 < m := dIdx_lt hne
    have := volume_close_le m (dIdx m p.1 p.2 + 1) (by omega) (by omega)
      (wext m p.1) (wext m p.2) (wext_agree hne) (wext_diff hne) hρ
    simpa [pairBound, lam0] using this
  calc ∑ p ∈ P, volume {l ∈ Iwin | |Phi m (wext m p.1) l - Phi m (wext m p.2) l| ≤ ρ}
      ≤ ∑ p ∈ P, ENNReal.ofReal (pairBound m ρ (dIdx m p.1 p.2)) := Finset.sum_le_sum hstep
    _ = ENNReal.ofReal (∑ p ∈ P, pairBound m ρ (dIdx m p.1 p.2)) :=
        (ENNReal.ofReal_sum_of_nonneg (fun p _ => pairBound_nonneg m hρ _)).symm
    _ ≤ ENNReal.ofReal (8000 * lam0 / ((lam0 - 1) * (2 - lam0)) * ρ * (4 / lam0) ^ m) :=
        ENNReal.ofReal_le_ofReal (sum_pairBound_le m hρ)

/-! ### The bound for unordered pairs -/

lemma dIdx_comm (m : ℕ) (a b : Fin m → Bool) : dIdx m a b = dIdx m b a := by
  unfold dIdx
  congr 1
  ext j
  simp only [Set.mem_setOf_eq]
  constructor <;> · rintro ⟨h, hne⟩; exact ⟨h, Ne.symm hne⟩

open scoped Classical in
/-- One representative of each unordered pair of distinct branch words: the
ordered pair whose first word carries `false` at the first disagreement. -/
noncomputable def unordPairs (m : ℕ) : Finset ((Fin m → Bool) × (Fin m → Bool)) :=
  (Finset.univ : Finset ((Fin m → Bool) × (Fin m → Bool))).filter
    (fun p => p.1 ≠ p.2 ∧ wext m p.1 (dIdx m p.1 p.2 + 1) = false)

open scoped Classical in
/-- **T10, summed over unordered pairs.**  This is the note's own constant
`4λ₀/(δ(λ₀−1)(2−λ₀))`. -/
theorem sum_volume_close_le_unord (m : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∑ p ∈ unordPairs m,
        volume {l ∈ Iwin | |Phi m (wext m p.1) l - Phi m (wext m p.2) l| ≤ ρ}
      ≤ ENNReal.ofReal (4000 * lam0 / ((lam0 - 1) * (2 - lam0)) * ρ * (4 / lam0) ^ m) := by
  set P := (Finset.univ : Finset ((Fin m → Bool) × (Fin m → Bool))).filter (fun p => p.1 ≠ p.2)
    with hP
  set f : ((Fin m → Bool) × (Fin m → Bool)) → ℝ≥0∞ :=
    fun p => volume {l ∈ Iwin | |Phi m (wext m p.1) l - Phi m (wext m p.2) l| ≤ ρ} with hf
  have hfswap : ∀ p, f (p.2, p.1) = f p := by
    intro p
    simp only [hf]
    congr 1
    ext l
    simp [abs_sub_comm]
  have hUeq : unordPairs m = P.filter (fun p => wext m p.1 (dIdx m p.1 p.2 + 1) = false) := by
    rw [unordPairs, hP, Finset.filter_filter]
  have hswap : ∑ p ∈ P.filter (fun p => ¬ (wext m p.1 (dIdx m p.1 p.2 + 1) = false)), f p
      = ∑ p ∈ P.filter (fun p => wext m p.1 (dIdx m p.1 p.2 + 1) = false), f p := by
    refine Finset.sum_nbij' (fun p => (p.2, p.1)) (fun p => (p.2, p.1)) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      obtain ⟨hpP, hptrue⟩ := Finset.mem_filter.mp hp
      have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hpP).2
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Ne.symm hne⟩
      · have hd := wext_diff hne
        show wext m p.2 (dIdx m p.2 p.1 + 1) = false
        rw [dIdx_comm m p.2 p.1]
        have h1 : wext m p.1 (dIdx m p.1 p.2 + 1) = true := by simpa using hptrue
        have h2 : wext m p.2 (dIdx m p.1 p.2 + 1) ≠ true := by
          rw [← h1]
          exact fun h => hd h.symm
        simpa using h2
    · intro p hp
      obtain ⟨hpP, hpfalse⟩ := Finset.mem_filter.mp hp
      have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hpP).2
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Ne.symm hne⟩
      · have hd := wext_diff hne
        show ¬ wext m p.2 (dIdx m p.2 p.1 + 1) = false
        rw [dIdx_comm m p.2 p.1]
        intro hb
        exact hd (by rw [hpfalse, hb])
    · intro p _; rfl
    · intro p _; rfl
    · intro p _; exact (hfswap p).symm
  have htotal : ∑ p ∈ P, f p = 2 * ∑ p ∈ unordPairs m, f p := by
    rw [hUeq, ← Finset.sum_filter_add_sum_filter_not P
      (fun p => wext m p.1 (dIdx m p.1 p.2 + 1) = false) f, hswap, two_mul]
  have hbound := sum_volume_close_le (m := m) (ρ := ρ) hρ
  rw [htotal] at hbound
  have hC : (8000 : ℝ) * lam0 / ((lam0 - 1) * (2 - lam0)) * ρ * (4 / lam0) ^ m
      = 2 * (4000 * lam0 / ((lam0 - 1) * (2 - lam0)) * ρ * (4 / lam0) ^ m) := by ring
  have hnn : 0 ≤ 4000 * lam0 / ((lam0 - 1) * (2 - lam0)) * ρ * (4 / lam0) ^ m := by
    have h1 := one_lt_lam0
    have h2 := lam0_lt_two
    have h3 : 0 < lam0 - 1 := by linarith
    have h4 : 0 < 2 - lam0 := by linarith
    have h5 : 0 < lam0 := by linarith
    positivity
  rw [hC, ENNReal.ofReal_mul (by norm_num), show ENNReal.ofReal (2:ℝ) = 2 by
    simp [ENNReal.ofReal_ofNat]] at hbound
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp hbound

/-! ### The pair-counting bound as an integral -/

lemma continuous_Phi (m : ℕ) (e : ℕ → Bool) : Continuous (Phi m e) := by
  unfold Phi
  fun_prop

lemma measurableSet_close (m : ℕ) (e e' : ℕ → Bool) (ρ : ℝ) :
    MeasurableSet {l : ℝ | |Phi m e l - Phi m e' l| ≤ ρ} :=
  (isClosed_le (((continuous_Phi m e).sub (continuous_Phi m e')).abs) continuous_const).measurableSet

open scoped Classical in
/-- The number of ordered pairs of distinct length-`m` branch words whose
endpoints at the parameter `l` are `ρ`-close. -/
noncomputable def pairCount (m : ℕ) (ρ l : ℝ) : ℕ :=
  ((Finset.univ : Finset ((Fin m → Bool) × (Fin m → Bool))).filter
    (fun p => p.1 ≠ p.2 ∧ |Phi m (wext m p.1) l - Phi m (wext m p.2) l| ≤ ρ)).card

open scoped Classical in
/-- **T10, integral form.**  The paper's pair-counting estimate: the integral
over the window `I = [1000/667, 2]` of the number of `ρ`-close pairs of
endpoints of length-`m` branch words is at most
`8λ₀ ρ (4/λ₀)^m / (δ(λ₀−1)(2−λ₀))` (ordered pairs; twice the constant of the
note, which counts unordered ones). -/
theorem lintegral_pairCount_le (m : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∫⁻ l in Iwin, (pairCount m ρ l : ℝ≥0∞)
      ≤ ENNReal.ofReal (8000 * lam0 / ((lam0 - 1) * (2 - lam0)) * ρ * (4 / lam0) ^ m) := by
  set P := (Finset.univ : Finset ((Fin m → Bool) × (Fin m → Bool))).filter (fun p => p.1 ≠ p.2)
    with hP
  set A : ((Fin m → Bool) × (Fin m → Bool)) → Set ℝ :=
    fun p => {l : ℝ | |Phi m (wext m p.1) l - Phi m (wext m p.2) l| ≤ ρ} with hA
  have hAmeas : ∀ p, MeasurableSet (A p) := fun p => measurableSet_close m _ _ ρ
  have hpoint : ∀ l : ℝ, (pairCount m ρ l : ℝ≥0∞)
      = ∑ p ∈ P, (A p).indicator (fun _ => (1 : ℝ≥0∞)) l := by
    intro l
    rw [pairCount, ← Finset.filter_filter, ← hP, Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases h : l ∈ A p
    · rw [Set.indicator_of_mem h]; exact if_pos h
    · rw [Set.indicator_of_notMem h]; exact if_neg h
  have hint : ∫⁻ l in Iwin, (pairCount m ρ l : ℝ≥0∞)
      = ∑ p ∈ P, volume {l ∈ Iwin | |Phi m (wext m p.1) l - Phi m (wext m p.2) l| ≤ ρ} := by
    rw [lintegral_congr hpoint]
    rw [MeasureTheory.lintegral_finset_sum _
      (fun p _ => (measurable_const.indicator (hAmeas p)))]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [MeasureTheory.lintegral_indicator (hAmeas p), MeasureTheory.setLIntegral_one,
      MeasureTheory.Measure.restrict_apply (hAmeas p)]
    congr 1
    ext l
    simp [hA, and_comm]
  rw [hint]
  exact sum_volume_close_le m hρ

end Transversality
end KnotGame
