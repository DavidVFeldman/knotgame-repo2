import RequestProject.KindTree

/-!
# T38 — the counting operator (paper `prop:lebeigen`)

The two branch maps of the game are `f λ 0 x = λ x` and `f λ 1 x = λ x - (λ-1)`
(`RequestProject.Basic`).  Their *transfer operator* on functions of `(0,1)` is

  `(T h)(y) = (1/λ) [ h (y/λ) + h ((y + λ - 1)/λ) ]`,

one term for each branch, the factor `1/λ` being the Jacobian.

* `T_one` : `T 1 = (2/λ) · 1`.  The two preimages listed are exactly the legal
  preimages: `branch_zero_preimage_mem_Ioo` and `branch_one_preimage_mem_Ioo`
  say each lies in the legal domain of its branch, `branch_zero_preimage` and
  `branch_one_preimage` say each is a preimage, and `f_injective` says it is
  the only one.  So each branch is a bijection from its legal domain onto
  `(0,1)` and every `y ∈ (0,1)` has exactly one legal preimage per branch.

* `integral_bcount` : `∫₀¹ B_λ(m,x) dx = (2/λ)^m`, where `B_λ(m,x)` counts the
  legal *branch* words of length `m` from `x` — the number of distinct knots
  that a knot at `x` can become in `m` steps.  This is the counting form of
  `T 1 = (2/λ) · 1`.

* `integral_kcount` : `∫₀¹ K_λ(m,x) dx = (3/λ)^m`, where `K_λ(m,x)` is the
  number of *kind words* of length `m` from `x` in the sense already fixed by
  `KindTree.kindWords`, i.e. words in the three-letter move alphabet
  `L, M, R`.  The constant is `3/λ`, not `2/λ`: see the scruples note below.

## Conventions (SCRUPLES)

* The commission's T38 asks for `∫₀¹ K_λ(m,x) dx = (2/λ)^m` with `K_λ(m,x)`
  "the number of kind words of length `m` from `x`" and the existing survival
  predicates reused.  Those two requirements are incompatible, and the
  formalisation records both true statements instead of one false one.  The
  existing predicate counts words in the **move** alphabet, and there each of
  the three moves contributes a branch that is a bijection from its legal
  domain onto `(0,1)`: `L` from `(g,1)`, `R` from `(0,r)` and `M` from
  `(0,r/2) ∪ (1-r/2,1)` (two pieces, onto `(0,1/2)` and `(1/2,1)`).  Hence the
  mean multiplication factor per step is `3/λ`, not `2/λ`, and
  `integral_kcount` proves `(3/λ)^m`.  At `λ = 3/2` this gives `2^m`, in
  agreement with `KindTree.card_kindWords_three_halves`, which is the sharpest
  available check on the constant: were it `(2/λ)^m = (4/3)^m`, the mean count
  would be smaller than the count `2^m` which holds at every point of the
  survival tree of `1/2`.
* The constant `2/λ` is correct for the **branch** count, which is what the
  operator `T` transfers: the move alphabet double-counts, because for
  `x < r/2` the moves `R` and `M` carry the knot to the same place, and for
  `x > 1-r/2` so do `L` and `M`.  `integral_bcount` proves `(2/λ)^m` for the
  branch count, so the paper's `prop:lebeigen` is certified in the reading in
  which its operator `T` is the transfer operator of the two branches.
* Both integrals are Bochner integrals over the open interval `(0,1)`; the
  endpoints are null, so the reading over `[0,1]` is the same.
-/

namespace KnotGame
namespace CountingOperator

open MeasureTheory Set

variable {lam : ℝ}

/-! ### The counting operator and its constant eigenfunction -/

/-- The counting operator `(T h)(y) = (1/λ)[h(y/λ) + h((y+λ-1)/λ)]`. -/
noncomputable def T (lam : ℝ) (h : ℝ → ℝ) (y : ℝ) : ℝ :=
  (1 / lam) * (h (y / lam) + h ((y + lam - 1) / lam))

lemma branch_zero_preimage (hlam : 1 < lam) (y : ℝ) : f lam 0 (y / lam) = y := by
  have h0 : lam ≠ 0 := ne_of_gt (lt_trans zero_lt_one hlam)
  simp only [f_zero]
  field_simp

lemma branch_one_preimage (hlam : 1 < lam) (y : ℝ) : f lam 1 ((y + lam - 1) / lam) = y := by
  have h0 : lam ≠ 0 := ne_of_gt (lt_trans zero_lt_one hlam)
  simp only [f_one]
  field_simp
  ring

/-- The legal domain of branch `0` is `(0, r)`: the preimage of `y ∈ (0,1)` lies
in it. -/
lemma branch_zero_preimage_mem (hlam : 1 < lam) {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    0 < y / lam ∧ y / lam < r lam := by
  have h0 : 0 < lam := lt_trans zero_lt_one hlam
  refine ⟨by positivity, ?_⟩
  rw [r, div_lt_iff₀ h0, inv_mul_cancel₀ (ne_of_gt h0)]
  exact hy1

/-- The legal domain of branch `1` is `(g, 1)`: the preimage of `y ∈ (0,1)` lies
in it. -/
lemma branch_one_preimage_mem (hlam : 1 < lam) {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    g lam < (y + lam - 1) / lam ∧ (y + lam - 1) / lam < 1 := by
  have h0 : 0 < lam := lt_trans zero_lt_one hlam
  constructor
  · rw [g, r, lt_div_iff₀ h0]
    have hc : (1 - lam⁻¹) * lam = lam - 1 := by field_simp
    rw [hc]
    linarith
  · rw [div_lt_one h0]
    linarith

/-- Branch `0` is injective, so the preimage exhibited above is the only one. -/
lemma f_zero_injective (hlam : 1 < lam) : Function.Injective (f lam 0) := by
  have h0 : lam ≠ 0 := ne_of_gt (lt_trans zero_lt_one hlam)
  intro a b hab
  simp only [f_zero] at hab
  exact mul_left_cancel₀ h0 hab

/-- Branch `1` is injective, so the preimage exhibited above is the only one. -/
lemma f_one_injective (hlam : 1 < lam) : Function.Injective (f lam 1) := by
  have h0 : lam ≠ 0 := ne_of_gt (lt_trans zero_lt_one hlam)
  intro a b hab
  simp only [f_one] at hab
  exact mul_left_cancel₀ h0 (by linarith)

/-- **Paper `prop:lebeigen`, the eigenvalue.**  The constant function `1` is an
eigenfunction of the counting operator with eigenvalue `2/λ`.  (Only `λ ≠ 0` is
used; the commission's range `1 < λ < 2` is what makes the two preimages the
legal ones, which is `branch_zero_preimage_mem` and `branch_one_preimage_mem`.)
-/
theorem T_one (hlam : 1 < lam) (hlam2 : lam < 2) (y : ℝ) :
    T lam (fun _ => 1) y = (2 / lam) * 1 := by
  have h0 : lam ≠ 0 := ne_of_gt (lt_trans zero_lt_one hlam)
  simp only [T]
  field_simp
  norm_num

/-! ### Measure-theoretic engine -/

lemma integral_Ioo_comp_affine (hlam : 1 < lam) (c a b u v : ℝ) (hab : a ≤ b)
    (hu : lam * a + c = u) (hv : lam * b + c = v) (H : ℝ → ℝ) :
    ∫ x in Ioo a b, H (lam * x + c) = (1 / lam) * ∫ y in Ioo u v, H y := by
  have h0 : (0:ℝ) < lam := lt_trans zero_lt_one hlam
  have huv : u ≤ v := by
    rw [← hu, ← hv]
    nlinarith
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_comp_mul_add H (ne_of_gt h0) c, hu, hv,
    intervalIntegral.integral_of_le huv, integral_Ioc_eq_integral_Ioo, smul_eq_mul,
    one_div]

lemma integral_indicator_Ioi (a : ℝ) (ha : 0 ≤ a) (H : ℝ → ℝ) :
    ∫ x in Ioo (0:ℝ) 1, (Ioi a).indicator H x = ∫ x in Ioo a 1, H x := by
  have hset : Ioo (0:ℝ) 1 ∩ Ioi a = Ioo a 1 := by
    ext x
    simp only [Set.mem_inter_iff, mem_Ioo, mem_Ioi]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨lt_of_le_of_lt ha h1, h2⟩, h1⟩
  rw [setIntegral_indicator measurableSet_Ioi, hset]

lemma integral_indicator_Iio (a : ℝ) (ha : a ≤ 1) (H : ℝ → ℝ) :
    ∫ x in Ioo (0:ℝ) 1, (Iio a).indicator H x = ∫ x in Ioo 0 a, H x := by
  have hset : Ioo (0:ℝ) 1 ∩ Iio a = Ioo 0 a := by
    ext x
    simp only [Set.mem_inter_iff, mem_Ioo, mem_Iio]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, lt_of_lt_of_le h2 ha⟩, h2⟩
  rw [setIntegral_indicator measurableSet_Iio, hset]

/-! ### The branch count -/

/-- `B_λ(m,x)`: the number of legal branch words of length `m` from `x`, i.e.
the number of orbits of length `m` of `x` under the two branch maps that stay
inside `(0,1)`.  Branch `0` is legal at `x` when `λ x < 1`, branch `1` when
`λ x - (λ-1) > 0`. -/
noncomputable def bcount (lam : ℝ) : ℝ → ℕ → ℝ
  | _, 0 => 1
  | x, (m + 1) =>
      (if x < r lam then bcount lam (lam * x) m else 0)
      + (if g lam < x then bcount lam (lam * x + (1 - lam)) m else 0)

@[simp] lemma bcount_zero (lam x : ℝ) : bcount lam x 0 = 1 := rfl

lemma bcount_succ (lam x : ℝ) (m : ℕ) :
    bcount lam x (m + 1) =
      (if x < r lam then bcount lam (lam * x) m else 0)
      + (if g lam < x then bcount lam (lam * x + (1 - lam)) m else 0) := rfl

lemma bcount_nonneg (lam x : ℝ) (m : ℕ) : 0 ≤ bcount lam x m := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
      rw [bcount_succ]
      have h1 : 0 ≤ (if x < r lam then bcount lam (lam * x) m else 0) := by
        split_ifs
        · exact ih _
        · exact le_rfl
      have h2 : 0 ≤ (if g lam < x then bcount lam (lam * x + (1 - lam)) m else 0) := by
        split_ifs
        · exact ih _
        · exact le_rfl
      linarith

lemma bcount_le (lam x : ℝ) (m : ℕ) : bcount lam x m ≤ 2 ^ m := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
      rw [bcount_succ, pow_succ]
      have h1 : (if x < r lam then bcount lam (lam * x) m else 0) ≤ 2 ^ m := by
        split_ifs
        · exact ih _
        · positivity
      have h2 : (if g lam < x then bcount lam (lam * x + (1 - lam)) m else 0) ≤ 2 ^ m := by
        split_ifs
        · exact ih _
        · positivity
      linarith

lemma measurable_bcount (lam : ℝ) (m : ℕ) : Measurable (fun x => bcount lam x m) := by
  classical
  induction m with
  | zero => simp only [bcount_zero]; exact measurable_const
  | succ m ih =>
      have h1 : Measurable fun x : ℝ => bcount lam (lam * x) m :=
        ih.comp (by fun_prop)
      have h2 : Measurable fun x : ℝ => bcount lam (lam * x + (1 - lam)) m :=
        ih.comp (by fun_prop)
      simp only [bcount_succ]
      exact (Measurable.ite measurableSet_Iio h1 measurable_const).add
        (Measurable.ite measurableSet_Ioi h2 measurable_const)

lemma integrableOn_bcount (lam : ℝ) (m : ℕ) {s : Set ℝ} (hs : volume s ≠ ⊤) :
    IntegrableOn (fun x => bcount lam x m) s := by
  refine Measure.integrableOn_of_bounded hs
    (measurable_bcount lam m).aestronglyMeasurable (M := 2 ^ m) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (bcount_nonneg lam x m)]
  exact bcount_le lam x m

lemma integrableOn_bcount_affine (lam c : ℝ) (m : ℕ) {s : Set ℝ} (hs : volume s ≠ ⊤) :
    IntegrableOn (fun x => bcount lam (lam * x + c) m) s := by
  refine Measure.integrableOn_of_bounded hs
    (((measurable_bcount lam m).comp (by fun_prop)).aestronglyMeasurable) (M := 2 ^ m) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (bcount_nonneg lam _ m)]
  exact bcount_le lam _ m

lemma integral_add4 {s : Set ℝ} {A B C D : ℝ → ℝ}
    (hA : IntegrableOn A s) (hB : IntegrableOn B s)
    (hC : IntegrableOn C s) (hD : IntegrableOn D s) :
    ∫ x in s, (A x + B x + C x + D x)
      = (∫ x in s, A x) + (∫ x in s, B x) + (∫ x in s, C x) + (∫ x in s, D x) := by
  have h1 : IntegrableOn (fun x => A x + B x) s := hA.add hB
  have h2 : IntegrableOn (fun x => A x + B x + C x) s := h1.add hC
  rw [integral_add h2 hD, integral_add h1 hC, integral_add hA hB]

lemma integral_Ioo_comp_mul (hlam : 1 < lam) (a b u v : ℝ) (hab : a ≤ b)
    (hu : lam * a = u) (hv : lam * b = v) (H : ℝ → ℝ) :
    ∫ x in Ioo a b, H (lam * x) = (1 / lam) * ∫ y in Ioo u v, H y := by
  have h := integral_Ioo_comp_affine hlam 0 a b u v hab (by simpa using hu) (by simpa using hv) H
  simpa using h

/-- One step of the branch count integrates to `2/λ` times the previous one. -/
theorem integral_bcount_succ (hlam : 1 < lam) (m : ℕ) :
    ∫ x in Ioo (0:ℝ) 1, bcount lam x (m + 1)
      = (2 / lam) * ∫ x in Ioo (0:ℝ) 1, bcount lam x m := by
  have hr0 : 0 < r lam := r_pos lam hlam
  have hr1 : r lam < 1 := r_lt_one lam hlam
  have hg0 : 0 < g lam := g_pos lam hlam
  have hg1 : g lam < 1 := g_lt_one lam hlam
  have hlam0 : (0:ℝ) < lam := lt_trans zero_lt_one hlam
  have hmul : lam * r lam = 1 := by
    rw [r]; field_simp
  have hmulg : lam * g lam + (1 - lam) = 0 := by
    rw [g, r]; field_simp; ring
  have hfin : volume (Ioo (0:ℝ) 1) ≠ ⊤ := by simp
  -- pointwise decomposition into two indicator terms
  have hpt : ∀ x : ℝ, bcount lam x (m + 1)
      = (Iio (r lam)).indicator (fun x => bcount lam (lam * x) m) x
        + (Ioi (g lam)).indicator (fun x => bcount lam (lam * x + (1 - lam)) m) x := by
    intro x
    rw [bcount_succ, Set.indicator_apply, Set.indicator_apply]
    simp only [mem_Iio, mem_Ioi]
  rw [setIntegral_congr_fun measurableSet_Ioo (fun x _ => hpt x)]
  rw [integral_add ((integrableOn_bcount_affine lam 0 m hfin).congr_fun
        (fun x _ => by simp) measurableSet_Ioo |>.indicator measurableSet_Iio)
      ((integrableOn_bcount_affine lam (1 - lam) m hfin).indicator measurableSet_Ioi)]
  rw [integral_indicator_Iio _ hr1.le, integral_indicator_Ioi _ hg0.le]
  rw [integral_Ioo_comp_mul hlam 0 (r lam) 0 1 hr0.le (by ring) hmul
      (fun y => bcount lam y m),
    integral_Ioo_comp_affine hlam (1 - lam) (g lam) 1 0 1 hg1.le hmulg (by ring)
      (fun y => bcount lam y m)]
  ring

/-- **The counting form of `T 1 = (2/λ)·1`.**  The mean number of legal branch
words of length `m` is `(2/λ)^m`. -/
theorem integral_bcount (hlam : 1 < lam) (m : ℕ) :
    ∫ x in Ioo (0:ℝ) 1, bcount lam x m = (2 / lam) ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [integral_bcount_succ hlam m, ih, pow_succ]; ring

/-! ### `bcount` really counts branch words -/

/-- The words of a given length over the two-letter branch alphabet. -/
def binWords : ℕ → Finset (List (Fin 2))
  | 0 => {[]}
  | n + 1 => (Finset.univ : Finset (Fin 2)).biUnion (fun i => (binWords n).image (List.cons i))

lemma mem_binWords : ∀ {n : ℕ} {w : List (Fin 2)}, w ∈ binWords n ↔ w.length = n
  | 0, w => by
      constructor
      · intro h; simp [binWords] at h; simp [h]
      · intro h; simp [binWords, List.length_eq_zero_iff.mp h]
  | n + 1, w => by
      simp only [binWords, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨i, v, hv, rfl⟩
        simp [mem_binWords.mp hv]
      · intro h
        match w with
        | [] => simp at h
        | i :: v => exact ⟨i, v, mem_binWords.mpr (by simpa using h), rfl⟩

/-- Branch `i` is legal at `x` exactly when its image stays inside `(0,1)`:
branch `0` needs `λ x < 1`, branch `1` needs `λ x - (λ-1) > 0`. -/
def branchLegal (lam : ℝ) (i : Fin 2) (x : ℝ) : Prop := if i = 0 then x < r lam else g lam < x

noncomputable instance decidableBranchLegal (lam : ℝ) (i : Fin 2) (x : ℝ) :
    Decidable (branchLegal lam i x) := by
  unfold branchLegal
  split <;> infer_instance

@[simp] lemma branchLegal_zero (lam x : ℝ) : branchLegal lam 0 x ↔ x < r lam := by
  rw [branchLegal, if_pos rfl]

@[simp] lemma branchLegal_one (lam x : ℝ) : branchLegal lam 1 x ↔ g lam < x := by
  rw [branchLegal, if_neg (by decide : ¬ ((1 : Fin 2) = 0))]

/-- Branch `0` is legal at `x ∈ (0,1)` exactly when its image stays in `(0,1)`. -/
lemma branchLegal_zero_iff (hlam : 1 < lam) {x : ℝ} (hx0 : 0 < x) :
    branchLegal lam 0 x ↔ f lam 0 x ∈ Ioo (0:ℝ) 1 := by
  have hlam0 : (0:ℝ) < lam := lt_trans zero_lt_one hlam
  have hrr : lam * r lam = 1 := by rw [r]; field_simp
  rw [branchLegal_zero, f_zero, mem_Ioo]
  constructor
  · intro h
    exact ⟨mul_pos hlam0 hx0, by nlinarith⟩
  · rintro ⟨-, h2⟩
    nlinarith

/-- Branch `1` is legal at `x < 1` exactly when its image stays in `(0,1)`. -/
lemma branchLegal_one_iff (hlam : 1 < lam) {x : ℝ} (hx1 : x < 1) :
    branchLegal lam 1 x ↔ f lam 1 x ∈ Ioo (0:ℝ) 1 := by
  have hlam0 : (0:ℝ) < lam := lt_trans zero_lt_one hlam
  have hgg : lam * g lam = lam - 1 := by rw [g, r]; field_simp
  rw [branchLegal_one, f_one, mem_Ioo]
  constructor
  · intro h
    exact ⟨by nlinarith, by nlinarith⟩
  · rintro ⟨h1, -⟩
    nlinarith

/-- A branch word is legal from `x` when every step of the orbit is. -/
def branchSurvivesWord (lam : ℝ) : ℝ → List (Fin 2) → Prop
  | _, [] => True
  | x, i :: w => branchLegal lam i x ∧ branchSurvivesWord lam (f lam i x) w

noncomputable instance decidableBranchSurvivesWord (lam : ℝ) :
    ∀ (x : ℝ) (w : List (Fin 2)), Decidable (branchSurvivesWord lam x w)
  | _, [] => by unfold branchSurvivesWord; infer_instance
  | x, i :: w => by
      letI := decidableBranchSurvivesWord lam (f lam i x) w
      unfold branchSurvivesWord
      infer_instance

/-- The legal branch words of length `m` from `x`. -/
noncomputable def branchWords (lam x : ℝ) (m : ℕ) : Finset (List (Fin 2)) :=
  (binWords m).filter (fun w => branchSurvivesWord lam x w)

lemma mem_branchWords {lam x : ℝ} {m : ℕ} {w : List (Fin 2)} :
    w ∈ branchWords lam x m ↔ w.length = m ∧ branchSurvivesWord lam x w := by
  simp [branchWords, mem_binWords]

lemma branchWords_succ (lam x : ℝ) (m : ℕ) :
    branchWords lam x (m + 1)
      = (Finset.univ.filter (fun i : Fin 2 => branchLegal lam i x)).biUnion
          (fun i => (branchWords lam (f lam i x) m).image (List.cons i)) := by
  classical
  ext w
  simp only [mem_branchWords, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_image]
  constructor
  · rintro ⟨hlen, hsurv⟩
    match w with
    | [] => simp at hlen
    | i :: v =>
        obtain ⟨h1, h2⟩ := hsurv
        exact ⟨i, h1, v, ⟨by simpa using hlen, h2⟩, rfl⟩
  · rintro ⟨i, hi, v, ⟨hlen, hsurv⟩, rfl⟩
    exact ⟨by simp [hlen], ⟨hi, hsurv⟩⟩

lemma card_branchWords_succ (lam x : ℝ) (m : ℕ) :
    (branchWords lam x (m + 1)).card
      = ∑ i ∈ Finset.univ.filter (fun i : Fin 2 => branchLegal lam i x),
          (branchWords lam (f lam i x) m).card := by
  classical
  rw [branchWords_succ, Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun i _ =>
      Finset.card_image_of_injective _ (List.cons_injective)
  · intro a _ b _ hab
    simp only [Finset.disjoint_left, Finset.mem_image]
    rintro w ⟨u, -, rfl⟩ ⟨v, -, hv⟩
    obtain ⟨h1, -⟩ := List.cons_eq_cons.mp hv
    exact hab h1.symm

/-- `bcount` is the number of legal branch words: the recursion of `bcount` is
the branching of the tree of legal branch words. -/
theorem bcount_eq_card (lam : ℝ) : ∀ (m : ℕ) (x : ℝ),
    bcount lam x m = ((branchWords lam x m).card : ℝ)
  | 0, x => by
      classical
      have h : branchWords lam x 0 = {[]} := by
        ext w
        simp only [mem_branchWords, Finset.mem_singleton, List.length_eq_zero_iff]
        constructor
        · rintro ⟨h, -⟩; exact h
        · rintro rfl; exact ⟨rfl, trivial⟩
      rw [bcount_zero, h, Finset.card_singleton, Nat.cast_one]
  | (m + 1), x => by
      classical
      have hzero : f lam 0 x = lam * x := by simp
      have hone : f lam 1 x = lam * x + (1 - lam) := by simp; ring
      rw [bcount_succ, card_branchWords_succ]
      push_cast
      rw [Finset.sum_filter, Fin.sum_univ_two]
      rw [bcount_eq_card lam m (lam * x), bcount_eq_card lam m (lam * x + (1 - lam))]
      simp only [hzero, hone, branchLegal_zero, branchLegal_one]

/-! ### The kind-word count -/

/-- `K_λ(m,x)`: the number of kind words of length `m` from `x`, in the sense
of `KindTree.kindWords` — words in the three-letter move alphabet that a knot
at `x` survives. -/
noncomputable def kcount (lam x : ℝ) (m : ℕ) : ℝ := ((KindTree.kindWords lam x m).card : ℝ)

@[simp] lemma kcount_zero (lam x : ℝ) : kcount lam x 0 = 1 := by
  rw [kcount, KindTree.card_kindWords_zero]
  norm_num

lemma kcount_eq_sum (lam x : ℝ) (m : ℕ) :
    kcount lam x m
      = ∑ w ∈ KindTree.words m, (if survivesWord lam x w then (1:ℝ) else 0) := by
  classical
  rw [kcount, KindTree.kindWords, Finset.card_filter]
  push_cast
  rfl

lemma kcount_nonneg (lam x : ℝ) (m : ℕ) : 0 ≤ kcount lam x m := by
  rw [kcount]; positivity

lemma kcount_le (lam x : ℝ) (m : ℕ) : kcount lam x m ≤ ((KindTree.words m).card : ℝ) := by
  rw [kcount]
  exact_mod_cast Finset.card_filter_le _ _

lemma measurableSet_survives (lam : ℝ) (mv : Move) :
    MeasurableSet {x : ℝ | survives lam mv x} := by
  cases mv
  · exact measurableSet_Ioi
  · have hset : {x : ℝ | survives lam Move.M x} = Iio (r lam / 2) ∪ Ioi (1 - r lam / 2) := by
      ext x; simp [Set.mem_union]
    rw [hset]
    exact measurableSet_Iio.union measurableSet_Ioi
  · exact measurableSet_Iio

lemma measurable_act (lam : ℝ) (mv : Move) : Measurable (act lam mv) := by
  classical
  cases mv
  · have hL : act lam Move.L = fun x : ℝ => lam * x - (lam - 1) := by
      funext x; simp
    rw [hL]; fun_prop
  · have hM : act lam Move.M
        = fun x : ℝ => if x < r lam / 2 then lam * x else lam * x - (lam - 1) := by
      funext x
      by_cases h : x < r lam / 2
      · rw [act_M_of_lt lam x h, if_pos h]
      · rw [act_M_of_gt lam x h, if_neg h]
    rw [hM]
    exact Measurable.ite measurableSet_Iio (by fun_prop) (by fun_prop)
  · have hR : act lam Move.R = fun x : ℝ => lam * x := by
      funext x; simp
    rw [hR]; fun_prop

lemma measurableSet_survivesWord (lam : ℝ) :
    ∀ w : List Move, MeasurableSet {x : ℝ | survivesWord lam x w}
  | [] => by simp
  | mv :: w => by
      have hrec : {x : ℝ | survivesWord lam x (mv :: w)}
          = {x : ℝ | survives lam mv x} ∩ act lam mv ⁻¹' {x : ℝ | survivesWord lam x w} := by
        ext x; simp [survivesWord]
      rw [hrec]
      exact (measurableSet_survives lam mv).inter
        ((measurableSet_survivesWord lam w).preimage (measurable_act lam mv))

lemma measurable_kcount (lam : ℝ) (m : ℕ) : Measurable (fun x => kcount lam x m) := by
  classical
  simp only [kcount_eq_sum]
  refine Finset.measurable_sum _ (fun w _ => ?_)
  exact Measurable.ite (measurableSet_survivesWord lam w) measurable_const measurable_const

lemma integrableOn_kcount_affine (lam c : ℝ) (m : ℕ) {s : Set ℝ} (hs : volume s ≠ ⊤) :
    IntegrableOn (fun x => kcount lam (lam * x + c) m) s := by
  refine Measure.integrableOn_of_bounded hs
    (((measurable_kcount lam m).comp (by fun_prop)).aestronglyMeasurable)
    (M := ((KindTree.words m).card : ℝ)) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (kcount_nonneg lam _ m)]
  exact kcount_le lam _ m

lemma sum_move (F : Move → ℝ) : ∑ mv : Move, F mv = F Move.L + F Move.M + F Move.R := by
  rw [show (Finset.univ : Finset Move) = {Move.L, Move.M, Move.R} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

lemma kcount_succ_moves (lam x : ℝ) (m : ℕ) :
    kcount lam x (m + 1)
      = (if survives lam Move.L x then kcount lam (act lam Move.L x) m else 0)
        + (if survives lam Move.M x then kcount lam (act lam Move.M x) m else 0)
        + (if survives lam Move.R x then kcount lam (act lam Move.R x) m else 0) := by
  classical
  rw [kcount, KindTree.card_kindWords_succ]
  push_cast
  rw [Finset.sum_filter]
  rw [sum_move (fun mv => if survives lam mv x then
    ((KindTree.kindWords lam (act lam mv x) m).card : ℝ) else 0)]
  rfl

/-- The pointwise recursion for `K_λ`, resolved into the four affine branches:
`L` on `(g,1)`, `R` on `(0,r)`, and the two pieces of `M`, on `(0,r/2)` and on
`(1-r/2,1)`. -/
lemma kcount_succ (hlam : 1 < lam) (x : ℝ) (m : ℕ) :
    kcount lam x (m + 1)
      = (if g lam < x then kcount lam (lam * x + (1 - lam)) m else 0)
        + (if x < r lam then kcount lam (lam * x) m else 0)
        + (if x < r lam / 2 then kcount lam (lam * x) m else 0)
        + (if 1 - r lam / 2 < x then kcount lam (lam * x + (1 - lam)) m else 0) := by
  have hr1 : r lam < 1 := r_lt_one lam hlam
  have hr0 : 0 < r lam := r_pos lam hlam
  have hL : act lam Move.L x = lam * x + (1 - lam) := by simp; ring
  have hR : act lam Move.R x = lam * x := by simp
  have hM : (if survives lam Move.M x then kcount lam (act lam Move.M x) m else 0)
      = (if x < r lam / 2 then kcount lam (lam * x) m else 0)
        + (if 1 - r lam / 2 < x then kcount lam (lam * x + (1 - lam)) m else 0) := by
    by_cases h1 : x < r lam / 2
    · have h2 : ¬ (1 - r lam / 2 < x) := by intro hc; linarith
      rw [act_M_of_lt lam x h1, if_pos (show survives lam Move.M x from Or.inl h1),
        if_pos h1, if_neg h2]
      ring
    · by_cases h2 : 1 - r lam / 2 < x
      · have hact : act lam Move.M x = lam * x + (1 - lam) := by
          rw [act_M_of_gt lam x h1]; ring
        rw [hact, if_pos (show survives lam Move.M x from Or.inr h2), if_neg h1, if_pos h2]
        ring
      · have hns : ¬ survives lam Move.M x := by
          rw [survives_M]
          push_neg
          exact ⟨not_lt.mp h1, not_lt.mp h2⟩
        rw [if_neg hns, if_neg h1, if_neg h2]
        ring
  rw [kcount_succ_moves, hM]
  simp only [survives_L, survives_R, hL, hR]
  ring

/-- One step of the kind-word count integrates to `3/λ` times the previous
one. -/
theorem integral_kcount_succ (hlam : 1 < lam) (m : ℕ) :
    ∫ x in Ioo (0:ℝ) 1, kcount lam x (m + 1)
      = (3 / lam) * ∫ x in Ioo (0:ℝ) 1, kcount lam x m := by
  have hr0 : 0 < r lam := r_pos lam hlam
  have hr1 : r lam < 1 := r_lt_one lam hlam
  have hg0 : 0 < g lam := g_pos lam hlam
  have hg1 : g lam < 1 := g_lt_one lam hlam
  have hlam0 : (0:ℝ) < lam := lt_trans zero_lt_one hlam
  have hmul : lam * r lam = 1 := by rw [r]; field_simp
  have hmulg : lam * g lam + (1 - lam) = 0 := by rw [g, r]; field_simp; ring
  have hmulhalf : lam * (r lam / 2) = 1 / 2 := by rw [r]; field_simp
  have hmulhi : lam * (1 - r lam / 2) + (1 - lam) = 1 / 2 := by rw [r]; field_simp; ring
  have hfin : volume (Ioo (0:ℝ) 1) ≠ ⊤ := by simp
  have hhalf0 : (0:ℝ) ≤ r lam / 2 := by linarith
  have hhalf1 : r lam / 2 ≤ 1 := by linarith
  have hhi0 : (0:ℝ) ≤ 1 - r lam / 2 := by linarith
  have hhi1 : 1 - r lam / 2 ≤ 1 := by linarith
  have hIL : IntegrableOn (fun x : ℝ => kcount lam (lam * x + (1 - lam)) m) (Ioo (0:ℝ) 1) :=
    integrableOn_kcount_affine lam (1 - lam) m hfin
  have hIR : IntegrableOn (fun x : ℝ => kcount lam (lam * x) m) (Ioo (0:ℝ) 1) :=
    (integrableOn_kcount_affine lam 0 m hfin).congr_fun (fun x _ => by simp) measurableSet_Ioo
  have hpt : ∀ x : ℝ, kcount lam x (m + 1)
      = ((Ioi (g lam)).indicator (fun x => kcount lam (lam * x + (1 - lam)) m) x
          + (Iio (r lam)).indicator (fun x => kcount lam (lam * x) m) x
          + (Iio (r lam / 2)).indicator (fun x => kcount lam (lam * x) m) x)
        + (Ioi (1 - r lam / 2)).indicator
            (fun x => kcount lam (lam * x + (1 - lam)) m) x := by
    intro x
    rw [kcount_succ hlam x m]
    simp only [Set.indicator_apply, mem_Ioi, mem_Iio]
  have hA : IntegrableOn
      (fun x => (Ioi (g lam)).indicator (fun x => kcount lam (lam * x + (1 - lam)) m) x)
      (Ioo (0:ℝ) 1) := hIL.indicator measurableSet_Ioi
  have hB : IntegrableOn
      (fun x => (Iio (r lam)).indicator (fun x => kcount lam (lam * x) m) x)
      (Ioo (0:ℝ) 1) := hIR.indicator measurableSet_Iio
  have hC : IntegrableOn
      (fun x => (Iio (r lam / 2)).indicator (fun x => kcount lam (lam * x) m) x)
      (Ioo (0:ℝ) 1) := hIR.indicator measurableSet_Iio
  have hD : IntegrableOn
      (fun x => (Ioi (1 - r lam / 2)).indicator
        (fun x => kcount lam (lam * x + (1 - lam)) m) x)
      (Ioo (0:ℝ) 1) := hIL.indicator measurableSet_Ioi
  rw [setIntegral_congr_fun measurableSet_Ioo (fun x _ => hpt x)]
  rw [integral_add4 hA hB hC hD]
  rw [integral_indicator_Ioi _ hg0.le, integral_indicator_Iio _ hr1.le,
    integral_indicator_Iio _ hhalf1, integral_indicator_Ioi _ hhi0]
  rw [integral_Ioo_comp_affine hlam (1 - lam) (g lam) 1 0 1 hg1.le hmulg (by ring)
      (fun y => kcount lam y m),
    integral_Ioo_comp_mul hlam 0 (r lam) 0 1 hr0.le (by ring) hmul (fun y => kcount lam y m),
    integral_Ioo_comp_mul hlam 0 (r lam / 2) 0 (1/2) hhalf0 (by ring) hmulhalf
      (fun y => kcount lam y m),
    integral_Ioo_comp_affine hlam (1 - lam) (1 - r lam / 2) 1 (1/2) 1 hhi1 hmulhi (by ring)
      (fun y => kcount lam y m)]
  have hsplit : (∫ y in Ioo (0:ℝ) (1/2), kcount lam y m)
      + ∫ y in Ioo (1/2 : ℝ) 1, kcount lam y m = ∫ y in Ioo (0:ℝ) 1, kcount lam y m := by
    have hI : ∀ a b : ℝ, IntervalIntegrable (fun y => kcount lam y m) volume a b := by
      intro a b
      constructor <;>
        exact Measure.integrableOn_of_bounded (by simp)
          ((measurable_kcount lam m).aestronglyMeasurable)
          (M := ((KindTree.words m).card : ℝ))
          (by
            filter_upwards with x
            rw [Real.norm_eq_abs, abs_of_nonneg (kcount_nonneg lam x m)]
            exact kcount_le lam x m)
    have hadd := intervalIntegral.integral_add_adjacent_intervals (hI 0 (1/2)) (hI (1/2) 1)
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1/2),
      intervalIntegral.integral_of_le (by norm_num : (1/2:ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo,
      integral_Ioc_eq_integral_Ioo] at hadd
    exact hadd
  have hlamne : lam ≠ 0 := ne_of_gt hlam0
  field_simp
  linarith [hsplit]

/-- **The mean kind-word count.**  `∫₀¹ K_λ(m,x) dx = (3/λ)^m`: each of the
three moves contributes a branch that is a bijection from its legal domain onto
`(0,1)`.  At `λ = 3/2` this is `2^m`, in agreement with
`KindTree.card_kindWords_three_halves`. -/
theorem integral_kcount (hlam : 1 < lam) (m : ℕ) :
    ∫ x in Ioo (0:ℝ) 1, kcount lam x m = (3 / lam) ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [integral_kcount_succ hlam m, ih, pow_succ]; ring

/-- The consistency check at `λ = 3/2`: the mean kind-word count is `2^m`, the
value that `KindTree.card_kindWords_three_halves` gives at every node of the
survival tree of `1/2`. -/
theorem integral_kcount_three_halves (m : ℕ) :
    ∫ x in Ioo (0:ℝ) 1, kcount (3/2 : ℝ) x m = 2 ^ m := by
  rw [integral_kcount (by norm_num : (1:ℝ) < 3/2) m]
  norm_num

end CountingOperator
end KnotGame
