import RequestProject.Gaps

/-!
# T19 — two short consequences of the gap law

## (a) The deficit law (paper Corollary `cor:deficit`)

Write `S` for the *spread* of a configuration, the distance from its leftmost
to its rightmost knot, and `T = 1 - S` for the *deficit*.  Across a move at
which no knot dies and none is born outside the current range, the gap law
`gap_law` (T2) for the extreme pair says `S ↦ λS - (λ-1)` when that pair
straddles and `S ↦ λS` otherwise; substituting `S = 1 - T` gives
`T ↦ λT` in the straddling case and `T ↦ λT - (λ-1)` otherwise.

* `deficit_law` — the law itself, for the extreme pair;
* `step_extremes` — the hypothesis "no death, no range-extending birth" indeed
  makes `act m x` and `act m y` the extremes of the new configuration.

## (b) Free births (paper Lemma `lem:free`)

An `M` is *free* for the configuration `C` when it acts on `C` exactly as an
`R` (or exactly as an `L`) does — same survivors, same images — so that it adds
a knot at no cost.  `ActsAs` below is that relation.

* `actsAs_M_R_of_forall_lt`, `actsAs_M_L_of_forall_gt` — the two sufficient
  conditions of the paper: `C` contained in `[0, r/2)`, resp. in `(1 - r/2, 1]`;
* `forall_lt_of_actsAs_M_R`, `forall_gt_of_actsAs_M_L` — the converses, **valid
  as stated only for `λ < 3/2`**;
* `actsAs_M_R_iff`, `actsAs_M_L_iff` — the biconditionals of `lem:free`, under
  `1 < λ < 3/2`;
* `actsAs_M_R_converse_fails` — a counterexample showing that for `λ ≥ 3/2` the
  converse direction of `lem:free` is false as literally stated.  This is the
  `λ ≥ 3/2` versus `λ < 3/2` position of `1 - r/2` relative to `r` that the
  paper's proof flags: when `r ≤ 1 - r/2` a knot sitting in `[r, 1 - r/2]` is
  deleted by `M` *and* by `R`, so `M` acts on the one-knot configuration `{r}`
  exactly as `R` does even though `r ≥ r/2`.  The paper's argument at this
  point invokes a knot in `(1 - r/2, 1]`, which need not belong to `C`.
* `step_M_eq_of_actsAs` — the payoff: if `M` acts as `m'` on `C`, the new
  configuration is the one `m'` would produce, plus the newborn knot at `1/2`.
-/

namespace KnotGame

variable {lam : ℝ}

/-! ## (a) The deficit law -/

/-- The *deficit* of the pair `(x, y)`: one minus the spread `y - x`. -/
def deficit (x y : ℝ) : ℝ := 1 - (y - x)

/-- **T19(a)** (paper Corollary `cor:deficit`).  Across a move survived by both
extreme knots, the deficit `T = 1 - spread` obeys `T ↦ λT` when the extreme
pair straddles (which happens only at an `M`), and `T ↦ λT - (λ-1)`
otherwise. -/
theorem deficit_law (h : 1 < lam) (m : Move) {x y : ℝ}
    (hx : survives lam m x) (hy : survives lam m y) (hxy : x < y) :
    deficit (act lam m x) (act lam m y) = lam * deficit x y - (lam - 1) ∨
      (m = Move.M ∧ Straddles lam x y ∧
        deficit (act lam m x) (act lam m y) = lam * deficit x y) := by
  rcases gap_law h m hx hy hxy with hg | ⟨hm, hs, hg⟩
  · left; simp only [deficit]; linarith
  · exact Or.inr ⟨hm, hs, by simp only [deficit]; linarith⟩

lemma act_le_act (h : 1 < lam) (m : Move) {x y : ℝ}
    (hx : survives lam m x) (hy : survives lam m y) (hxy : x ≤ y) :
    act lam m x ≤ act lam m y := by
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · exact le_refl _
  · exact (act_lt_act h m hx hy hlt).le

/-- **No death, no range-extending birth.**  If every knot of `C` survives the
move `m`, and (when `m = M`) the newborn knot at `1/2` does not fall outside the
image of the current range, then the extremes of the new configuration are
exactly the images of the old extremes. -/
theorem step_extremes (h : 1 < lam) (m : Move) {C : Finset ℝ} {x y : ℝ}
    (hxC : x ∈ C) (hyC : y ∈ C) (hlo : ∀ z ∈ C, x ≤ z) (hhi : ∀ z ∈ C, z ≤ y)
    (hsurv : ∀ z ∈ C, survives lam m z)
    (hbirth : m = Move.M → act lam m x ≤ 1/2 ∧ (1:ℝ)/2 ≤ act lam m y) :
    act lam m x ∈ step lam m C ∧ act lam m y ∈ step lam m C ∧
      ∀ z ∈ step lam m C, act lam m x ≤ z ∧ z ≤ act lam m y := by
  classical
  have hfil : survivors lam m C = C := Finset.filter_true_of_mem hsurv
  have himg : ∀ z ∈ (survivors lam m C).image (act lam m),
      act lam m x ≤ z ∧ z ≤ act lam m y := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    rw [hfil] at hw
    exact ⟨act_le_act h m (hsurv x hxC) (hsurv w hw) (hlo w hw),
      act_le_act h m (hsurv w hw) (hsurv y hyC) (hhi w hw)⟩
  have hmemx : act lam m x ∈ (survivors lam m C).image (act lam m) :=
    Finset.mem_image_of_mem _ (by rw [hfil]; exact hxC)
  have hmemy : act lam m y ∈ (survivors lam m C).image (act lam m) :=
    Finset.mem_image_of_mem _ (by rw [hfil]; exact hyC)
  cases m with
  | L =>
      refine ⟨by simpa using hmemx, by simpa using hmemy, ?_⟩
      intro z hz; exact himg z (by simpa using hz)
  | R =>
      refine ⟨by simpa using hmemx, by simpa using hmemy, ?_⟩
      intro z hz; exact himg z (by simpa using hz)
  | M =>
      obtain ⟨hb1, hb2⟩ := hbirth rfl
      refine ⟨by rw [step_M]; exact Finset.mem_union_left _ hmemx,
        by rw [step_M]; exact Finset.mem_union_left _ hmemy, ?_⟩
      intro z hz
      rw [step_M, Finset.mem_union] at hz
      rcases hz with hz | hz
      · exact himg z hz
      · rw [Finset.mem_singleton.mp hz]; exact ⟨hb1, hb2⟩

/-! ## (b) Free births -/

/-- `ActsAs lam m m' C`: the move `m` acts on the configuration `C` exactly as
`m'` does — the same knots of `C` survive, and the survivors are carried to the
same places. -/
def ActsAs (lam : ℝ) (m m' : Move) (C : Finset ℝ) : Prop :=
  (∀ x ∈ C, (survives lam m x ↔ survives lam m' x)) ∧
    (∀ x ∈ C, survives lam m x → act lam m x = act lam m' x)

/-- If every knot of `C` lies below `r/2`, then `M` acts on `C` exactly as `R`
does (paper Lemma `lem:free`, the easy direction). -/
theorem actsAs_M_R_of_forall_lt (h : 1 < lam) {C : Finset ℝ}
    (hC : ∀ x ∈ C, x < r lam / 2) : ActsAs lam Move.M Move.R C := by
  have hr0 : 0 < r lam := r_pos lam h
  refine ⟨fun x hx => ?_, fun x hx _ => ?_⟩
  · have hxr : x < r lam := lt_trans (hC x hx) (by linarith)
    simp only [survives_M, survives_R]
    exact ⟨fun _ => hxr, fun _ => Or.inl (hC x hx)⟩
  · rw [act_M_of_lt lam x (hC x hx), act_R]

/-- If every knot of `C` lies above `1 - r/2`, then `M` acts on `C` exactly as
`L` does (paper Lemma `lem:free`, the easy direction). -/
theorem actsAs_M_L_of_forall_gt (h : 1 < lam) {C : Finset ℝ}
    (hC : ∀ x ∈ C, 1 - r lam / 2 < x) : ActsAs lam Move.M Move.L C := by
  have hr0 : 0 < r lam := r_pos lam h
  refine ⟨fun x hx => ?_, fun x hx _ => ?_⟩
  · have hxg : g lam < x := by
      have := hC x hx
      simp only [g]
      linarith
    simp only [survives_M, survives_L]
    exact ⟨fun _ => hxg, fun _ => Or.inr (hC x hx)⟩
  · have hnot : ¬ x < r lam / 2 := by
      have := hC x hx
      have := r_lt_one lam h
      push_neg
      linarith
    rw [act_M_of_gt lam x hnot, act_L]

/-- The converse for `R`, valid for `λ < 3/2`.  (For `λ ≥ 3/2` it is false; see
`actsAs_M_R_converse_fails`.) -/
theorem forall_lt_of_actsAs_M_R (h : 1 < lam) (h32 : lam < 3/2) {C : Finset ℝ}
    (hC : ActsAs lam Move.M Move.R C) : ∀ x ∈ C, x < r lam / 2 := by
  have hlam : (0:ℝ) < lam := lt_trans zero_lt_one h
  have hlr : lam * r lam = 1 := lam_mul_r h
  -- `λ < 3/2` says exactly `1 - r/2 < r`
  have hkey : 1 - r lam / 2 < r lam := by
    nlinarith [r_pos lam h]
  intro x hx
  by_contra hxr
  push_neg at hxr
  by_cases hsm : survives lam Move.M x
  · -- `x` survives `M`, hence lies above `1 - r/2`, and the two images differ
    have hup : 1 - r lam / 2 < x := by
      rcases hsm with hs | hs
      · exact absurd hs (not_lt.mpr hxr)
      · exact hs
    have heq := hC.2 x hx hsm
    rw [act_M_of_gt lam x (not_lt.mpr hxr), act_R] at heq
    linarith
  · -- `x` is deleted by `M`, hence also by `R`, which is impossible for `λ < 3/2`
    have hsr : ¬ survives lam Move.R x := fun hr => hsm ((hC.1 x hx).mpr hr)
    simp only [survives_R, not_lt] at hsr
    simp only [survives_M, not_or, not_lt] at hsm
    linarith [hsm.2]

/-- The converse for `L`, valid for `λ < 3/2`. -/
theorem forall_gt_of_actsAs_M_L (h : 1 < lam) (h32 : lam < 3/2) {C : Finset ℝ}
    (hC : ActsAs lam Move.M Move.L C) : ∀ x ∈ C, 1 - r lam / 2 < x := by
  have hlam : (0:ℝ) < lam := lt_trans zero_lt_one h
  have hlr : lam * r lam = 1 := lam_mul_r h
  have hkey : 1 - r lam / 2 < r lam := by
    nlinarith [r_pos lam h]
  intro x hx
  by_contra hxr
  push_neg at hxr
  by_cases hsm : survives lam Move.M x
  · have hlo : x < r lam / 2 := by
      rcases hsm with hs | hs
      · exact hs
      · exact absurd hs (not_lt.mpr hxr)
    have heq := hC.2 x hx hsm
    rw [act_M_of_lt lam x hlo, act_L] at heq
    linarith
  · have hsl : ¬ survives lam Move.L x := fun hl => hsm ((hC.1 x hx).mpr hl)
    simp only [survives_L, not_lt] at hsl
    simp only [survives_M, not_or, not_lt] at hsm
    simp only [g] at hsl
    linarith [hsm.1]

/-- **T19(b)** (paper Lemma `lem:free`), for `R`.  For `1 < λ < 3/2`, an `M`
acts on `C` exactly as `R` does precisely when every knot of `C` lies below
`r/2`. -/
theorem actsAs_M_R_iff (h : 1 < lam) (h32 : lam < 3/2) (C : Finset ℝ) :
    ActsAs lam Move.M Move.R C ↔ ∀ x ∈ C, x < r lam / 2 :=
  ⟨forall_lt_of_actsAs_M_R h h32, actsAs_M_R_of_forall_lt h⟩

/-- **T19(b)** (paper Lemma `lem:free`), for `L`.  For `1 < λ < 3/2`, an `M`
acts on `C` exactly as `L` does precisely when every knot of `C` lies above
`1 - r/2`. -/
theorem actsAs_M_L_iff (h : 1 < lam) (h32 : lam < 3/2) (C : Finset ℝ) :
    ActsAs lam Move.M Move.L C ↔ ∀ x ∈ C, 1 - r lam / 2 < x :=
  ⟨forall_gt_of_actsAs_M_L h h32, actsAs_M_L_of_forall_gt h⟩

/-- **The restriction `λ < 3/2` in `lem:free` is necessary.**  For `λ ≥ 3/2`
one has `r ≤ 1 - r/2`, so the single knot at `r` is deleted by `M` and by `R`
alike; `M` then acts on `{r}` exactly as `R` does although `r ≥ r/2`.  (The
knot sits in `(0,1)`, so this is a legitimate configuration.) -/
theorem actsAs_M_R_converse_fails (h : 1 < lam) (h32 : 3/2 ≤ lam) :
    ActsAs lam Move.M Move.R {r lam} ∧ 0 < r lam ∧ r lam < 1 ∧
      ¬ (∀ x ∈ ({r lam} : Finset ℝ), x < r lam / 2) := by
  have hr0 : 0 < r lam := r_pos lam h
  have hr1 : r lam < 1 := r_lt_one lam h
  have hlam : (0:ℝ) < lam := lt_trans zero_lt_one h
  have hlr : lam * r lam = 1 := lam_mul_r h
  -- `3/2 ≤ λ` says exactly `r ≤ 1 - r/2`
  have hkey : r lam ≤ 1 - r lam / 2 := by nlinarith
  have hnotM : ¬ survives lam Move.M (r lam) := by
    simp only [survives_M, not_or, not_lt]
    exact ⟨by linarith, hkey⟩
  have hnotR : ¬ survives lam Move.R (r lam) := by
    simp only [survives_R, not_lt]
    exact le_refl _
  refine ⟨⟨fun x hx => ?_, fun x hx hs => ?_⟩, hr0, hr1, ?_⟩
  · rw [Finset.mem_singleton.mp hx]
    exact ⟨fun hs => absurd hs hnotM, fun hs => absurd hs hnotR⟩
  · rw [Finset.mem_singleton.mp hx] at hs
    exact absurd hs hnotM
  · intro hall
    have := hall (r lam) (Finset.mem_singleton_self _)
    linarith

/-- **A free `M` is a free birth.**  If `M` acts on `C` exactly as `m'` does,
then the configuration after the `M` is the configuration after `m'` together
with the newborn knot at `1/2`. -/
theorem step_M_eq_of_actsAs {m' : Move} {C : Finset ℝ} (hm' : m' ≠ Move.M)
    (hC : ActsAs lam Move.M m' C) :
    step lam Move.M C = step lam m' C ∪ {(1:ℝ)/2} := by
  classical
  have hfil : survivors lam Move.M C = survivors lam m' C :=
    Finset.filter_congr (fun x hx => by simpa using hC.1 x hx)
  have himg : (survivors lam Move.M C).image (act lam Move.M)
      = (survivors lam m' C).image (act lam m') := by
    rw [← hfil]
    refine Finset.image_congr (fun x hx => ?_)
    have hx' : x ∈ survivors lam Move.M C := hx
    rw [survivors, Finset.mem_filter] at hx'
    exact hC.2 x hx'.1 hx'.2
  rw [step_M, himg, step, if_neg hm']
  simp

end KnotGame
