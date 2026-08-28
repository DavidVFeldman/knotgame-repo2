import RequestProject.Threshold

/-!
# Theorem 3.1: Pisot finiteness (Work Order 7)

If `lam` is a Pisot number then the forward orbit of `1/2` under the surviving
branches is finite.

The route: every orbit point `x` satisfies `2x ∈ 𝒪_K`; the conjugate maps
`y ↦ σ(λ)y` and `y ↦ σ(λ)y - 2(σ(λ)-1)` (acting on `y = 2x`) are contractions
with fixed points `0` and `2`, so all conjugates of `2x` are bounded uniformly
in the branch sequence; and `0 < x < 1`.
-/

namespace KnotGame

open IntermediateField

variable {lam : ℝ}

/-- A **Pisot number**: a real number `> 1` which is a root of a monic integer
polynomial all of whose other complex roots have modulus `< 1`.  (Taking the
polynomial to be the minimal polynomial shows this is the usual definition.) -/
def IsPisot (lam : ℝ) : Prop :=
  1 < lam ∧ ∃ p : Polynomial ℤ, p.Monic ∧ Polynomial.aeval lam p = 0 ∧
    ∀ z : ℂ, Polynomial.aeval z p = 0 → z ≠ (lam : ℂ) → ‖z‖ < 1

/-- The forward orbit of `1/2` along surviving branches. -/
def Orb (lam : ℝ) : Set ℝ :=
  {x | ∃ w : List Move, survivesWord lam (1/2) w ∧ posAfter lam (1/2) w = x}

/-! ### Knots stay in the open unit interval -/

lemma act_mem_Ioo (h : 1 < lam) {x : ℝ} (hx : x ∈ Set.Ioo (0:ℝ) 1) {m : Move}
    (hs : survives lam m x) : act lam m x ∈ Set.Ioo (0:ℝ) 1 := by
  obtain ⟨hx0, hx1⟩ := hx
  have hlam : (0:ℝ) < lam := lt_trans zero_lt_one h
  have hr : lam * r lam = 1 := lam_mul_r h
  have hg : lam * g lam = lam - 1 := lam_mul_g h
  have hr1 : r lam < 1 := r_lt_one lam h
  have hr0 : 0 < r lam := r_pos lam h
  cases m
  · have hgx : g lam < x := hs
    rw [act_L]
    constructor
    · nlinarith
    · nlinarith
  · rcases hs with hs | hs
    · rw [act_M_of_lt lam x hs]
      constructor
      · nlinarith
      · nlinarith
    · rw [act_M_of_gt lam x (by push_neg; linarith)]
      constructor
      · have : 1 - r lam / 2 < x := hs
        nlinarith
      · nlinarith
  · have hxr : x < r lam := hs
    rw [act_R]
    constructor
    · nlinarith
    · nlinarith

lemma posAfter_mem_Ioo (h : 1 < lam) {x : ℝ} (hx : x ∈ Set.Ioo (0:ℝ) 1) (w : List Move)
    (hs : survivesWord lam x w) : posAfter lam x w ∈ Set.Ioo (0:ℝ) 1 := by
  induction w generalizing x with
  | nil => simpa using hx
  | cons m w ih =>
      rw [survivesWord_cons] at hs
      exact ih (act_mem_Ioo h hx hs.1) hs.2

lemma orb_subset_Ioo (h : 1 < lam) : Orb lam ⊆ Set.Ioo (0:ℝ) 1 := by
  rintro x ⟨w, hs, rfl⟩
  exact posAfter_mem_Ioo h (by norm_num) w hs

/-! ### The orbit as a set of branch words -/

/-- The composite of branch maps along an itinerary. -/
noncomputable def branchIter (lam : ℝ) : List (Fin 2) → ℝ → ℝ
  | [], x => x
  | e :: es, x => branchIter lam es (f lam e x)

/-- The branch itinerary followed by a knot along a word of moves. -/
noncomputable def branchesOf (lam : ℝ) : ℝ → List Move → List (Fin 2)
  | _, [] => []
  | x, m :: w => branch lam m x :: branchesOf lam (act lam m x) w

lemma posAfter_eq_branchIter (x : ℝ) (w : List Move) :
    posAfter lam x w = branchIter lam (branchesOf lam x w) x := by
  induction w generalizing x with
  | nil => rfl
  | cons m w ih => simpa [branchIter, branchesOf, act] using ih (act lam m x)

lemma orb_subset (h : 1 < lam) :
    Orb lam ⊆ {x | (∃ w : List (Fin 2), branchIter lam w (1/2) = x) ∧ x ∈ Set.Ioo (0:ℝ) 1} := by
  rintro x hx
  refine ⟨?_, orb_subset_Ioo h hx⟩
  obtain ⟨w, hs, rfl⟩ := hx
  exact ⟨branchesOf lam (1/2) w, (posAfter_eq_branchIter (1/2) w).symm⟩

/-! ### The doubled orbit in an arbitrary ring -/

/-- The composite of branch maps along an itinerary, in a general ring, with the
branch maps `y ↦ c*y` and `y ↦ c*y - 2*(c-1)` — these are the maps induced on
`y = 2x` by `f₀` and `f₁`. -/
def iterC {R : Type*} [Ring R] (c : R) : List (Fin 2) → R → R
  | [], y => y
  | e :: es, y => iterC c es (if e = 0 then c * y else c * y - 2 * (c - 1))

lemma two_mul_branchIter (w : List (Fin 2)) (x : ℝ) :
    2 * branchIter lam w x = iterC lam w (2 * x) := by
  induction w generalizing x with
  | nil => rfl
  | cons e es ih =>
      rw [branchIter, iterC, ih]
      congr 1
      rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl
      · simp [f]; ring
      · simp [f]; ring

lemma map_iterC {R S : Type*} [Ring R] [Ring S] (ψ : R →+* S) (c : R) (w : List (Fin 2))
    (y : R) : ψ (iterC c w y) = iterC (ψ c) w (ψ y) := by
  induction w generalizing y with
  | nil => rfl
  | cons e es ih =>
      rw [iterC, iterC, ih]
      congr 1
      rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl
      · simp
      · simp [map_ofNat]

lemma isIntegral_iterC {R : Type*} [CommRing R] [Algebra ℤ R] {c : R} (hc : IsIntegral ℤ c)
    (w : List (Fin 2)) {y : R} (hy : IsIntegral ℤ y) : IsIntegral ℤ (iterC c w y) := by
  induction w generalizing y with
  | nil => exact hy
  | cons e es ih =>
      apply ih
      have h2 : IsIntegral ℤ ((2 : R)) := by
        simpa using (isIntegral_algebraMap (x := (2:ℤ)) (R := ℤ) (A := R))
      rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl
      · simpa using hc.mul hy
      · rw [if_neg (by decide : ¬ ((1 : Fin 2) = 0))]
        exact (hc.mul hy).sub (h2.mul (hc.sub (isIntegral_one)))

/-- **The uniform bound on the conjugates.**  If `‖c‖ < 1` then the orbit of `1`
under the two contractions is bounded, uniformly in the branch sequence. -/
lemma conj_bound {c : ℂ} (hc : ‖c‖ < 1) (w : List (Fin 2)) :
    ‖iterC c w 1‖ ≤ (2 + 2 * ‖c‖) / (1 - ‖c‖) := by
  set t := ‖c‖ with ht
  have ht0 : 0 ≤ t := norm_nonneg c
  have hden : 0 < 1 - t := by linarith
  set B := (2 + 2 * t) / (1 - t) with hB
  have hB2 : 2 ≤ B := by
    rw [hB, le_div_iff₀ hden]
    linarith
  have hBt : t * B + 2 * (t + 1) = B := by
    rw [hB]
    field_simp
    ring
  have key : ∀ (w : List (Fin 2)) (y : ℂ), ‖y‖ ≤ B → ‖iterC c w y‖ ≤ B := by
    intro w
    induction w with
    | nil => intro y hy; exact hy
    | cons e es ih =>
        intro y hy
        apply ih
        rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl
        · rw [if_pos rfl, norm_mul, ← ht]
          nlinarith [norm_nonneg y]
        · rw [if_neg (by decide : ¬ ((1 : Fin 2) = 0))]
          have h1 : ‖c * y - 2 * (c - 1)‖ ≤ ‖c * y‖ + ‖2 * (c - 1)‖ := norm_sub_le _ _
          have h2 : ‖c * y‖ = t * ‖y‖ := by rw [norm_mul, ht]
          have h3 : ‖(2 : ℂ) * (c - 1)‖ ≤ 2 * (t + 1) := by
            rw [norm_mul]
            have hcl : ‖c - 1‖ ≤ t + 1 := by
              refine le_trans (norm_sub_le c 1) ?_
              simp [ht]
            have h2n : ‖(2:ℂ)‖ = 2 := by norm_num
            rw [h2n]
            linarith
          nlinarith [norm_nonneg y]
  exact key w 1 (by simpa using le_trans one_le_two hB2)

/-- **Theorem 3.1.** For a Pisot number the orbit of `1/2` is finite. -/
theorem orb_finite (h : IsPisot lam) : (Orb lam).Finite := by
  obtain ⟨h1, p, hmonic, hroot, hconj⟩ := h
  have hint : IsIntegral ℤ lam := ⟨p, hmonic, hroot⟩
  have hQ : IsIntegral ℚ lam := hint.tower_top
  set K := (ℚ⟮lam⟯ : IntermediateField ℚ ℝ) with hK
  haveI : FiniteDimensional ℚ K := IntermediateField.adjoin.finiteDimensional hQ
  haveI : NumberField K := ⟨⟩
  set co : K →+* ℝ := (IntermediateField.val K).toRingHom with hco
  have hcoinj : Function.Injective co := (IntermediateField.val K).injective
  set lamK : K := ⟨lam, IntermediateField.mem_adjoin_simple_self ℚ lam⟩ with hlamK
  have hcolam : co lamK = lam := rfl
  -- `lamK` is a root of `p`
  have hrootK : Polynomial.aeval lamK p = 0 := by
    apply hcoinj
    have := Polynomial.aeval_algHom_apply (co.toIntAlgHom) lamK p
    simp only [RingHom.toIntAlgHom_coe] at this
    rw [map_zero, ← this, hcolam, hroot]
  have hintK : IsIntegral ℤ lamK := ⟨p, hmonic, hrootK⟩
  -- the uniform bound
  have hne : (Finset.univ : Finset (K →+* ℂ)).Nonempty := by
    refine ⟨(Complex.ofRealHom).comp co, Finset.mem_univ _⟩
  set B : ℝ := max 2 (Finset.univ.sup' hne
    (fun ψ : K →+* ℂ => (2 + 2 * ‖ψ lamK‖) / (1 - ‖ψ lamK‖))) with hB
  -- the finite ambient set
  have hfin : {z : K | IsIntegral ℤ z ∧ ∀ ψ : K →+* ℂ, ‖ψ z‖ ≤ B}.Finite :=
    NumberField.Embeddings.finite_of_norm_le K ℂ B
  have hfinA : {y : K | IsIntegral ℤ (2 * y) ∧ ∀ ψ : K →+* ℂ, ‖ψ (2 * y)‖ ≤ B}.Finite := by
    have hpre : {y : K | IsIntegral ℤ (2 * y) ∧ ∀ ψ : K →+* ℂ, ‖ψ (2 * y)‖ ≤ B}
        = (fun y : K => 2 * y) ⁻¹' {z : K | IsIntegral ℤ z ∧ ∀ ψ : K →+* ℂ, ‖ψ z‖ ≤ B} := rfl
    rw [hpre]
    refine Set.Finite.preimage ?_ hfin
    intro a _ b _ hab
    exact mul_left_cancel₀ (two_ne_zero) hab
  refine Set.Finite.subset (hfinA.image (fun y : K => co y)) ?_
  rintro x hx
  obtain ⟨⟨w, hw⟩, hx0, hx1⟩ := orb_subset h1 hx
  refine ⟨(iterC lamK w 1) / 2, ⟨?_, ?_⟩, ?_⟩
  · -- integrality
    have h2 : (2 : K) * ((iterC lamK w 1) / 2) = iterC lamK w 1 := by
      field_simp
    rw [h2]
    exact isIntegral_iterC hintK w isIntegral_one
  · -- the bound on every embedding
    intro ψ
    have h2 : (2 : K) * ((iterC lamK w 1) / 2) = iterC lamK w 1 := by field_simp
    rw [h2, map_iterC ψ lamK w 1, map_one]
    by_cases hcase : ψ lamK = (lam : ℂ)
    · -- the identity embedding: use `0 < x < 1`
      rw [hcase]
      have hmap : iterC ((lam : ℝ) : ℂ) w (1 : ℂ) = ((iterC lam w (1:ℝ) : ℝ) : ℂ) := by
        have hh := map_iterC (Complex.ofRealHom) lam w 1
        simpa using hh.symm
      have hval : iterC lam w (1:ℝ) = 2 * x := by
        have hh := two_mul_branchIter (lam := lam) w (1/2)
        rw [hw] at hh
        simp only [show (2:ℝ) * (1/2) = 1 by norm_num] at hh
        exact hh.symm
      rw [show ((lam : ℝ) : ℂ) = (lam : ℂ) from rfl] at hmap
      rw [hmap, hval]
      have : ‖((2 * x : ℝ) : ℂ)‖ = |2 * x| := by simp
      rw [this]
      have : |2 * x| ≤ 2 := by
        rw [abs_of_pos (by linarith)]
        linarith
      exact le_trans this (le_max_left _ _)
    · -- a conjugate embedding: contraction
      have hrootc : Polynomial.aeval (ψ lamK) p = 0 := by
        have := Polynomial.aeval_algHom_apply (ψ.toIntAlgHom) lamK p
        simp only [RingHom.toIntAlgHom_coe] at this
        rw [this, hrootK, map_zero]
      have hlt : ‖ψ lamK‖ < 1 := hconj _ hrootc hcase
      refine le_trans (conj_bound hlt w) ?_
      refine le_trans (Finset.le_sup' (f := fun ψ : K →+* ℂ =>
        (2 + 2 * ‖ψ lamK‖) / (1 - ‖ψ lamK‖)) (Finset.mem_univ ψ)) (le_max_right _ _)
  · -- the point itself
    have hmap : co (iterC lamK w 1) = iterC lam w (1:ℝ) := by
      rw [map_iterC co lamK w 1, hcolam, map_one]
    have hval : iterC lam w (1:ℝ) = 2 * x := by
      have hh := two_mul_branchIter (lam := lam) w (1/2)
      rw [hw] at hh
      simp only [show (2:ℝ) * (1/2) = 1 by norm_num] at hh
      exact hh.symm
    show co (iterC lamK w 1 / 2) = x
    rw [map_div₀, hmap, hval, map_ofNat]
    ring

end KnotGame
