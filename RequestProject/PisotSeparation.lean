import RequestProject.Pisot

/-!
# Round 16, T46: the Pisot separation bound

`Pisot.orb_finite` proves that the orbit `Orb lam` of `1/2` along surviving
branches is finite when `lam` is Pisot, by a discreteness argument that gives no
quantitative information.  This module makes it quantitative.

For distinct `x, y ∈ Orb lam` the number `2*(x - y)` is a nonzero algebraic
integer of `ℚ⟮lam⟯`; the round-14 estimate `conj_bound` bounds every conjugate
of `2*x` by `B = (2 + 2*c)/(1 - c)`, where `c` bounds the moduli of the
conjugates of `lam`; and the field norm of a nonzero algebraic integer is a
nonzero rational integer, hence at least `1` in absolute value.  Writing the
norm as the product of the `d = [ℚ⟮lam⟯ : ℚ]` complex embeddings and isolating
the real one gives

`1 ≤ 2*|x - y| * (2*B)^(d-1)`,

that is, the orbit is `1 / (2 * (2*B)^(d-1))`-separated (`orb_separated_of_conj_le`).
A `δ`-separated subset of `(0,1)` has at most `1/δ + 1` elements, so the orbit
also has an explicit cardinality bound (`orb_ncard_le_of_conj_le`), which
strengthens `orb_finite` from finiteness to a count.

The constant depends only on `lam` — through a bound `c < 1` on the moduli of
the conjugates and through the degree — and not on the orbit, on the points, or
on the length of the branch words.
-/

namespace KnotGame

open IntermediateField

/-! ### The norm step in a number field -/

/-- The product of the moduli of all complex embeddings of a nonzero algebraic
integer is at least `1`: it is the absolute value of the field norm, a nonzero
rational integer. -/
theorem one_le_prod_norm_embeddings {K : Type*} [Field K] [NumberField K] {a : K}
    (ha : a ≠ 0) (hint : IsIntegral ℤ a) :
    1 ≤ ∏ ψ : K →+* ℂ, ‖ψ a‖ := by
  classical
  have hnorm : IsIntegral ℤ (Algebra.norm ℚ a) := Algebra.isIntegral_norm ℚ hint
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hnorm
  have hne : Algebra.norm ℚ a ≠ 0 := Algebra.norm_ne_zero_iff.mpr ha
  have hn0 : n ≠ 0 := by
    rintro rfl; simp at hn; exact hne hn.symm
  have h1 : (1:ℝ) ≤ |(n : ℝ)| := by
    have h := (Int.cast_le (R := ℝ)).mpr (Int.one_le_abs hn0)
    rwa [Int.cast_abs, Int.cast_one] at h
  have key := congr_arg (fun z : ℂ => ‖z‖) (Algebra.norm_eq_prod_embeddings (L := K) ℚ ℂ a)
  simp only [norm_prod] at key
  rw [Fintype.prod_equiv RingHom.equivRatAlgHom (fun f : K →+* ℂ => ‖f a‖)
      (fun psi : K →ₐ[ℚ] ℂ => ‖psi a‖) (fun _ => by simp [RingHom.equivRatAlgHom_apply]),
    ← key, ← hn]
  simp only [eq_ratCast, Complex.norm_ratCast]
  simpa using h1

/-- If every embedding other than a distinguished one `φ` sends the nonzero
algebraic integer `a` into the disc of radius `C`, then `‖φ a‖` is bounded below
by `C^(1-d)`, with `d` the degree. -/
theorem one_le_norm_mul_pow {K : Type*} [Field K] [NumberField K] {a : K}
    (ha : a ≠ 0) (hint : IsIntegral ℤ a) (φ : K →+* ℂ) {C : ℝ}
    (hC : ∀ ψ : K →+* ℂ, ‖ψ a‖ ≤ C) :
    1 ≤ ‖φ a‖ * C ^ (Module.finrank ℚ K - 1) := by
  classical
  have hmem : φ ∈ (Finset.univ : Finset (K →+* ℂ)) := Finset.mem_univ _
  have hsplit := Finset.mul_prod_erase Finset.univ (fun ψ : K →+* ℂ => ‖ψ a‖) hmem
  have hb : ∏ ψ ∈ Finset.univ.erase φ, ‖ψ a‖ ≤ C ^ (Finset.univ.erase φ).card := by
    calc ∏ ψ ∈ Finset.univ.erase φ, ‖ψ a‖ ≤ ∏ _ψ ∈ Finset.univ.erase φ, C :=
          Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hC i)
      _ = C ^ (Finset.univ.erase φ).card := by rw [Finset.prod_const]
  have hcard : (Finset.univ.erase φ).card = Module.finrank ℚ K - 1 := by
    rw [Finset.card_erase_of_mem hmem, Finset.card_univ, NumberField.Embeddings.card K ℂ]
  have h1 := one_le_prod_norm_embeddings ha hint
  rw [← hsplit] at h1
  calc (1:ℝ) ≤ ‖φ a‖ * ∏ ψ ∈ Finset.univ.erase φ, ‖ψ a‖ := h1
    _ ≤ ‖φ a‖ * C ^ (Module.finrank ℚ K - 1) := by
        rw [← hcard]
        exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)

/-! ### Separated subsets of the unit interval -/

/-- A `δ`-separated subset of `(0,1)` is finite with at most `⌊1/δ⌋ + 1`
elements. -/
theorem finite_ncard_le_of_separated {S : Set ℝ} {delta : ℝ} (hd : 0 < delta)
    (hS : S ⊆ Set.Ioo (0:ℝ) 1)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → delta ≤ |x - y|) :
    S.Finite ∧ S.ncard ≤ ⌊1 / delta⌋₊ + 1 := by
  classical
  set N : ℕ := ⌊1 / delta⌋₊ with hN
  set F : ℝ → ℕ := fun x => ⌊x / delta⌋₊ with hF
  have hmaps : ∀ x ∈ S, F x ∈ Set.Iic N := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := hS hx
    have hle : x / delta ≤ 1 / delta := by gcongr
    exact Nat.floor_le_floor hle
  have hinj : Set.InjOn F S := by
    intro x hx y hy hxy
    by_contra hne
    obtain ⟨hx0, -⟩ := hS hx
    obtain ⟨hy0, -⟩ := hS hy
    have hax : ((F x : ℝ)) ≤ x / delta := Nat.floor_le (div_pos hx0 hd).le
    have hay : ((F y : ℝ)) ≤ y / delta := Nat.floor_le (div_pos hy0 hd).le
    have hbx : x / delta < (F x : ℝ) + 1 := Nat.lt_floor_add_one _
    have hby : y / delta < (F y : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [hxy] at hax hbx
    have hlt : |x / delta - y / delta| < 1 := by
      rw [abs_lt]; constructor <;> linarith
    have hlt2 : |x - y| < delta := by
      have hxy' : x - y = delta * (x / delta - y / delta) := by field_simp
      rw [hxy', abs_mul, abs_of_pos hd]
      nlinarith [abs_nonneg (x / delta - y / delta)]
    exact absurd (hsep x hx y hy hne) (not_le.mpr hlt2)
  have hcard : (Set.Iic N).ncard = N + 1 := by simp [Set.ncard_eq_toFinset_card']
  refine ⟨?_, ?_⟩
  · have himg : (F '' S).Finite :=
      Set.Finite.subset (Set.finite_Iic N) (by rintro _ ⟨x, hx, rfl⟩; exact hmaps x hx)
    exact Set.Finite.of_finite_image himg hinj
  · have h := Set.ncard_le_ncard_of_injOn F hmaps hinj (Set.finite_Iic N)
    rwa [hcard] at h

/-! ### The doubled orbit -/

variable {lam : ℝ}

/-- Every orbit point is `1/2` times a value of the doubled branch iteration
started at `1`. -/
lemma exists_iterC_eq_two_mul (h1 : 1 < lam) {x : ℝ} (hx : x ∈ Orb lam) :
    ∃ w : List (Fin 2), iterC lam w (1:ℝ) = 2 * x := by
  obtain ⟨⟨w, hw⟩, -⟩ := orb_subset h1 hx
  refine ⟨w, ?_⟩
  have h := two_mul_branchIter (lam := lam) w (1/2)
  rw [hw] at h
  simpa using h.symm

/-! ### The separation bound -/

/-- **T46(a), the separation estimate.**  With `c` a bound `< 1` on the moduli
of the conjugates of the algebraic integer `lam` and `B = (2 + 2c)/(1 - c)`,
distinct points of the orbit are at distance at least `1 / (2 * (2B)^(d-1))`,
where `d = [ℚ⟮lam⟯ : ℚ]`. -/
theorem orb_separated_of_conj_le (h1 : 1 < lam) {p : Polynomial ℤ} (hmonic : p.Monic)
    (hroot : Polynomial.aeval lam p = 0) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hconj : ∀ z : ℂ, Polynomial.aeval z p = 0 → z ≠ (lam : ℂ) → ‖z‖ ≤ c)
    {x y : ℝ} (hx : x ∈ Orb lam) (hy : y ∈ Orb lam) (hxy : x ≠ y) :
    1 / (2 * (2 * ((2 + 2 * c) / (1 - c))) ^
        (Module.finrank ℚ (ℚ⟮lam⟯ : IntermediateField ℚ ℝ) - 1)) ≤ |x - y| := by
  classical
  have hc1' : (0:ℝ) < 1 - c := by linarith
  set B : ℝ := (2 + 2 * c) / (1 - c) with hB
  have hB2 : (2:ℝ) ≤ B := by
    rw [hB, le_div_iff₀ hc1']; linarith
  have hint : IsIntegral ℤ lam := ⟨p, hmonic, hroot⟩
  have hQ : IsIntegral ℚ lam := hint.tower_top
  set K := (ℚ⟮lam⟯ : IntermediateField ℚ ℝ) with hK
  haveI : FiniteDimensional ℚ K := IntermediateField.adjoin.finiteDimensional hQ
  haveI : NumberField K := ⟨⟩
  set co : K →+* ℝ := (IntermediateField.val K).toRingHom with hco
  set lamK : K := ⟨lam, IntermediateField.mem_adjoin_simple_self ℚ lam⟩ with hlamK
  have hcolam : co lamK = lam := rfl
  have hrootK : Polynomial.aeval lamK p = 0 := by
    apply (IntermediateField.val K).injective
    have h := Polynomial.aeval_algHom_apply (co.toIntAlgHom) lamK p
    simp only [RingHom.toIntAlgHom_coe] at h
    rw [map_zero, ← h, hcolam, hroot]
  have hintK : IsIntegral ℤ lamK := ⟨p, hmonic, hrootK⟩
  obtain ⟨hx0, hx1⟩ := orb_subset_Ioo h1 hx
  obtain ⟨hy0, hy1⟩ := orb_subset_Ioo h1 hy
  obtain ⟨w, hw⟩ := exists_iterC_eq_two_mul h1 hx
  obtain ⟨w', hw'⟩ := exists_iterC_eq_two_mul h1 hy
  set a : K := iterC lamK w 1 - iterC lamK w' 1 with ha
  have hcoa : co a = 2 * x - 2 * y := by
    rw [ha, map_sub, map_iterC co lamK w 1, map_iterC co lamK w' 1, hcolam, map_one, hw, hw']
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hcoa
    exact hxy (by linarith)
  have haint : IsIntegral ℤ a :=
    (isIntegral_iterC hintK w isIntegral_one).sub (isIntegral_iterC hintK w' isIntegral_one)
  set emb : K →+* ℂ := (Complex.ofRealHom).comp co with hemb
  have hnormemb : ‖emb a‖ = 2 * |x - y| := by
    have hval : emb a = ((co a : ℝ) : ℂ) := rfl
    rw [hval, hcoa, Complex.norm_real, Real.norm_eq_abs,
      show (2 * x - 2 * y) = 2 * (x - y) by ring, abs_mul]
    norm_num
  have hall : ∀ ψ : K →+* ℂ, ‖ψ a‖ ≤ 2 * B := by
    intro ψ
    have hpsi : ψ a = iterC (ψ lamK) w 1 - iterC (ψ lamK) w' 1 := by
      rw [ha, map_sub, map_iterC ψ lamK w 1, map_iterC ψ lamK w' 1, map_one]
    by_cases hcase : ψ lamK = (lam : ℂ)
    · have hreal : ∀ v : List (Fin 2), iterC ((lam : ℝ) : ℂ) v (1 : ℂ)
          = ((iterC lam v (1:ℝ) : ℝ) : ℂ) := by
        intro v
        simpa using (map_iterC (Complex.ofRealHom) lam v 1).symm
      rw [hpsi, hcase, hreal w, hreal w', hw, hw', ← Complex.ofReal_sub]
      have h2 : |2 * x - 2 * y| ≤ 2 := by
        rw [abs_le]; constructor <;> linarith
      have h3 : ‖((2 * x - 2 * y : ℝ) : ℂ)‖ = |2 * x - 2 * y| := by
        rw [Complex.norm_real, Real.norm_eq_abs]
      rw [h3]
      linarith
    · have hrootc : Polynomial.aeval (ψ lamK) p = 0 := by
        have h := Polynomial.aeval_algHom_apply (ψ.toIntAlgHom) lamK p
        simp only [RingHom.toIntAlgHom_coe] at h
        rw [h, hrootK, map_zero]
      have hle : ‖ψ lamK‖ ≤ c := hconj _ hrootc hcase
      have hlt : ‖ψ lamK‖ < 1 := lt_of_le_of_lt hle hc1
      have hmono : (2 + 2 * ‖ψ lamK‖) / (1 - ‖ψ lamK‖) ≤ B := by
        rw [hB, div_le_div_iff₀ (by linarith) hc1']
        nlinarith [norm_nonneg (ψ lamK)]
      have hb1 : ‖iterC (ψ lamK) w 1‖ ≤ B := le_trans (conj_bound hlt w) hmono
      have hb2 : ‖iterC (ψ lamK) w' 1‖ ≤ B := le_trans (conj_bound hlt w') hmono
      rw [hpsi]
      calc ‖iterC (ψ lamK) w 1 - iterC (ψ lamK) w' 1‖
          ≤ ‖iterC (ψ lamK) w 1‖ + ‖iterC (ψ lamK) w' 1‖ := norm_sub_le _ _
        _ ≤ 2 * B := by linarith
  have hkey := one_le_norm_mul_pow ha0 haint emb hall
  rw [hnormemb] at hkey
  have hpos : (0:ℝ) < 2 * (2 * B) ^ (Module.finrank ℚ K - 1) := by
    have h2B : (0:ℝ) < 2 * B := by linarith
    positivity
  rw [div_le_iff₀ hpos]
  nlinarith [hkey]

/-- **T46(b), the cardinality bound.**  The orbit is finite with an explicit
bound on its size in terms of the same constant. -/
theorem orb_ncard_le_of_conj_le (h1 : 1 < lam) {p : Polynomial ℤ} (hmonic : p.Monic)
    (hroot : Polynomial.aeval lam p = 0) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hconj : ∀ z : ℂ, Polynomial.aeval z p = 0 → z ≠ (lam : ℂ) → ‖z‖ ≤ c) :
    (Orb lam).Finite ∧ (Orb lam).ncard ≤
      ⌊2 * (2 * ((2 + 2 * c) / (1 - c))) ^
        (Module.finrank ℚ (ℚ⟮lam⟯ : IntermediateField ℚ ℝ) - 1)⌋₊ + 1 := by
  have hc1' : (0:ℝ) < 1 - c := by linarith
  set B : ℝ := (2 + 2 * c) / (1 - c) with hB
  have hB2 : (2:ℝ) ≤ B := by
    rw [hB, le_div_iff₀ hc1']; linarith
  set d : ℕ := Module.finrank ℚ (ℚ⟮lam⟯ : IntermediateField ℚ ℝ) with hd
  have h2B : (0:ℝ) < 2 * B := by linarith
  have hdelta : (0:ℝ) < 1 / (2 * (2 * B) ^ (d - 1)) := by positivity
  have hmain := finite_ncard_le_of_separated hdelta (orb_subset_Ioo h1)
    (fun x hx y hy hne => orb_separated_of_conj_le h1 hmonic hroot hc0 hc1 hconj hx hy hne)
  rwa [one_div_one_div] at hmain

/-- From `IsPisot` alone: a uniform bound `c < 1` on the moduli of the
conjugates exists, because the witnessing polynomial has finitely many roots. -/
lemma exists_conj_bound (h : IsPisot lam) :
    ∃ p : Polynomial ℤ, p.Monic ∧ Polynomial.aeval lam p = 0 ∧
      ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧
        ∀ z : ℂ, Polynomial.aeval z p = 0 → z ≠ (lam : ℂ) → ‖z‖ ≤ c := by
  classical
  obtain ⟨h1, p, hmonic, hroot, hconj⟩ := h
  refine ⟨p, hmonic, hroot, ?_⟩
  set q : Polynomial ℂ := p.map (algebraMap ℤ ℂ) with hq
  have hq0 : q ≠ 0 := (hmonic.map (algebraMap ℤ ℂ)).ne_zero
  have hev : ∀ z : ℂ, Polynomial.aeval z p = Polynomial.eval z q := by
    intro z
    rw [hq, Polynomial.eval_map, Polynomial.aeval_def]
  set S : Finset ℂ := q.roots.toFinset.filter (fun z => z ≠ (lam : ℂ)) with hS
  set T : Finset ℝ := insert (0:ℝ) (S.image (fun z => ‖z‖)) with hT
  have hTne : T.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  refine ⟨T.max' hTne, ?_, ?_, ?_⟩
  · exact T.le_max' 0 (Finset.mem_insert_self _ _)
  · rw [Finset.max'_lt_iff]
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb'
    · norm_num
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hb'
      obtain ⟨hzr, hzl⟩ := Finset.mem_filter.mp hz
      have hzroot : Polynomial.eval z q = 0 :=
        (Polynomial.mem_roots hq0).mp (Multiset.mem_toFinset.mp hzr)
      exact hconj z (by rw [hev z]; exact hzroot) hzl
  · intro z hz hzl
    have hzeval : Polynomial.eval z q = 0 := by rw [← hev z]; exact hz
    have hzq : z ∈ q.roots := (Polynomial.mem_roots hq0).mpr hzeval
    refine T.le_max' _ (Finset.mem_insert_of_mem ?_)
    exact Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hzq, hzl⟩, rfl⟩

/-- **T46 for a Pisot parameter.**  The orbit of `1/2` is uniformly separated
and its cardinality is bounded, by a constant of the commissioned shape
`1 / (2 * (2B)^(d-1))` with `B = (2 + 2c)/(1 - c)` a bound on the conjugates and
`d` the degree. -/
theorem orb_separated (h : IsPisot lam) :
    ∃ B : ℝ, 2 ≤ B ∧
      (∀ x ∈ Orb lam, ∀ y ∈ Orb lam, x ≠ y →
        1 / (2 * (2 * B) ^ (Module.finrank ℚ (ℚ⟮lam⟯ : IntermediateField ℚ ℝ) - 1))
          ≤ |x - y|) ∧
      (Orb lam).Finite ∧
      (Orb lam).ncard ≤
        ⌊2 * (2 * B) ^ (Module.finrank ℚ (ℚ⟮lam⟯ : IntermediateField ℚ ℝ) - 1)⌋₊ + 1 := by
  obtain ⟨p, hmonic, hroot, c, hc0, hc1, hconj⟩ := exists_conj_bound h
  have h1 : 1 < lam := h.1
  have hc1' : (0:ℝ) < 1 - c := by linarith
  refine ⟨(2 + 2 * c) / (1 - c), ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hc1']; linarith
  · exact fun x hx y hy hne => orb_separated_of_conj_le h1 hmonic hroot hc0 hc1 hconj hx hy hne
  · exact orb_ncard_le_of_conj_le h1 hmonic hroot hc0 hc1 hconj

end KnotGame
