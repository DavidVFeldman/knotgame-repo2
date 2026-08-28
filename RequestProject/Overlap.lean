import RequestProject.Pisot
import RequestProject.Golden
import RequestProject.Plastic

/-!
# The exact-overlap criterion (paper `lem:overlap`)

Lemma 11 of *Knot counts in an interval deletion game* (`lem:overlap`) says
that neither `1/√2` nor `2/3` is a root of a non-zero polynomial with
coefficients in `{0, ±1}`, while `1/φ` is a root of `x² + x − 1` and `1/ρ` is a
root of `x³ + x² − 1`.

The class of polynomials in question is `PMOne` below.  The two negative
statements are proved by one argument, which replaces the paper's two ad-hoc
computations (separating even and odd indices for `1/√2`, reduction modulo `2`
for `2/3`) by a single divisibility:

* a non-zero `PMOne` polynomial has leading coefficient `±1`, so it is
  *primitive* (`PMOne.isPrimitive`);
* if it vanishes at `u`, the minimal polynomial of `u` over `ℚ` divides it, so
  any primitive integer polynomial `m` whose rational image is a scalar multiple
  of that minimal polynomial divides it *in `ℤ[X]`* (Gauss's lemma, in the form
  `Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast`);
* hence the leading coefficient of `m` divides `±1`, which fails for
  `m = 2X² − 1` (at `u = 1/√2`) and for `m = 3X − 2` (at `u = 2/3`).

The consequence the paper draws from the lemma — that at `λ = 3/2` and
`λ = √2` distinct branch words of a common length carry a knot to distinct
positions, so that the number of reachable positions is the number of surviving
words — is `branchIter_injective_three_halves` and
`branchIter_injective_sqrt_two` at the end of the file.
-/

namespace KnotGame
namespace Overlap

open Polynomial

/-! ## The class of `{0, ±1}` polynomials -/

/-- A polynomial with integer coefficients all in `{−1, 0, 1}`. -/
def PMOne (p : Polynomial ℤ) : Prop :=
  ∀ i, p.coeff i = -1 ∨ p.coeff i = 0 ∨ p.coeff i = 1

/-- A non-zero `PMOne` polynomial has leading coefficient `1` or `−1`. -/
lemma PMOne.leadingCoeff_eq {p : Polynomial ℤ} (hp : PMOne p) (h0 : p ≠ 0) :
    p.leadingCoeff = 1 ∨ p.leadingCoeff = -1 := by
  have h := hp p.natDegree
  have hne : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr h0
  rw [Polynomial.leadingCoeff] at hne ⊢
  rcases h with h | h | h
  · exact Or.inr h
  · exact absurd h hne
  · exact Or.inl h

/-- A non-zero `PMOne` polynomial is primitive: its coefficients have no common
non-unit factor, since the leading one is `±1`. -/
lemma PMOne.isPrimitive {p : Polynomial ℤ} (hp : PMOne p) (h0 : p ≠ 0) : p.IsPrimitive := by
  intro s hs
  rw [C_dvd_iff_dvd_coeff] at hs
  have h := hs p.natDegree
  rcases hp.leadingCoeff_eq h0 with h1 | h1 <;>
    rw [Polynomial.leadingCoeff] at h1 <;> rw [h1] at h
  · exact isUnit_of_dvd_one h
  · exact (Int.isUnit_iff).2 (by
      rcases Int.isUnit_iff.1 (isUnit_of_dvd_one ((dvd_neg).1 h)) with h2 | h2 <;> simp [h2])

/-- Two monic polynomials, one dividing the other and of no smaller degree, are
equal. -/
lemma monic_eq_of_dvd {p q : Polynomial ℚ} (hp : p.Monic) (hq : q.Monic) (h : p ∣ q)
    (hd : q.natDegree ≤ p.natDegree) : p = q := by
  obtain ⟨k, hk⟩ := h
  have hk0 : k ≠ 0 := by rintro rfl; simp [hk] at hq
  have hdeg : q.natDegree = p.natDegree + k.natDegree := by
    rw [hk, Polynomial.natDegree_mul hp.ne_zero hk0]
  have hk1 : k.natDegree = 0 := by omega
  have hlead : (1:ℚ) = 1 * k.leadingCoeff := by
    have := hq.leadingCoeff
    rw [hk, Polynomial.leadingCoeff_mul, hp.leadingCoeff] at this
    exact this.symm
  have hkC := Polynomial.eq_C_of_natDegree_eq_zero hk1
  rw [hkC, Polynomial.leadingCoeff_C, one_mul] at hlead
  rw [hk, hkC, ← hlead, map_one, mul_one]

/-- **The divisibility argument.**  If a primitive integer polynomial `m` maps
to a non-zero scalar multiple of the minimal polynomial of `u`, and its leading
coefficient is not a unit, then no non-zero `PMOne` polynomial vanishes at `u`. -/
theorem not_root_of_primitive {u : ℝ} (m : Polynomial ℤ) (a : ℚ) (ha : a ≠ 0)
    (hm : m.IsPrimitive) (hmap : m.map (Int.castRingHom ℚ) = C a * minpoly ℚ u)
    (hnu : ¬ IsUnit m.leadingCoeff)
    {p : Polynomial ℤ} (hp : PMOne p) (hp0 : p ≠ 0) : Polynomial.aeval u p ≠ 0 := by
  intro hroot
  have hmapp : Polynomial.aeval u (p.map (Int.castRingHom ℚ)) = 0 := by
    have hc : (algebraMap ℤ ℚ) = Int.castRingHom ℚ := rfl
    rw [← hc, Polynomial.aeval_map_algebraMap ℚ u p, hroot]
  obtain ⟨k, hk⟩ := minpoly.dvd ℚ u hmapp
  have hdvdQ : m.map (Int.castRingHom ℚ) ∣ p.map (Int.castRingHom ℚ) := by
    refine ⟨C a⁻¹ * k, ?_⟩
    rw [hmap, hk, show (C a * minpoly ℚ u) * (C a⁻¹ * k)
      = (C a * C a⁻¹) * (minpoly ℚ u * k) from by ring, ← C_mul, mul_inv_cancel₀ ha, C_1, one_mul]
  obtain ⟨q, hq⟩ :=
    (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast m p hm (hp.isPrimitive hp0)).2 hdvdQ
  have hlead : p.leadingCoeff = m.leadingCoeff * q.leadingCoeff := by
    rw [hq, Polynomial.leadingCoeff_mul]
  rcases hp.leadingCoeff_eq hp0 with h1 | h1 <;> rw [h1] at hlead
  · exact hnu (isUnit_of_dvd_one ⟨q.leadingCoeff, hlead⟩)
  · exact hnu (isUnit_of_dvd_one ⟨-q.leadingCoeff, by rw [mul_neg, ← hlead]; ring⟩)

/-! ## The two minimal polynomials -/

/-- The minimal polynomial of `1/√2` over `ℚ` is `X² − 1/2`. -/
theorem minpoly_inv_sqrt_two : minpoly ℚ ((1:ℝ)/Real.sqrt 2) = X ^ 2 - C (1/2 : ℚ) := by
  set u : ℝ := 1/Real.sqrt 2 with hu
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hu2 : u ^ 2 = 1/2 := by rw [hu, div_pow, one_pow, hs]
  set q : Polynomial ℚ := X ^ 2 - C (1/2 : ℚ) with hq
  have hqm : q.Monic := Polynomial.monic_X_pow_sub_C _ (by norm_num)
  have hqroot : (Polynomial.aeval u) q = 0 := by simp [hq, hu2]
  have hdvd : minpoly ℚ u ∣ q := minpoly.dvd ℚ u hqroot
  have hint : IsIntegral ℚ u := ⟨q, hqm, hqroot⟩
  have hirr : Irrational u := by rw [hu, one_div]; exact irrational_sqrt_two.inv
  have hdeg1 : (minpoly ℚ u).degree ≠ 1 := by
    intro hc
    rw [minpoly.degree_eq_one_iff] at hc
    obtain ⟨c, hcv⟩ := hc
    exact hirr ⟨c, hcv⟩
  have hpos : 0 < (minpoly ℚ u).natDegree :=
    Polynomial.natDegree_pos_iff_degree_pos.mpr (minpoly.degree_pos hint)
  have hne1 : (minpoly ℚ u).natDegree ≠ 1 := by
    intro hc
    exact hdeg1 (by rw [Polynomial.degree_eq_natDegree (minpoly.ne_zero hint), hc]; rfl)
  have hqdeg : q.natDegree = 2 := by rw [hq]; compute_degree!
  exact monic_eq_of_dvd (minpoly.monic hint) hqm hdvd (by omega)

/-- The minimal polynomial of the rational number `2/3` over `ℚ` is `X − 2/3`. -/
theorem minpoly_two_thirds : minpoly ℚ ((2:ℝ)/3) = X - C (2/3 : ℚ) := by
  have h : ((2:ℝ)/3) = algebraMap ℚ ℝ (2/3 : ℚ) := by
    simp
  rw [h, minpoly.eq_X_sub_C ℝ]

/-! ## Lemma 11 -/

/-- **Lemma 11, first half** (`lem:overlap`).  `1/√2` is not a root of a
non-zero polynomial with coefficients in `{0, ±1}`. -/
theorem not_pm_root_inv_sqrt_two {p : Polynomial ℤ} (hp : PMOne p) (hp0 : p ≠ 0) :
    Polynomial.aeval ((1:ℝ)/Real.sqrt 2) p ≠ 0 := by
  refine not_root_of_primitive (C 2 * X ^ 2 - C 1) 2 (by norm_num) ?_ ?_ ?_ hp hp0
  · -- `2X² − 1` is primitive: its constant coefficient is `−1`
    intro s hs
    rw [C_dvd_iff_dvd_coeff] at hs
    have h := hs 0
    have hc : (C (2:ℤ) * X ^ 2 - C 1).coeff 0 = -1 := by simp
    rw [hc] at h
    rcases Int.isUnit_iff.1 (isUnit_of_dvd_one ((dvd_neg).1 h)) with h2 | h2 <;> simp [h2]
  · rw [minpoly_inv_sqrt_two]
    simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, map_C, map_X, mul_sub,
      ← C_mul]
    norm_num
  · have hdeg : (C (2:ℤ) * X ^ 2 - C 1).natDegree = 2 := by compute_degree!
    have hl : (C (2:ℤ) * X ^ 2 - C 1).leadingCoeff = 2 := by
      rw [Polynomial.leadingCoeff, hdeg]; simp [Polynomial.coeff_one]
    rw [hl]
    decide

/-- **Lemma 11, second half** (`lem:overlap`).  `2/3` is not a root of a
non-zero polynomial with coefficients in `{0, ±1}`. -/
theorem not_pm_root_two_thirds {p : Polynomial ℤ} (hp : PMOne p) (hp0 : p ≠ 0) :
    Polynomial.aeval ((2:ℝ)/3) p ≠ 0 := by
  refine not_root_of_primitive (C 3 * X - C 2) 3 (by norm_num) ?_ ?_ ?_ hp hp0
  · -- `3X − 2` is primitive: `gcd (3, 2) = 1`
    intro s hs
    rw [C_dvd_iff_dvd_coeff] at hs
    have h := hs 0
    have hc : (C (3:ℤ) * X - C 2).coeff 0 = -2 := by simp
    rw [hc] at h
    have h1 : s ∣ 3 := by simpa using hs 1
    have h2 : s ∣ (2:ℤ) := (dvd_neg).1 h
    exact isUnit_of_dvd_one (by simpa using Int.dvd_sub h1 h2)
  · rw [minpoly_two_thirds]
    simp only [Polynomial.map_sub, Polynomial.map_mul, map_C, map_X, mul_sub, ← C_mul]
    norm_num
  · have hdeg : (C (3:ℤ) * X - C 2).natDegree = 1 := by compute_degree!
    have hl : (C (3:ℤ) * X - C 2).leadingCoeff = 3 := by
      rw [Polynomial.leadingCoeff, hdeg]; simp
    rw [hl]
    decide

/-- If `x ≠ 0` satisfies `x² = x + 1` then `1/x` is a root of `x² + x − 1`. -/
lemma inv_root_quadratic {x : ℝ} (hx : x ≠ 0) (h : x ^ 2 = x + 1) :
    (1/x) ^ 2 + (1/x) - 1 = 0 := by
  field_simp
  linarith

/-- If `x ≠ 0` satisfies `x³ = x + 1` then `1/x` is a root of `x³ + x² − 1`. -/
lemma inv_root_cubic {x : ℝ} (hx : x ≠ 0) (h : x ^ 3 = x + 1) :
    (1/x) ^ 3 + (1/x) ^ 2 - 1 = 0 := by
  field_simp
  linarith

/-- **Lemma 11, the contrast.**  `1/φ` is a root of `x² + x − 1`. -/
theorem inv_phi_root :
    Polynomial.aeval (1/Golden.phi : ℝ) (X ^ 2 + X - C 1 : Polynomial ℤ) = 0 := by
  have h1 : (0:ℝ) < Golden.phi := lt_trans zero_lt_one Golden.one_lt_phi
  simpa using inv_root_quadratic (ne_of_gt h1) Golden.phi_sq

/-- **Lemma 11, the contrast.**  `1/ρ` is a root of `x³ + x² − 1`. -/
theorem inv_rho_root :
    Polynomial.aeval (1/Plastic.rho : ℝ) (X ^ 3 + X ^ 2 - C 1 : Polynomial ℤ) = 0 := by
  have h1 : (0:ℝ) < Plastic.rho := lt_trans zero_lt_one Plastic.one_lt_rho
  have hcube : Plastic.rho ^ 3 = Plastic.rho + 1 := by have := Plastic.rho_cubic; linarith
  simpa using inv_root_cubic (ne_of_gt h1) hcube


/-! ## Distinct branch words give distinct positions

The paper's use of Lemma 11 (Figure `fig:reachable`): at `λ = 3/2` and at
`λ = √2` two distinct branch words of a common length carry a knot from a
common starting point to distinct positions, so the number of reachable
positions is exactly the number of surviving words.

The position reached along a branch word `e` of length `n` is
`λⁿ x − (λ−1) ∑_j e_j λ^{n−j}` (`branchIter_eq`), so two words of a common
length agree exactly when the `{0, ±1}` polynomial built from their difference
vanishes at `r = 1/λ`.
-/

/-- Horner evaluation of a coefficient list at `t`: `∑ i, cᵢ tⁱ`. -/
noncomputable def hornerL : List ℤ → ℝ → ℝ
  | [], _ => 0
  | a :: c, t => (a : ℝ) + t * hornerL c t

/-- The integer polynomial whose `i`-th coefficient is the `i`-th entry of the
list. -/
noncomputable def polyL : List ℤ → Polynomial ℤ
  | [] => 0
  | a :: c => C a + X * polyL c

/-- The `i`-th entry of a coefficient list, `0` beyond its end. -/
def cf : List ℤ → ℕ → ℤ
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: c, (i+1) => cf c i

lemma aeval_polyL (t : ℝ) : ∀ c : List ℤ, Polynomial.aeval t (polyL c) = hornerL c t
  | [] => by simp [polyL, hornerL]
  | a :: c => by simp [polyL, hornerL, aeval_polyL t c]

lemma coeff_polyL : ∀ (c : List ℤ) (i : ℕ), (polyL c).coeff i = cf c i
  | [], i => by simp [polyL, cf]
  | a :: c, 0 => by simp [polyL, cf]
  | a :: c, (i+1) => by
      simp only [polyL, cf, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_X_mul,
        coeff_polyL c i]
      simp

lemma polyL_eq_zero_iff (c : List ℤ) : polyL c = 0 ↔ ∀ i, cf c i = 0 := by
  constructor
  · intro h i; rw [← coeff_polyL, h, Polynomial.coeff_zero]
  · intro h
    ext i
    rw [coeff_polyL, h i, Polynomial.coeff_zero]

/-- The weighted sum `∑_j c_j λ^{n−1−j}` of a coefficient list of length `n`. -/
noncomputable def wsum (lam : ℝ) : List ℤ → ℝ
  | [] => 0
  | a :: c => (a : ℝ) * lam ^ c.length + wsum lam c

lemma wsum_eq_hornerL {lam t : ℝ} (ht : lam * t = 1) :
    ∀ c : List ℤ, wsum lam c = lam ^ c.length * t * hornerL c t
  | [] => by simp [wsum, hornerL]
  | a :: c => by
      have ih := wsum_eq_hornerL ht c
      simp only [wsum, hornerL, List.length_cons, ih, pow_succ]
      have h2 : lam ^ c.length * lam * t * ((a:ℝ) + t * hornerL c t)
          = lam ^ c.length * (lam * t) * ((a:ℝ) + t * hornerL c t) := by ring
      rw [h2, ht, mul_one]
      ring

/-- A branch word as a coefficient list. -/
def bits (e : List (Fin 2)) : List ℤ := e.map (fun i : Fin 2 => (i.val : ℤ))

@[simp] lemma bits_nil : bits [] = [] := rfl

@[simp] lemma bits_cons (a : Fin 2) (e : List (Fin 2)) :
    bits (a :: e) = (a.val : ℤ) :: bits e := rfl

@[simp] lemma length_bits (e : List (Fin 2)) : (bits e).length = e.length := by
  simp [bits]

/-- The entrywise difference of two branch words. -/
def diffL : List (Fin 2) → List (Fin 2) → List ℤ
  | [], _ => []
  | _, [] => []
  | a :: e, b :: e' => ((b.val : ℤ) - (a.val : ℤ)) :: diffL e e'

lemma cf_diffL_pm : ∀ (e e' : List (Fin 2)) (i : ℕ),
    cf (diffL e e') i = -1 ∨ cf (diffL e e') i = 0 ∨ cf (diffL e e') i = 1
  | [], _, _ => by simp [diffL, cf]
  | _ :: _, [], _ => by simp [diffL, cf]
  | a :: _, b :: _, 0 => by
      simp only [diffL, cf]
      omega
  | a :: e, b :: e', (i+1) => by
      simpa [diffL, cf] using cf_diffL_pm e e' i

lemma length_diffL : ∀ (e e' : List (Fin 2)), e.length = e'.length →
    (diffL e e').length = e.length
  | [], _, _ => by simp [diffL]
  | _ :: _, [], h => by simp at h
  | a :: e, b :: e', h => by
      simp only [diffL, List.length_cons]
      simp only [List.length_cons] at h
      rw [length_diffL e e' (by omega)]

lemma eq_of_diffL_zero : ∀ (e e' : List (Fin 2)), e.length = e'.length →
    (∀ i, cf (diffL e e') i = 0) → e = e'
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: e, b :: e', h, hz => by
      have h0 : (b.val : ℤ) - (a.val : ℤ) = 0 := by simpa [diffL, cf] using hz 0
      have hab : a = b := Fin.ext (by omega)
      have htl : e = e' := by
        refine eq_of_diffL_zero e e' (by simpa using h) ?_
        intro i
        simpa [diffL, cf] using hz (i+1)
      rw [hab, htl]

/-- The difference of the weighted sums of two branch words of a common length
is the weighted sum of their difference. -/
lemma wsum_bits_sub (lam : ℝ) : ∀ (e e' : List (Fin 2)), e.length = e'.length →
    wsum lam (bits e') - wsum lam (bits e) = wsum lam (diffL e e')
  | [], [], _ => by simp [diffL, wsum]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: e, b :: e', h => by
      have h' : e.length = e'.length := by simpa using h
      have ih := wsum_bits_sub lam e e' h'
      have hle : (bits e').length = e.length := by simp [← h']
      have hld : (diffL e e').length = e.length := length_diffL e e' h'
      simp only [bits_cons, diffL, wsum, length_bits, hle, hld]
      push_cast
      linarith [ih]

/-- The position after a branch word: `λⁿ x − (λ−1) ∑_j e_j λ^{n−j}`. -/
lemma branchIter_eq (lam x : ℝ) : ∀ e : List (Fin 2),
    branchIter lam e x = lam ^ e.length * x - (lam - 1) * wsum lam (bits e)
  | [] => by simp [branchIter, wsum]
  | a :: e => by
      have ih := branchIter_eq lam (f lam a x) e
      have hf : f lam a x = lam * x - (lam - 1) * (a.val : ℝ) := by
        fin_cases a <;> simp [f]
      calc branchIter lam (a :: e) x = branchIter lam e (f lam a x) := rfl
        _ = lam ^ e.length * f lam a x - (lam - 1) * wsum lam (bits e) := ih
        _ = lam ^ (a :: e).length * x - (lam - 1) * wsum lam (bits (a :: e)) := by
            rw [hf]
            simp only [bits_cons, wsum, length_bits, List.length_cons, pow_succ]
            push_cast
            ring

/-- **Injectivity of the branch coding.**  If no non-zero `{0, ±1}` polynomial
vanishes at `r = 1/λ`, then two branch words of a common length carry a common
starting point to distinct positions unless they are equal. -/
theorem branchIter_injective {lam x : ℝ} (h : 1 < lam)
    (hno : ∀ p : Polynomial ℤ, PMOne p → p ≠ 0 → Polynomial.aeval (r lam) p ≠ 0)
    {e e' : List (Fin 2)} (hlen : e.length = e'.length)
    (heq : branchIter lam e x = branchIter lam e' x) : e = e' := by
  have hlam0 : (0:ℝ) < lam := lt_trans zero_lt_one h
  have hrt : lam * r lam = 1 := lam_mul_r h
  have hr0 : (0:ℝ) < r lam := r_pos lam h
  rw [branchIter_eq lam x e, branchIter_eq lam x e', hlen] at heq
  have hprod : (lam - 1) * (wsum lam (bits e') - wsum lam (bits e)) = 0 := by linarith
  have hw : wsum lam (bits e') - wsum lam (bits e) = 0 := by
    rcases mul_eq_zero.mp hprod with h1 | h1
    · exact absurd h1 (by linarith)
    · exact h1
  have hzero : wsum lam (diffL e e') = 0 := by
    rw [← wsum_bits_sub lam e e' hlen]; exact hw
  rw [wsum_eq_hornerL hrt] at hzero
  have hne : lam ^ (diffL e e').length * r lam ≠ 0 := by positivity
  have hh : hornerL (diffL e e') (r lam) = 0 := by
    rcases mul_eq_zero.mp hzero with h1 | h1
    · exact absurd h1 hne
    · exact h1
  have hpoly : Polynomial.aeval (r lam) (polyL (diffL e e')) = 0 := by
    rw [aeval_polyL, hh]
  have hp0 : polyL (diffL e e') = 0 := by
    by_contra hcon
    exact hno _ (fun i => by rw [coeff_polyL]; exact cf_diffL_pm e e' i) hcon hpoly
  exact eq_of_diffL_zero e e' hlen ((polyL_eq_zero_iff _).1 hp0)

/-- **At `λ = 3/2` distinct branch words of a common length give distinct
positions** (`lem:overlap`, as used in Figure `fig:reachable`). -/
theorem branchIter_injective_three_halves {x : ℝ} {e e' : List (Fin 2)}
    (hlen : e.length = e'.length)
    (heq : branchIter (3/2) e x = branchIter (3/2) e' x) : e = e' := by
  refine branchIter_injective (by norm_num) ?_ hlen heq
  have hr : r (3/2 : ℝ) = 2/3 := by norm_num [r]
  rw [hr]
  intro p hp hp0
  exact not_pm_root_two_thirds hp hp0

/-- **At `λ = √2` distinct branch words of a common length give distinct
positions** (`lem:overlap`, as used in Figure `fig:reachable`). -/
theorem branchIter_injective_sqrt_two {x : ℝ} {e e' : List (Fin 2)}
    (hlen : e.length = e'.length)
    (heq : branchIter (Real.sqrt 2) e x = branchIter (Real.sqrt 2) e' x) : e = e' := by
  have h1 : (1:ℝ) < Real.sqrt 2 := by
    have h2 : Real.sqrt 1 < Real.sqrt 2 := by
      apply Real.sqrt_lt_sqrt <;> norm_num
    simpa using h2
  refine branchIter_injective h1 ?_ hlen heq
  have hr : r (Real.sqrt 2) = 1/Real.sqrt 2 := by simp [r, one_div]
  rw [hr]
  intro p hp hp0
  exact not_pm_root_inv_sqrt_two hp hp0

end Overlap
end KnotGame
