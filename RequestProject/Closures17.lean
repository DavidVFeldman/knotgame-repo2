import RequestProject.BackwardClosure
import RequestProject.Contraction
import RequestProject.Pisot

/-!
# Round 17 — three small closures (T47, T48, T49)

Three independent statements, none of which depends on the others.

* **T47** (`no_contracting_weight`).  For `1 < lam < 2` there is no weight
  `w : ℝ → ℝ` bounded below by `1` on `(0,1)` which contracts by a fixed factor
  `θ < 1` along every legal move.  The reason is that every point of `(0,1)`
  has a legal move keeping it in `(0,1)` (because `g lam < r lam` exactly when
  `lam < 2`), so from any starting point there is an infinite legal orbit, along
  which the weight would decay to zero.

* **T48** (`P_id`, `dist_P_id`, `not_lipschitzWith_P_id`).  The contraction
  factor `r lam` of `Contraction.lipschitz_contraction` is best possible: it is
  attained at the identity, where `P lam id` is the affine map
  `y ↦ r lam * y + (1 - r lam)/2`.

* **T49** (`not_kindDense_of_orb_finite`, `not_denseFrom_half_of_finite`,
  `not_kindDense_of_isPisot`, `not_denseFrom_half_of_isPisot`).  The density
  criterion of §10 fails at every Pisot parameter: `Orb lam` is finite there,
  and a finite set is not dense in `(0,1)`.

Everything here is stated for a general real `lam`; no parameter-specific
computation occurs.
-/

namespace KnotGame
namespace Closures17

open Set

variable {lam : ℝ}

/-! ## T47 — no contracting weight exists -/

/-- For `1 < lam < 2` the deleted proportion is smaller than the retained one.
This is exactly what makes the two moves `R` (legal below `r lam`) and `L`
(legal above `g lam`) cover all of `(0,1)`. -/
lemma g_lt_r (h : 1 < lam) (h2 : lam < 2) : g lam < r lam := by
  have hlam : (0:ℝ) < lam := lt_trans zero_lt_one h
  have hr : lam * r lam = 1 := lam_mul_r h
  have hr0 : 0 < r lam := r_pos lam h
  have : g lam = 1 - r lam := rfl
  nlinarith

/-- The move chosen at `x`: `R` below `r lam`, `L` above it. -/
noncomputable def nextMove (lam x : ℝ) : Move :=
  if x < r lam then Move.R else Move.L

/-- The chosen move is legal at every point of `(0,1)`. -/
lemma survives_nextMove (h : 1 < lam) (h2 : lam < 2) (x : ℝ) :
    survives lam (nextMove lam x) x := by
  by_cases hxr : x < r lam
  · rw [nextMove, if_pos hxr]
    exact hxr
  · rw [nextMove, if_neg hxr]
    exact lt_of_lt_of_le (g_lt_r h h2) (not_lt.1 hxr)

/-- The infinite legal orbit from `x`: at each step the move `nextMove` is
played. -/
noncomputable def orbit (lam x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 => act lam (nextMove lam (orbit lam x n)) (orbit lam x n)

@[simp] lemma orbit_zero (lam x : ℝ) : orbit lam x 0 = x := rfl

lemma orbit_succ (lam x : ℝ) (n : ℕ) :
    orbit lam x (n + 1) = act lam (nextMove lam (orbit lam x n)) (orbit lam x n) := rfl

/-- The orbit never leaves `(0,1)`. -/
lemma orbit_mem_Ioo (h : 1 < lam) (h2 : lam < 2) {x : ℝ} (hx : x ∈ Ioo (0:ℝ) 1) :
    ∀ n, orbit lam x n ∈ Ioo (0:ℝ) 1 := by
  intro n
  induction n with
  | zero => simpa using hx
  | succ n ih =>
      rw [orbit_succ]
      exact act_mem_Ioo h ih (survives_nextMove h h2 _)

/-- **T47.**  No weight bounded below by `1` on `(0,1)` contracts along every
legal move by a fixed factor `< 1`. -/
theorem no_contracting_weight (h : 1 < lam) (h2 : lam < 2)
    (w : ℝ → ℝ) (th : ℝ) (hth : th < 1)
    (hw : ∀ x ∈ Ioo (0:ℝ) 1, 1 ≤ w x) :
    ¬ (∀ x ∈ Ioo (0:ℝ) 1, ∀ m : Move, survives lam m x → w (act lam m x) ≤ th * w x) := by
  intro hcon
  have hhalf : (1/2 : ℝ) ∈ Ioo (0:ℝ) 1 := by constructor <;> norm_num
  set x : ℕ → ℝ := orbit lam (1/2) with hx
  have hmem : ∀ n, x n ∈ Ioo (0:ℝ) 1 := orbit_mem_Ioo h h2 hhalf
  have hstep : ∀ n, w (x (n + 1)) ≤ th * w (x n) := by
    intro n
    have := hcon (x n) (hmem n) (nextMove lam (x n)) (survives_nextMove h h2 (x n))
    simpa [hx, orbit_succ] using this
  rcases lt_or_ge th 0 with hneg | hpos
  · have h1 : (1:ℝ) ≤ w (x 1) := hw _ (hmem 1)
    have h0 : (1:ℝ) ≤ w (x 0) := hw _ (hmem 0)
    have := hstep 0
    nlinarith
  · have hdecay : ∀ n, w (x n) ≤ th ^ n * w (x 0) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          have := hstep n
          have hmono : th * w (x n) ≤ th * (th ^ n * w (x 0)) :=
            mul_le_mul_of_nonneg_left ih hpos
          calc w (x (n + 1)) ≤ th * w (x n) := this
            _ ≤ th * (th ^ n * w (x 0)) := hmono
            _ = th ^ (n + 1) * w (x 0) := by ring
    have hw0 : (1:ℝ) ≤ w (x 0) := hw _ (hmem 0)
    have hw0pos : 0 < w (x 0) := lt_of_lt_of_le zero_lt_one hw0
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < 1 / w (x 0)) hth
    have hlt : th ^ n * w (x 0) < 1 := by
      have := mul_lt_mul_of_pos_right hn hw0pos
      rwa [div_mul_cancel₀ _ (ne_of_gt hw0pos)] at this
    have := hdecay n
    have := hw _ (hmem n)
    linarith

/-! ## T48 — sharpness of the contraction constant -/

/-- **T48.**  `P lam` applied to the identity is the affine map
`y ↦ r lam * y + (1 - r lam)/2`. -/
theorem P_id : Contraction.P lam id = fun y => r lam * y + (1 - r lam) / 2 := by
  funext y
  simp only [Contraction.P, id_eq]
  ring

/-- **T48, the sharpness.**  On the identity `P lam` scales distances by exactly
`r lam`: the contraction factor of `Contraction.lipschitz_contraction` cannot be
improved. -/
theorem dist_P_id (h : 1 < lam) (y z : ℝ) :
    dist (Contraction.P lam id y) (Contraction.P lam id z) = r lam * dist y z := by
  have hr0 : 0 < r lam := r_pos lam h
  have e : Contraction.P lam id y - Contraction.P lam id z = r lam * (y - z) := by
    simp only [Contraction.P, id_eq]; ring
  rw [Real.dist_eq, Real.dist_eq, e, abs_mul, abs_of_pos hr0]

/-- **T48, restated as a non-Lipschitz statement.**  `P lam id` is not
`LipschitzWith K` for any `K < r lam`. -/
theorem not_lipschitzWith_P_id (h : 1 < lam) {K : NNReal} (hK : (K : ℝ) < r lam) :
    ¬ LipschitzWith K (Contraction.P lam id) := by
  intro hlip
  have hd := hlip.dist_le_mul 1 0
  rw [dist_P_id h] at hd
  have : dist (1:ℝ) 0 = 1 := by simp
  rw [this, mul_one] at hd
  linarith

/-! ## T49 — the density criterion fails at every Pisot parameter -/

/-- Membership in `Orb`, unfolded: the orbit of `1/2` is exactly the set of
endpoints of the words that `1/2` survives. -/
lemma mem_orb_iff {x : ℝ} :
    x ∈ Orb lam ↔ ∃ u : List Move, survivesWord lam (1/2) u ∧ posAfter lam (1/2) u = x :=
  Iff.rfl

/-- **T49(a).**  A finite orbit is not dense: `KindDense` fails whenever
`Orb lam` is finite.  No hypothesis on `lam` is needed. -/
theorem not_kindDense_of_orb_finite (hfin : (Orb lam).Finite) : ¬ KindDense lam := by
  intro H
  set S : Finset ℝ := hfin.toFinset with hS
  set n : ℕ := S.card + 1 with hn
  have hn0 : 0 < n := Nat.succ_pos _
  have hnR : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have key : ∀ k : Fin n, ∃ y : ℝ, y ∈ Orb lam ∧
      ((k : ℕ) : ℝ) / (n : ℝ) < y ∧ y < (((k : ℕ) : ℝ) + 1) / (n : ℝ) := by
    intro k
    have h1 : (0:ℝ) ≤ ((k : ℕ) : ℝ) / (n : ℝ) := by positivity
    have h2 : ((k : ℕ) : ℝ) / (n : ℝ) < (((k : ℕ) : ℝ) + 1) / (n : ℝ) := by
      gcongr; linarith
    have h3 : (((k : ℕ) : ℝ) + 1) / (n : ℝ) ≤ 1 := by
      rw [div_le_one hnR]
      exact_mod_cast Nat.succ_le_of_lt k.isLt
    obtain ⟨u, hu, hu1, hu2⟩ := H _ _ h1 h2 h3
    exact ⟨posAfter lam (1/2) u, ⟨u, hu, rfl⟩, hu1, hu2⟩
  choose y hy hy1 hy2 using key
  have hinj : Function.Injective y := by
    intro a b hab
    have hab1 : ((a : ℕ) : ℝ) / (n : ℝ) < (((b : ℕ) : ℝ) + 1) / (n : ℝ) := by
      have := hy1 a
      rw [hab] at this
      exact lt_trans this (hy2 b)
    have hab2 : ((b : ℕ) : ℝ) / (n : ℝ) < (((a : ℕ) : ℝ) + 1) / (n : ℝ) := by
      have := hy1 b
      rw [← hab] at this
      exact lt_trans this (hy2 a)
    have e1 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) + 1 := by
      have := mul_lt_mul_of_pos_right hab1 hnR
      field_simp at this
      linarith
    have e2 : ((b : ℕ) : ℝ) < ((a : ℕ) : ℝ) + 1 := by
      have := mul_lt_mul_of_pos_right hab2 hnR
      field_simp at this
      linarith
    have e1' : (a : ℕ) < (b : ℕ) + 1 := by exact_mod_cast e1
    have e2' : (b : ℕ) < (a : ℕ) + 1 := by exact_mod_cast e2
    exact Fin.ext (by omega)
  have hsub : (Finset.univ : Finset (Fin n)).image y ⊆ S := by
    intro z hz
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz
    obtain ⟨k, rfl⟩ := hz
    rw [hS, Set.Finite.mem_toFinset]
    exact hy k
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at hcard
  omega

/-- **T49(b).**  A finite orbit refutes the density hypothesis in its branch-word
form as well.  (Through `denseFrom_half_imp_kindDense`, the direction of the
round-15 equivalence that needs no hypothesis on `lam`.) -/
theorem not_denseFrom_half_of_finite (hfin : (Orb lam).Finite) :
    ¬ BackwardClosure.DenseFrom lam (1/2) := fun H =>
  not_kindDense_of_orb_finite hfin (BackwardClosure.denseFrom_half_imp_kindDense H)

/-- **T49(c).**  At a Pisot parameter the density criterion fails. -/
theorem not_kindDense_of_isPisot (h : IsPisot lam) : ¬ KindDense lam :=
  not_kindDense_of_orb_finite (orb_finite h)

/-- **T49(c'), the branch-word form.** -/
theorem not_denseFrom_half_of_isPisot (h : IsPisot lam) :
    ¬ BackwardClosure.DenseFrom lam (1/2) :=
  not_denseFrom_half_of_finite (orb_finite h)

end Closures17
end KnotGame
