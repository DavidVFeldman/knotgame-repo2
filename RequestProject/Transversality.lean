import RequestProject.TransversalityCell
import RequestProject.TransversalityCertificate

/-!
# δ-transversality on `[1/2, 667/1000]` (round 3, Target T9)

For the class

  `𝓑₀₁ = { g(x) = 1 + ∑_{i≥1} c_i x^i : c_i ∈ {−1,0,1} }`

and `δ = 1/1000`, every `g ∈ 𝓑₀₁` satisfies, on the window `x ∈ [1/2, 667/1000]`,

  `|g(x)| ≤ δ  ⟹  g′(x) < −δ`.

The proof combines
* `cell_sound` (soundness of the branch-and-bound checker on one cell),
* the 27 kernel-checked cell certificates of
  `RequestProject.TransversalityCertificate`,
* the covering argument `exists_cell` below, which locates `x` in one of the
  cells.

`transversality` states the conclusion for the termwise derivative series
`gder`; `hasDerivAt_gval` identifies that series with the actual derivative of
`gval`, and `transversality_deriv` is the resulting statement about `deriv`.
-/

namespace KnotGame
namespace Transversality

open Finset

/-! ### Locating a point in the decomposition -/

/-- `ChainFrom a L` says that the cells of `L` tile an interval starting at
`a`: consecutive cells share an endpoint. -/
def ChainFrom : ℕ → List (ℕ × ℕ) → Prop
  | _, [] => True
  | a, p :: rest => p.1 = a ∧ ChainFrom p.2 rest

/-- The right endpoint of the last cell of `L`, or `a` if `L` is empty. -/
def lastEnd : ℕ → List (ℕ × ℕ) → ℕ
  | a, [] => a
  | _, p :: rest => lastEnd p.2 rest

/-- A point of the tiled interval lies in one of the cells. -/
lemma exists_cell : ∀ (L : List (ℕ × ℕ)) (a : ℕ) (x : ℝ), ChainFrom a L → L ≠ [] →
    (a : ℝ) / Qn ≤ x → x ≤ (lastEnd a L : ℝ) / Qn →
    ∃ p ∈ L, ((p.1 : ℝ) / Qn ≤ x ∧ x ≤ (p.2 : ℝ) / Qn) := by
  intro L
  induction L with
  | nil => intro a x _ hne; exact absurd rfl hne
  | cons p rest ih =>
      intro a x hchain _ hxa hxb
      obtain ⟨hp1, hrest⟩ := hchain
      have hlast : lastEnd a (p :: rest) = lastEnd p.2 rest := rfl
      rw [hlast] at hxb
      match rest, hrest, hxb with
      | [], _, hxb =>
          refine ⟨p, by simp, ?_, ?_⟩
          · rw [hp1]; exact hxa
          · exact hxb
      | (q :: rest'), hrest, hxb =>
          rcases le_total x ((p.2 : ℝ) / Qn) with h | h
          · exact ⟨p, by simp, by rw [hp1]; exact hxa, h⟩
          · obtain ⟨r, hr, hr1, hr2⟩ := ih p.2 x hrest (by simp) h hxb
            exact ⟨r, List.mem_cons_of_mem _ hr, hr1, hr2⟩

lemma cells_chain : ChainFrom 512000000 cells := by
  simp [cells, ChainFrom]

lemma cells_lastEnd : lastEnd 512000000 cells = 683008000 := rfl

/-! ### The main theorem -/

/-- **δ-transversality on the window.**  For a power series with coefficients in
`{−1,0,1}` and constant term `1`, on `[1/2, 667/1000]` a value of modulus at
most `1/1000` forces the (termwise) derivative to be less than `−1/1000`. -/
theorem transversality (c : ℕ → ℤ) (hc0 : c 0 = 1)
    (hc : ∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) {x : ℝ}
    (hx1 : 1 / 2 ≤ x) (hx2 : x ≤ 667 / 1000) (hg : |gval c x| ≤ 1 / 1000) :
    gder c x < -(1 / 1000) := by
  have hcabs : ∀ i, |(c i : ℝ)| ≤ 1 := by
    intro i
    rcases hc i with h | h | h <;> rw [h] <;> norm_num
  have hQ : ((Qn : ℕ) : ℝ) = 1024000000 := by norm_num [Qn]
  have ha : ((512000000 : ℕ) : ℝ) / Qn ≤ x := by
    rw [hQ]; push_cast; linarith
  have hb : x ≤ ((683008000 : ℕ) : ℝ) / Qn := by
    rw [hQ]; push_cast; linarith
  obtain ⟨p, hp, hp1, hp2⟩ :=
    exists_cell cells 512000000 x cells_chain (by simp [cells]) ha
      (by rw [cells_lastEnd]; exact hb)
  obtain ⟨hle, h34, hev⟩ := cells_wf p hp
  exact cell_sound hle h34 hev (cells_ok p hp) hc0 hcabs hp1 hp2 hg

/-! ### The termwise series is the derivative -/

/-- On `(-4/5, 4/5)` the termwise derivative series is the derivative of the
series. -/
lemma hasDerivAt_gval (c : ℕ → ℤ) (hc : ∀ i, |(c i : ℝ)| ≤ 1) {y : ℝ} (hy : |y| < 4 / 5) :
    HasDerivAt (gval c) (gder c y) y := by
  set t : Set ℝ := Set.Ioo (-(4/5 : ℝ)) (4/5) with ht
  have hyt : y ∈ t := by
    rw [ht]
    rcases abs_lt.mp hy with ⟨h1, h2⟩
    exact ⟨h1, h2⟩
  have hu : Summable (fun n : ℕ => (n : ℝ) * (4/5 : ℝ) ^ (n - 1)) :=
    summable_nat_mul_pow (by norm_num) (by norm_num)
  have hderiv : ∀ (n : ℕ), ∀ z ∈ t, HasDerivAt (fun w : ℝ => (c n : ℝ) * w ^ n)
      ((n : ℝ) * (c n : ℝ) * z ^ (n - 1)) z := by
    intro n z _
    have h := (hasDerivAt_pow n z).const_mul ((c n : ℝ))
    have heq : (c n : ℝ) * ((n : ℝ) * z ^ (n - 1)) = (n : ℝ) * (c n : ℝ) * z ^ (n - 1) := by
      ring
    rw [heq] at h
    exact h
  have hbound : ∀ (n : ℕ), ∀ z ∈ t, ‖(n : ℝ) * (c n : ℝ) * z ^ (n - 1)‖
      ≤ (n : ℝ) * (4/5 : ℝ) ^ (n - 1) := by
    intro n z hz
    rw [ht] at hz
    have hz' : |z| ≤ 4/5 := le_of_lt (abs_lt.mpr ⟨hz.1, hz.2⟩)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, Nat.abs_cast]
    have h1 : |z| ^ (n - 1) ≤ (4/5 : ℝ) ^ (n - 1) := pow_le_pow_left₀ (abs_nonneg z) hz' _
    have h2 : (0:ℝ) ≤ |z| ^ (n - 1) := by positivity
    have h3 : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    have hstep : |(c n : ℝ)| * |z| ^ (n - 1) ≤ (4/5 : ℝ) ^ (n - 1) := by
      have h := mul_le_mul (hc n) h1 h2 (by norm_num : (0:ℝ) ≤ 1)
      simpa using h
    calc (n : ℝ) * |(c n : ℝ)| * |z| ^ (n - 1)
        = (n : ℝ) * (|(c n : ℝ)| * |z| ^ (n - 1)) := by ring
      _ ≤ (n : ℝ) * (4/5 : ℝ) ^ (n - 1) := mul_le_mul_of_nonneg_left hstep h3
  have h0 : Summable (fun n : ℕ => (c n : ℝ) * (0:ℝ) ^ n) :=
    summable_gterm hc (le_refl 0) (by norm_num)
  have h0t : (0:ℝ) ∈ t := by rw [ht]; constructor <;> norm_num
  have := hasDerivAt_tsum_of_isPreconnected (u := fun n : ℕ => (n : ℝ) * (4/5 : ℝ) ^ (n - 1))
    (g := fun n : ℕ => fun w : ℝ => (c n : ℝ) * w ^ n)
    (g' := fun n : ℕ => fun w : ℝ => (n : ℝ) * (c n : ℝ) * w ^ (n - 1))
    hu isOpen_Ioo isPreconnected_Ioo hderiv hbound h0t h0 hyt
  exact this

/-- **δ-transversality, stated for the derivative.** -/
theorem transversality_deriv (c : ℕ → ℤ) (hc0 : c 0 = 1)
    (hc : ∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) {x : ℝ}
    (hx1 : 1 / 2 ≤ x) (hx2 : x ≤ 667 / 1000) (hg : |gval c x| ≤ 1 / 1000) :
    HasDerivAt (gval c) (gder c x) x ∧ deriv (gval c) x < -(1 / 1000) := by
  have hcabs : ∀ i, |(c i : ℝ)| ≤ 1 := by
    intro i
    rcases hc i with h | h | h <;> rw [h] <;> norm_num
  have hx : |x| < 4 / 5 := by
    rw [abs_lt]; constructor <;> linarith
  have hd := hasDerivAt_gval c hcabs hx
  refine ⟨hd, ?_⟩
  rw [hd.deriv]
  exact transversality c hc0 hc hx1 hx2 hg

end Transversality
end KnotGame
