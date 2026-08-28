import RequestProject.BranchingCount
import RequestProject.Transversality

/-!
# The common window (round 4, T13)

A single citable statement asserting that every certified tool of the project
coexists on the parameter window

  `lam ∈ [1000/667, 8/5]`,

which contains `3/2`:

* **(a)** the round-3 δ-transversality theorem applies at `x = 1/lam`, because
  `1/lam ∈ [5/8, 667/1000] ⊆ [1/2, 667/1000]`;
* **(b)** `lam² < lam + 1`, i.e. `lam < φ`, so the round-4 branching lemmas T11
  apply;
* **(c)** `3/2` lies in the window, and `1/2` is a point of the dynamical window
  `(g, r)` for every such `lam`;
* the quantitative data of T11d hold with `η = 1/5` and `B = 3`, so the
  continuum T12a and the linear count `m/4 ≤ K lam m` of T12b are available
  throughout the window.
-/

namespace KnotGame
namespace CommonWindow

open Branching

/-- The left endpoint of the round-4 anchor window. -/
noncomputable def lamLo : ℝ := 1000 / 667

/-- The right endpoint of the round-4 anchor window. -/
noncomputable def lamHi : ℝ := 8 / 5

lemma lamLo_lt_lamHi : lamLo < lamHi := by norm_num [lamLo, lamHi]

lemma one_lt_lamLo : 1 < lamLo := by norm_num [lamLo]

lemma lamHi_sq : lamHi ^ 2 < lamHi + 1 := by norm_num [lamHi]

/-- `g` at the right endpoint is `3/8`. -/
lemma g_lamHi : g lamHi = 3 / 8 := by norm_num [g, r, lamHi]

/-- The commission's `η` for the anchor window is `1/5`. -/
lemma eta_anchor : eta lamLo lamHi = 1 / 5 := by
  rw [eta, lamLo, lamHi]
  norm_num

/-- The commission's return bound: `B = 3` works, since `lam₀² · η > g(lam₁)`. -/
lemma return_bound_anchor : g lamHi < lamLo ^ (3 - 1) * eta lamLo lamHi := by
  rw [g_lamHi, eta_anchor, lamLo]
  norm_num

/-- **T13 (the common window).**  Everything the project certifies is available
simultaneously on `[1000/667, 8/5]`, a window containing `3/2`. -/
theorem common_window (lam : ℝ) (hlo : lamLo ≤ lam) (hhi : lam ≤ lamHi) :
    -- (a) the round-3 transversality window contains `1/lam`
    (5 / 8 ≤ 1 / lam ∧ 1 / lam ≤ 667 / 1000 ∧ 1 / 2 ≤ 1 / lam) ∧
    (∀ c : ℕ → ℤ, c 0 = 1 → (∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) →
      |Transversality.gval c (1 / lam)| ≤ 1 / 1000 →
      Transversality.gder c (1 / lam) < -(1 / 1000)) ∧
    -- (b) below the golden ratio, so T11 applies
    (1 < lam ∧ lam < 2 ∧ lam ^ 2 < lam + 1) ∧
    -- (c) `3/2` lies in the parameter window, and `1/2` in the dynamical window
    (lamLo ≤ 3 / 2 ∧ (3 / 2 : ℝ) ≤ lamHi) ∧ (1 / 2 : ℝ) ∈ Window lam ∧
    -- T12a: a continuum of survival itineraries of `1/2`
    (∃ Θ : (ℕ → Bool) → (ℕ → Fin 2),
      Function.Injective Θ ∧ ∀ b, Surviving lam (1 / 2) (Θ b)) ∧
    -- T12b: the linear count, with `B = 3`
    (∀ m : ℕ, m / 4 ≤ K lam m) := by
  have hlo' : (1000 : ℝ) / 667 ≤ lam := hlo
  have hhi' : lam ≤ 8 / 5 := hhi
  have h1 : 1 < lam := by linarith
  have h2 : lam < 2 := by linarith
  have hpos : (0:ℝ) < lam := by linarith
  have hphi : lam ^ 2 < lam + 1 := by nlinarith
  have hinv1 : 5 / 8 ≤ 1 / lam := by
    rw [le_div_iff₀ hpos]; linarith
  have hinv2 : 1 / lam ≤ 667 / 1000 := by
    rw [div_le_iff₀ hpos]; linarith
  refine ⟨⟨hinv1, hinv2, by linarith⟩, ?_, ⟨h1, h2, hphi⟩, ⟨by norm_num [lamLo], by
    norm_num [lamHi]⟩, half_mem_Window h1 h2, ?_, ?_⟩
  · intro c hc0 hc hg
    exact Transversality.transversality c hc0 hc (by linarith) hinv2 hg
  · exact continuum_of_survival_itineraries h1 h2 hphi
  · intro m
    have := K_ge (lam0 := lamLo) (lam1 := lamHi) (B := 3) (by norm_num) one_lt_lamLo hlo hhi
      lamHi_sq return_bound_anchor m
    simpa using this

end CommonWindow
end KnotGame
