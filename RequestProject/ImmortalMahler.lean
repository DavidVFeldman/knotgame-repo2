import RequestProject.Translation

/-!
# T27 — immortal births at `λ = 3/2` (paper `prop:immortal32`)

The paper's `prop:immortal32` reads:

> If some `c ∈ {0,1,2}^ℕ` has infinitely many indices `t` with `c_t = 1` whose
> trajectories never meet the control, then `N_{3/2} = ∞`.

`RequestProject.Translation` already contains the dictionary between the game
at `λ = 3/2` and the knot-free `w`-recursion, together with the equivalence
`unbounded_iff_mahler` between unboundedness of `N_{3/2}` and the *finite*
criterion `MahlerCriterion`.  This file adds the *immortal* form of the
avoidance condition and derives the proposition.

The paper's two-line proof ("those knots are immortal, and distinct by
`lem:distinct`") is exactly what `unbounded_iff_mahler` packages: the
bookkeeping that distinct births give distinct knots is `card_birthSet`
together with `card_run` (`Suffix.lean`), which is where `lem:distinct` is
used.  Nothing is re-derived here.

## Conventions (SCRUPLES)

* Indices follow `Translation.lean`: `c j` is the control letter applied
  between time `j` and time `j+1`, so a birth at letter `b` (`c b = 1`)
  produces a knot at `w = 1` whose trajectory is driven by
  `c (b+1), c (b+2), …`.
* `MahlerImmortal c b` is `MahlerAlive c b N` with the horizon removed: the
  trajectory avoids the control *for ever*.
* Controls are functions `ℕ → ℤ` with values in `{0,1,2}`, as in
  `Translation.lean`; `unbounded_of_infinite_immortal_fin` is the same
  statement for a control `c : ℕ → Fin 3`.
* "`N_{3/2} = ∞`" is rendered, as everywhere in this development, as
  `∀ K, ∃ n, K ≤ N (3/2) n`.
-/

namespace KnotGame
namespace Ternary

/-- The knot born by the letter `b` of the control `c` is **immortal**: its
`w`-trajectory avoids the control at every future time. -/
def MahlerImmortal (c : ℕ → ℤ) (b : ℕ) : Prop :=
  ∀ i : ℕ, ⌊(3 / 2 : ℝ) * witer c (b + 1) 1 i⌋ ≠ c (b + 1 + i)

/-- An immortal birth is alive up to every finite horizon. -/
lemma mahlerAlive_of_immortal {c : ℕ → ℤ} {b : ℕ} (h : MahlerImmortal c b) (N : ℕ) :
    MahlerAlive c b N := fun i _ => h i

/-- **T27** (paper `prop:immortal32`).  If a control with values in `{0,1,2}`
has infinitely many indices carrying the digit `1` whose trajectories never
meet the control, then `N_{3/2}` is unbounded. -/
theorem unbounded_of_infinite_immortal (c : ℕ → ℤ)
    (hc : ∀ j, c j = 0 ∨ c j = 1 ∨ c j = 2)
    (hinf : {b : ℕ | c b = 1 ∧ MahlerImmortal c b}.Infinite) :
    ∀ K : ℕ, ∃ n : ℕ, K ≤ N (3 / 2 : ℝ) n := by
  refine unbounded_iff_mahler.mpr ?_
  intro k
  set p : ℕ → Prop := fun b => c b = 1 ∧ MahlerImmortal c b with hp
  have hinf' : (setOf p).Infinite := hinf
  refine ⟨Nat.nth p k + 1, c, Nat.nth p, hc, ?_, ?_⟩
  · intro i i' hii _
    exact (Nat.nth_lt_nth hinf').mpr hii
  · intro i hi
    obtain ⟨hone, himm⟩ : p (Nat.nth p i) := Nat.nth_mem_of_infinite hinf' i
    refine ⟨?_, hone, mahlerAlive_of_immortal himm _⟩
    have : Nat.nth p i < Nat.nth p k := (Nat.nth_lt_nth hinf').mpr hi
    omega

/-- **T27**, for a control presented as `c : ℕ → Fin 3`. -/
theorem unbounded_of_infinite_immortal_fin (c : ℕ → Fin 3)
    (hinf : {b : ℕ | c b = 1 ∧ MahlerImmortal (fun j => (c j : ℤ)) b}.Infinite) :
    ∀ K : ℕ, ∃ n : ℕ, K ≤ N (3 / 2 : ℝ) n := by
  refine unbounded_of_infinite_immortal (fun j => (c j : ℤ)) (fun j => ?_) ?_
  · have : (c j : ℕ) = 0 ∨ (c j : ℕ) = 1 ∨ (c j : ℕ) = 2 := by omega
    rcases this with h | h | h <;> simp [h]
  · refine hinf.mono ?_
    rintro b ⟨h1, h2⟩
    exact ⟨by simp [h1], h2⟩

end Ternary
end KnotGame
