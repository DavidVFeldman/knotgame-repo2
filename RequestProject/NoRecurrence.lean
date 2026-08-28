import RequestProject.Ternary
import RequestProject.Permanence

/-!
# T30 — no position recurs at `λ = 3/2` (paper `prop:norecur`)

At `λ = 3/2` no knot ever occupies the same position twice.

The paper's proof (§12) solves the fixed-point equation of the affine composite
`x ↦ λ^B x − c` applied by a block of `B` moves, clears denominators, and rules
out the two integer solutions `0` and `1`.  Round 8 already carries the piece of
information that makes all of this immediate, namely the **dyadic invariant** of
`RequestProject.Ternary`: a knot that was born `n` moves ago sits at an *odd*
multiple of `2 ^ -(n+1)` (`Ternary.Dyadic n`, `Ternary.dyadic_posAfter`).  As
prescribed by the commission this file reuses that invariant rather than
re-deriving the dyadic structure.

The whole content is then the observation that the dyadic level of a point is
determined by the point (`dyadic_level_unique`): if
`k / 2 ^ (m+1) = j / 2 ^ (n+1)` with `k`, `j` odd then `m = n`.  Since each move
raises the level by exactly one (`Ternary.dyadic_act`), a knot's position after
`u` moves determines the number of moves, so:

* `posAfter_length_eq` — the position of a knot determines its age;
* `no_recurrence` — a nonempty block of moves never returns a knot to where it
  started;
* `positions_pairwise_ne`, `knot_positions_injective` — the successive positions
  of one knot are pairwise distinct;
* `no_identity_block`, `no_identity_block_config` — the corollary the paper
  cites against a candidate mechanism for `prop:twostep`: no nonempty block of
  moves acts as the identity on a knot of a reachable configuration.

## Conventions (SCRUPLES)

* "Position" means the position of a knot of the game, i.e. a point on the
  forward orbit of the birth place `1/2`; that is exactly the hypothesis
  `Dyadic n x` under which the statements below are proved, and it is supplied
  for genuine knots by `dyadic_of_knotAt`.
* The paper argues with the numerator identity
  `Σ_{j=1}^B 3^{B−j} 2^{j−1} = 3^B − 2^B` and the oddness of `3^B − 2^B`.  Here
  the same arithmetic obstruction appears one step earlier: a recurrence would
  equate an odd numerator with an even one, because the denominator `2 ^ (n+1)`
  of a knot position is never `1`.  The fixed points `0` and `1` of the paper's
  discussion are therefore never in play — they are not dyadic of any level —
  and no separate argument excluding them is needed.
* Nothing is assumed about legality: the statements hold for the trajectory of
  the position under *any* block of moves, whether or not the knot survives it.
-/

namespace KnotGame
namespace NoRecurrence

open KnotGame.Ternary

variable {x : ℝ} {m n : ℕ}

/-! ## The dyadic level is determined by the point -/

private lemma dyadic_level_lt_absurd (hmn : m < n) (hm : Dyadic m x) (hn : Dyadic n x) :
    False := by
  obtain ⟨k, hk, rfl⟩ := hm
  obtain ⟨j, hj, hx⟩ := hn
  have h2m : ((2 : ℝ) ^ (m + 1)) ≠ 0 := by positivity
  have h2n : ((2 : ℝ) ^ (n + 1)) ≠ 0 := by positivity
  have hR : (k : ℝ) * 2 ^ (n + 1) = (j : ℝ) * 2 ^ (m + 1) := by
    field_simp at hx
    linarith
  have hZ : (k : ℤ) * 2 ^ (n + 1) = (j : ℤ) * 2 ^ (m + 1) := by exact_mod_cast hR
  -- write `n + 1 = (m + 1) + d` with `d ≥ 1` and cancel `2 ^ (m+1)`
  obtain ⟨d, hd⟩ : ∃ d : ℕ, n + 1 = (m + 1) + (d + 1) := ⟨n - m - 1, by omega⟩
  rw [hd, pow_add] at hZ
  have hcancel : (k : ℤ) * 2 ^ (d + 1) = j := by
    have h2 : ((2 : ℤ) ^ (m + 1)) ≠ 0 := by positivity
    have h3 : (2 ^ (m + 1) : ℤ) * ((k : ℤ) * 2 ^ (d + 1)) = (2 ^ (m + 1) : ℤ) * j := by
      linarith [hZ]
    exact mul_left_cancel₀ h2 h3
  have hjeven : Even j := by
    refine ⟨k * 2 ^ d, ?_⟩
    rw [← hcancel, pow_succ]
    ring
  exact (Int.not_even_iff_odd.mpr hj) hjeven

/-- **The dyadic level of a point is determined by the point.**  A real number is
an odd multiple of `2 ^ -(n+1)` for at most one `n`. -/
theorem dyadic_level_unique (hm : Dyadic m x) (hn : Dyadic n x) : m = n := by
  rcases lt_trichotomy m n with h | h | h
  · exact absurd (dyadic_level_lt_absurd h hm hn) not_false
  · exact h
  · exact absurd (dyadic_level_lt_absurd h hn hm) not_false

/-! ## Moving a dyadic point -/

/-- A block of `b.length` moves raises the dyadic level by `b.length`. -/
theorem dyadic_posAfter_of_dyadic (hx : Dyadic n x) (b : List Move) :
    Dyadic (n + b.length) (posAfter (3 / 2 : ℝ) x b) := by
  induction b generalizing n x with
  | nil => simpa using hx
  | cons c b ih =>
      have := ih (dyadic_act hx c)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

/-- A knot of a run sits at a dyadic point whose level is its age. -/
theorem dyadic_of_knotAt {w : List Move} {a : ℕ} (h : KnotAt (3 / 2 : ℝ) w a x) :
    Dyadic a x := by
  obtain ⟨-, s, -, rfl, -, rfl⟩ := h
  exact dyadic_posAfter s

/-! ## T30 -/

/-- **T30, core form** (paper `prop:norecur`).  The position of a knot
determines how long it has been travelling: two blocks of moves that carry a
knot position to the same place have the same length. -/
theorem posAfter_length_eq (hx : Dyadic n x) {u v : List Move}
    (h : posAfter (3 / 2 : ℝ) x u = posAfter (3 / 2 : ℝ) x v) : u.length = v.length := by
  have hu := dyadic_posAfter_of_dyadic hx u
  have hv := dyadic_posAfter_of_dyadic hx v
  rw [h] at hu
  have := dyadic_level_unique hu hv
  omega

/-- **T30** (paper `prop:norecur`).  At `λ = 3/2` a nonempty block of moves never
returns a knot to the position it started from. -/
theorem no_recurrence (hx : Dyadic n x) {b : List Move} (hb : b ≠ []) :
    posAfter (3 / 2 : ℝ) x b ≠ x := by
  intro h
  have : b.length = ([] : List Move).length :=
    posAfter_length_eq hx (u := b) (v := []) (by simpa using h)
  exact hb (List.eq_nil_of_length_eq_zero (by simpa using this))

/-- **T30, for a knot of a run.**  No knot of a reachable configuration is
returned to its own position by a nonempty block of moves. -/
theorem no_recurrence_knotAt {w : List Move} {a : ℕ}
    (hk : KnotAt (3 / 2 : ℝ) w a x) {b : List Move} (hb : b ≠ []) :
    posAfter (3 / 2 : ℝ) x b ≠ x :=
  no_recurrence (dyadic_of_knotAt hk) hb

/-- **T30, trajectory form.**  The successive positions of a knot are pairwise
distinct: distinct prefixes of a block of moves carry it to distinct places. -/
theorem positions_pairwise_ne (hx : Dyadic n x) {i j : ℕ} (b : List Move)
    (hi : i ≤ b.length) (hj : j ≤ b.length) (hij : i ≠ j) :
    posAfter (3 / 2 : ℝ) x (b.take i) ≠ posAfter (3 / 2 : ℝ) x (b.take j) := by
  intro h
  have := posAfter_length_eq hx h
  rw [List.length_take, List.length_take] at this
  omega

/-- **T30, no position of the game is visited twice.**  The positions of the
knot born at `1/2` after `i` and after `j` moves agree only if `i = j`; this is
the statement that no knot ever occupies the same position twice. -/
theorem knot_positions_injective (b : List Move) :
    Function.Injective
      (fun i : Fin (b.length + 1) => posAfter (3 / 2 : ℝ) (1 / 2 : ℝ) (b.take (i : ℕ))) := by
  intro i j h
  simp only at h
  by_contra hne
  exact positions_pairwise_ne (n := 0) dyadic_half b (i := (i : ℕ)) (j := (j : ℕ))
    (Nat.lt_succ_iff.mp i.2) (Nat.lt_succ_iff.mp j.2) (fun hc => hne (Fin.ext hc)) h

/-! ## No block of moves is the identity -/

/-- **`no_identity_block`** (paper §12, the corollary cited against a candidate
mechanism for `prop:twostep`).  A nonempty block of moves does not act as the
identity on any knot of a reachable configuration. -/
theorem no_identity_block {w : List Move} (b : List Move) (hb : b ≠ [])
    (hx : x ∈ run (3 / 2 : ℝ) w) : posAfter (3 / 2 : ℝ) x b ≠ x := by
  obtain ⟨a, ha⟩ := (mem_run_iff (by norm_num : (1:ℝ) < 3 / 2) w x).mp hx
  exact no_recurrence_knotAt ha hb

/-- **`no_identity_block`, configuration form.**  A nonempty block of moves never
acts as the identity on a nonempty reachable configuration. -/
theorem no_identity_block_config {w : List Move} (b : List Move) (hb : b ≠ [])
    (hne : (run (3 / 2 : ℝ) w).Nonempty) :
    ¬ ∀ y ∈ run (3 / 2 : ℝ) w, posAfter (3 / 2 : ℝ) y b = y := by
  obtain ⟨y, hy⟩ := hne
  exact fun hall => no_identity_block b hb hy (hall y hy)

end NoRecurrence
end KnotGame
