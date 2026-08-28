import RequestProject.Littlewood

/-!
# Immortal births (paper `prop:immortal32`)

Proposition `prop:immortal32` reads: if some control sequence has infinitely
many indices carrying the birth move whose knots never meet the control, then
`N_{3/2} = ∞`.  The paper's control sequences are elements of `{0,1,2}^ℕ` with
the digit `1` for the birth move; here a control sequence is a function
`ℕ → Move` and the birth move is `M`, the coding being the one of
`RequestProject.Ternary`.

The birth at time `t` is **immortal** (`ImmortalBirth`) when the letter at `t`
is `M` and the knot born there survives every finite block of later letters.
The proof is the paper's: immortal knots are simultaneously present, and
distinct by `lem:distinct`, which is exactly what the suffix decomposition
`card_run` counts.  Nothing here is special to `λ = 3/2`: the statement is
proved for every `λ > 1` and then specialised (`N_unbounded_of_immortal`,
`N_unbounded_of_immortal_three_halves`).
-/

namespace KnotGame
namespace Immortal

open scoped Classical

variable {lam : ℝ}

/-- The control sequence shifted one step forward. -/
def shiftSeq (v : ℕ → Move) : ℕ → Move := fun i => v (i + 1)

lemma prefixWord_cons (v : ℕ → Move) (n : ℕ) :
    prefixWord v (n + 1) = v 0 :: prefixWord (shiftSeq v) n := by
  simp [prefixWord, List.range_succ_eq_map, shiftSeq, Function.comp_def]

/-- The birth at time `t` of the control sequence `v` is **immortal**: the
letter at `t` is `M`, and the knot born there survives every finite block of
later letters. -/
def ImmortalBirth (lam : ℝ) (v : ℕ → Move) (t : ℕ) : Prop :=
  v t = Move.M ∧ ∀ n, survivesWord lam (1/2) (prefixWord (shiftSeq^[t + 1] v) n)

lemma immortalBirth_succ (v : ℕ → Move) (t : ℕ) :
    ImmortalBirth lam v (t + 1) ↔ ImmortalBirth lam (shiftSeq v) t := by
  unfold ImmortalBirth
  rw [Function.iterate_succ_apply]
  rfl

/-- Every immortal birth before time `n` contributes a knot to the run of the
first `n` letters. -/
lemma card_immortal_le_births : ∀ (n : ℕ) (v : ℕ → Move),
    ((Finset.range n).filter (fun t => ImmortalBirth lam v t)).card
      ≤ births lam (prefixWord v n)
  | 0, v => by simp
  | (n + 1), v => by
      have ih := card_immortal_le_births n (shiftSeq v)
      have hcard : ((Finset.range (n + 1)).filter (fun t => ImmortalBirth lam v t)).card
          = ((Finset.range n).filter (fun t => ImmortalBirth lam (shiftSeq v) t)).card
            + (if ImmortalBirth lam v 0 then 1 else 0) := by
        rw [Finset.card_filter, Finset.card_filter, Finset.sum_range_succ']
        congr 1
      rw [hcard, prefixWord_cons, births_cons]
      by_cases h0 : ImmortalBirth lam v 0
      · have hM : v 0 = Move.M := h0.1
        have hs : survivesWord lam (1/2) (prefixWord (shiftSeq v) n) := by
          have := h0.2 n
          simpa using this
        rw [if_pos h0, if_pos ⟨hM, hs⟩]
        omega
      · rw [if_neg h0]
        omega

/-- **`prop:immortal32`.**  A control sequence with infinitely many immortal
births makes the knot count unbounded. -/
theorem N_unbounded_of_immortal (h : 1 < lam) (v : ℕ → Move)
    (H : {t | ImmortalBirth lam v t}.Infinite) : ∀ k : ℕ, ∃ n : ℕ, k ≤ N lam n := by
  intro k
  obtain ⟨T, hTsub, hTcard⟩ := H.exists_subset_card_eq k
  classical
  set n : ℕ := (T.sup id) + 1 with hn
  have hTsub' : T ⊆ (Finset.range n).filter (fun t => ImmortalBirth lam v t) := by
    intro t ht
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hTsub ht⟩
    have hle : id t ≤ T.sup id := Finset.le_sup ht
    simp only [id] at hle
    omega
  have h1 : k ≤ births lam (prefixWord v n) :=
    le_trans (by rw [← hTcard]; exact Finset.card_le_card hTsub')
      (card_immortal_le_births n v)
  refine ⟨n, ?_⟩
  have h2 := births_le_N h (prefixWord v n)
  rw [prefixWord_length] at h2
  omega

/-- **`prop:immortal32` at `λ = 3/2`.** -/
theorem N_unbounded_of_immortal_three_halves (v : ℕ → Move)
    (H : {t | ImmortalBirth (3/2 : ℝ) v t}.Infinite) :
    ∀ k : ℕ, ∃ n : ℕ, k ≤ N (3/2 : ℝ) n :=
  N_unbounded_of_immortal (by norm_num) v H

end Immortal
end KnotGame
