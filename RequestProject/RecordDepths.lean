import RequestProject.TwoStep

/-!
# Exact record depths at `λ = 3/2` for `k ≤ 4`

`TwoStep.lean` certifies the upper bounds `d_{3/2}(k) ≤ |w|` supplied by
explicit record words.  This file certifies the matching *lower* bounds for the
small values of `k`, by exhausting all words of the relevant length in the exact
integer model of `RunRational.lean`:

* `N (3/2) 2 ≤ 1`, hence `d_{3/2}(2) = 3`;
* `N (3/2) 4 ≤ 2`, hence `d_{3/2}(3) = 5`;
* `N (3/2) 8 ≤ 3`, hence `d_{3/2}(4) = 9`.

The exhaustion is a kernel `decide` over the `3^n` words of length `n`
(`allWords`), which is why it stops at `n = 8`: the next interesting length,
`n = 18` (for `d_{3/2}(5) = 19`), has `3^18 ≈ 4·10^8` words, and the
deduplicated breadth-first search that would replace the enumeration is not
kernel-feasible either.  Beyond `k = 4` only the upper bounds of `TwoStep.lean`
are certified.
-/

namespace KnotGame

set_option maxRecDepth 100000

/-! ## Enumerating words -/

/-- All words of a given length, in the order `L < M < R` on the first letter. -/
def allWords : ℕ → List (List Move)
  | 0 => [[]]
  | n + 1 => (allWords n).flatMap (fun w => [Move.L :: w, Move.M :: w, Move.R :: w])

/-- Every word occurs in the enumeration of words of its own length. -/
lemma mem_allWords : ∀ w : List Move, w ∈ allWords w.length
  | [] => by simp [allWords]
  | c :: w => by
      have hw : w ∈ allWords w.length := mem_allWords w
      refine List.mem_flatMap.2 ⟨w, hw, ?_⟩
      cases c <;> simp

/-- If every word of length `n` produces at most `k` knots in the integer model,
then `N (3/2) n ≤ k`. -/
lemma N_le_of_allWords {n k : ℕ}
    (h : ((allWords n).all (fun w => (runZ w).card ≤ k)) = true) :
    N (3/2 : ℝ) n ≤ k := by
  refine Finset.sup_le ?_
  intro v _
  rw [card_run_eq_card_runZ]
  have hv : List.ofFn v ∈ allWords (List.ofFn v).length := mem_allWords _
  rw [List.length_ofFn] at hv
  simpa using List.all_eq_true.1 h _ hv

/-- `N` is monotone (the iterated form of the inherited `N_mono`). -/
lemma N_le_of_le {lam : ℝ} (h : 1 < lam) {m n : ℕ} (hmn : m ≤ n) : N lam m ≤ N lam n := by
  induction n with
  | zero => simpa using le_of_eq (by rw [Nat.le_zero.1 hmn])
  | succ n ih =>
      rcases Nat.lt_or_ge m (n + 1) with hlt | hge
      · exact le_trans (ih (Nat.lt_succ_iff.1 hlt)) (N_mono h n)
      · rw [le_antisymm hmn hge]

/-- The lower bound on a record depth supplied by an exhaustion. -/
lemma le_d_of_N_le {k n : ℕ} (hk : k ≤ N (3/2 : ℝ) (n + 1))
    (h : N (3/2 : ℝ) n ≤ k - 1) (hk0 : 0 < k) : n + 1 ≤ d (3/2 : ℝ) k := by
  by_contra hcon
  push_neg at hcon
  have hne : d (3/2 : ℝ) k ∈ {m | k ≤ N (3/2 : ℝ) m} :=
    Nat.sInf_mem ⟨n + 1, hk⟩
  have hle : N (3/2 : ℝ) (d (3/2 : ℝ) k) ≤ N (3/2 : ℝ) n :=
    N_le_of_le one_lt_three_halves (Nat.lt_succ_iff.1 hcon)
  have : k ≤ k - 1 := le_trans hne (le_trans hle h)
  omega

/-! ## The exhaustions -/

theorem N_two_le_one : N (3/2 : ℝ) 2 ≤ 1 := N_le_of_allWords (by decide +kernel)

theorem N_four_le_two : N (3/2 : ℝ) 4 ≤ 2 := N_le_of_allWords (by decide +kernel)

theorem N_eight_le_three : N (3/2 : ℝ) 8 ≤ 3 := N_le_of_allWords (by decide +kernel)

/-! ## The exact depths -/

/-- `d_{3/2}(2) = 3`: the record word `record2` is as short as possible. -/
theorem d_two_eq_three : d (3/2 : ℝ) 2 = 3 := by
  refine le_antisymm d_le_three ?_
  refine le_d_of_N_le (n := 2) (k := 2) ?_ N_two_le_one (by norm_num)
  have := card_run_le_N one_lt_three_halves record2
  rw [card_run_record2] at this
  exact this

/-- `d_{3/2}(3) = 5`: the record word `record3` is as short as possible. -/
theorem d_three_eq_five : d (3/2 : ℝ) 3 = 5 := by
  refine le_antisymm d_le_five ?_
  refine le_d_of_N_le (n := 4) (k := 3) ?_ N_four_le_two (by norm_num)
  have := card_run_le_N one_lt_three_halves record3
  rw [card_run_record3] at this
  exact this

/-- `d_{3/2}(4) = 9`: the record word `record4` is as short as possible. -/
theorem d_four_eq_nine : d (3/2 : ℝ) 4 = 9 := by
  refine le_antisymm d_le_nine ?_
  refine le_d_of_N_le (n := 8) (k := 4) ?_ N_eight_le_three (by norm_num)
  have := card_run_le_N one_lt_three_halves record4
  rw [card_run_record4] at this
  exact this

end KnotGame
