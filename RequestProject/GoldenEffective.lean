import RequestProject.Golden
import RequestProject.Gaps

/-!
# The effective bound at the golden ratio (round 2, Target T6)

Round 1 certified that at `lam = phi` every reachable configuration is the image
under `p` of a subset of the five-point orbit
`{1 - phi/2, (phi-1)/2, 1/2, (3-phi)/2, phi/2}` (`KnotGame.Golden.run_eq`).
The smallest distance between two of those five points is
`delta0 = phi - 3/2 = (√5 - 2)/2`.  The identity `phi ^ 2 = phi + 1` gives
`phi ^ 5 = 5 * phi + 3` and hence the exact evaluation

  `phi ^ 5 * (phi - 3/2) = (phi + 1)/2 = phi ^ 2 / 2 ≥ 1`,

so the window `W = 5` satisfies the hypothesis of the scheduling theorem
`KnotGame.N_le_of_separated`, with no numerical estimate anywhere.  The bound is
`N_phi ≤ 5 + ⌈5/2⌉ + 1 = 9`.

**Consistency remark.**  Round 1 proved the sharp value `sup N phi = 2`
(`KnotGame.Golden.sup_N_phi`).  The bound `9` proved here is strictly weaker;
it is obtained by an independent argument (order, gap law, and pigeonhole over a
window of moves) that never inspects the set of reachable configurations, and
that is the point of the exercise.
-/

namespace KnotGame
namespace Golden

/-- The smallest distance between two points of the five-point orbit of `1/2` at
the golden ratio: `delta0 = phi - 3/2 = (√5 - 2)/2 ≈ 0.1180`. -/
noncomputable def delta0 : ℝ := phi - 3/2

lemma delta0_pos : 0 < delta0 := by
  have := phi_gt
  simp only [delta0]
  linarith

/-- `phi ^ 5 = 5 * phi + 3`, an exact consequence of `phi ^ 2 = phi + 1`. -/
lemma phi_pow_five : phi ^ 5 = 5 * phi + 3 := by
  linear_combination (phi ^ 3 + phi ^ 2 + 2 * phi + 3) * phi_sq

/-- The exact identity behind the choice `W = 5`:
`phi ^ 5 * delta0 = (phi + 1)/2 = phi ^ 2 / 2`. -/
lemma phi_pow_five_mul_delta0 : phi ^ 5 * delta0 = phi ^ 2 / 2 := by
  rw [delta0, phi_pow_five]
  linear_combination (9/2 : ℝ) * phi_sq

/-- The window hypothesis of the scheduling theorem holds at `W = 5`. -/
lemma window_bound : 1 ≤ phi ^ 5 * delta0 := by
  rw [phi_pow_five_mul_delta0, phi_sq]
  have := phi_gt
  linarith

/-- Two distinct points of the five-point orbit are at distance at least
`delta0`. -/
lemma p_sep (i j : Fin 5) (hij : i ≠ j) : delta0 ≤ |p i - p j| := by
  have h1 := phi_gt
  have h2 := phi_lt
  have key : delta0 ≤ p i - p j ∨ delta0 ≤ p j - p i := by
    simp only [delta0]
    fin_cases i <;> fin_cases j <;> simp [p] at hij ⊢ <;>
      first
        | (left; linarith)
        | (right; linarith)
  rcases key with hk | hk
  · exact le_trans hk (le_abs_self _)
  · refine le_trans hk ?_
    rw [abs_sub_comm]
    exact le_abs_self _

/-- Every two distinct coexisting knots at the golden ratio are at distance at
least `delta0`: all knots lie in the five-point orbit, and coexisting knots are
distinct. -/
theorem run_sep (w : List Move) :
    ∀ x ∈ run phi w, ∀ y ∈ run phi w, x ≠ y → delta0 ≤ |x - y| := by
  intro x hx y hy hxy
  rw [run_eq] at hx hy
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
  exact p_sep i j (fun hij => hxy (by rw [hij]))

/-- **T6 (golden ratio, effective bound).**  At `lam = phi` the scheduling
theorem with `delta = phi - 3/2` and `W = 5` gives `N phi n ≤ 9` for every `n`.

This is strictly weaker than the sharp value `2` certified in round 1
(`sup_N_phi`); the argument is independent of it. -/
theorem N_phi_le_nine (n : ℕ) : N phi n ≤ 9 := by
  have := N_le_of_separated (lam := phi) one_lt_phi (delta := delta0) 5 window_bound run_sep n
  norm_num at this
  exact this

/-- The effective bound in the form "every run of any length has at most nine
simultaneous knots at the golden ratio". -/
theorem card_run_phi_le_nine (w : List Move) : (run phi w).card ≤ 9 := by
  have := scheduling_bound (lam := phi) one_lt_phi (delta := delta0) 5 window_bound w
    (fun u _ _ => run_sep u)
  norm_num at this
  exact this

end Golden
end KnotGame
