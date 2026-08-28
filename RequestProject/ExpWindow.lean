import RequestProject.ExpWindowData

/-!
# A uniform exponential lower bound on the parameter window (round 7)

`RequestProject.ExpLower` proves `2 ^ (m / 5) ≤ K (3/2) m` at the single
parameter `lam = 3/2`.  Here the same covering argument is run *uniformly* over
the parameter window

  `lam ∈ [1000/667, 8/5]`,

which is the window used throughout the earlier rounds.  The certificate
(`RequestProject.ExpWindowData`) splits the window into `24` parameter cells; on
each of them a list of interval cells tiles `J = [1/5, 4/5]`, each carrying two
distinct branch words of a common length `T ≤ 8` whose *enclosures* — computed
with interval arithmetic in the parameter as well as in the point — stay inside
`J`.  The result is

  `2 ^ (m / 8) ≤ K lam m`  for every `lam` in the window.

## Conventions (SCRUPLES)

* `J = [1/5, 4/5]` is a single interval used for all parameter cells; it must
  contain `1/2`, and be inside `(0,1)`, which it is.  It is wider than the
  `[1/4, 3/4]` used at `3/2`, because a wider `J` is what makes one certificate
  survive an interval of parameters.
* The word length `T` varies by parameter cell (`6`, `7` or `8`); the exponent is
  normalised down to the worst case `m / 8`, so the stated rate `2 ^ (1/8)` is
  weaker than what most of the window actually enjoys.
* The window is covered *exactly*: `chained` closes the last cell at `8/5`, and
  both endpoints are included.  The certificate search did not succeed past
  `8/5` with `T ≤ 8`.
-/

namespace KnotGame
namespace ExpWindow

open KnotGame.Branching KnotGame.ExpCount KnotGame.ExpCert

/-- Validity of one parameter cell against the target interval `[a,b]`: a
positive parameter range, a positive word length at most `8`, and a nonempty
chained list of cells tiling `[a,b]`, all valid. -/
def lamCellOK (a b : ℚ) (c : LamCell) : Bool :=
  decide (0 < c.1) && decide (0 < c.2.2.1) && decide (c.2.2.1 ≤ 8) &&
    chained a c.2.2.2 b && decide (c.2.2.2 ≠ []) &&
    c.2.2.2.all (cellOK c.1 c.2.1 a b c.2.2.1)

lemma lamCells_chained : chained (1000/667) lamCells (8/5) = true := by decide +kernel

lemma lamCells_ok : lamCells.all (lamCellOK (1/5) (4/5)) = true := by decide +kernel

/-- **The doubling property, uniformly on the parameter window.**  For every
`lam ∈ [1000/667, 8/5]` there is a word length `T ≤ 8` such that every
`x ∈ [1/5, 4/5]` has two distinct branch words of length `T` whose images again
lie in `[1/5, 4/5]`. -/
theorem doubling_window {lam : ℝ} (h0 : (1000/667 : ℝ) ≤ lam) (h1 : lam ≤ 8/5) :
    ∃ T : ℕ, 0 < T ∧ T ≤ 8 ∧ Doubling lam (1/5 : ℝ) (4/5 : ℝ) T := by
  have h0' : (((1000/667 : ℚ) : ℚ) : ℝ) ≤ lam := by push_cast; exact h0
  have h1' : lam ≤ (((8/5 : ℚ) : ℚ) : ℝ) := by push_cast; exact h1
  obtain ⟨c, hc, hp, hq⟩ := exists_cell lamCells_chained (by decide) h0' h1'
  have hok : lamCellOK (1/5) (4/5) c = true := (List.all_eq_true.1 lamCells_ok) c hc
  simp only [lamCellOK, Bool.and_eq_true, decide_eq_true_eq, ne_eq] at hok
  obtain ⟨⟨⟨⟨⟨hl0, hT0⟩, hT8⟩, hch⟩, hne⟩, hall⟩ := hok
  refine ⟨c.2.2.1, hT0, hT8, ?_⟩
  have hd := doubling_of_cert (l0 := c.1) (l1 := c.2.1) (a := 1/5) (b := 4/5)
    (T := c.2.2.1) (lam := lam) hl0 hp hq hch hne hall
  simpa using hd

/-- **A uniform exponential lower bound for the kind count.**  For every
parameter in the window `[1000/667, 8/5]`, the number of length-`m` branch words
along which `1/2` survives is at least `2 ^ (m / 8)`. -/
theorem two_pow_le_K_window {lam : ℝ} (h0 : (1000/667 : ℝ) ≤ lam) (h1 : lam ≤ 8/5)
    (m : ℕ) : 2 ^ (m / 8) ≤ K lam m := by
  obtain ⟨T, hT0, hT8, hdb⟩ := doubling_window h0 h1
  have hlam1 : (1 : ℝ) < lam := lt_of_lt_of_le (by norm_num) h0
  have hlam2 : lam < 2 := lt_of_le_of_lt h1 (by norm_num)
  have hmain : 2 ^ (m / T) ≤ K lam m :=
    two_pow_le_K_of_doubling hlam1 hlam2 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hdb m
  exact le_trans (Nat.pow_le_pow_right (by norm_num) (Nat.div_le_div_left hT8 hT0)) hmain

end ExpWindow
end KnotGame
