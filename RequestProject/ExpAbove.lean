import RequestProject.ExpAboveChecks

/-!
# T32 — exponential kind counts ABOVE the golden ratio (round 10)

Every earlier exponential lower bound in this development lives below the golden
ratio: round 4's branching lemmas need `λ² < λ + 1`, and round 7's certificates
cover `[1000/667, 8/5]`.  Nothing in the *covering* argument needs `λ < φ`,
though, and this file certifies a doubling bound on a rational window **above**
the golden ratio containing `√3`:

  `2 ^ (m / Tbound) ≤ K lam m`  for every `lam ∈ [3457/2000, 4331/2500]`,

and in particular at `lam = √3` itself (`two_pow_le_K_sqrt_three`).

The certificate uses the *variable-return-time* form of the doubling hypothesis
(`RequestProject.ExpVar`): the two words issued from a point may have different
lengths, provided they diverge and both are at most `Tbound`.  This is what
makes the argument possible here.  Above `φ` the two-cycle
`{1/(λ+1), λ/(λ+1)}` of `RequestProject.Branching` sits outside the branching
window, so returns are slow and irregular, and no certificate with two words of a
*common* length was found at any kernel-feasible size — see the infeasibility
report in `CENSUS-round10.md`.

## Conventions (SCRUPLES)

* **The commissioned window `[17/10, 7/4]` is NOT certified.**  What is
  certified is the rational window `[3457/2000, 4331/2500] = [1.7285, 1.7324]`, which contains
  `√3 = 1.7320508…` (`sqrt_three_mem_window`) and lies entirely above the golden
  ratio (`golden_lt_window`).  The obstruction is reported in full in
  `CENSUS-round10.md`: outside this window the greedy search hits parameters
  (near `1.7282`, `1.7325`, `1.7328`) at which the cells of the tiling shrink to
  nothing — the shadow of the two-cycle — and the certificate could not be
  completed at any subdivision depth tried.
* The core interval is `J = [43/100, 57/100]`, which is *inside* the branching
  window `(1 − 1/λ, 1/λ)` for every parameter of the window.  It has to be: for
  the wider `J = [2/5, 3/5]` the search fails, since points of `J` outside the
  branching window can lie on orbits that never branch at all (the survivor set
  of the hole is nonempty above `φ`).
* Interval arithmetic is carried out in the point *and* in the parameter, as in
  round 7, so one certificate serves a whole interval of parameters; the window
  is split into parameter cells adaptively.
* The rate `2 ^ (1/Tbound)` is governed by the *worst* return time in the
  certificate; most cells return much sooner.  No sharpness is claimed.
* The search (`scripts/gen_expabove.py`, `scripts/expvar_search.py`) is not
  trusted: the kernel re-checks every cell in
  `RequestProject.ExpAboveChecks`.
-/

namespace KnotGame
namespace ExpAbove

open KnotGame.Branching KnotGame.ExpCount KnotGame.ExpCert KnotGame.ExpVar

/-- The certified parameter window, lower end. -/
noncomputable def L0 : ℝ := 3457/2000

/-- The certified parameter window, upper end. -/
noncomputable def L1 : ℝ := 4331/2500

/-- **The variable-time doubling property on the window.**  For every
`lam ∈ [3457/2000, 4331/2500]`, every `x ∈ [43/100, 57/100]` has two
diverging branch words of length at most `Tbound` whose images again lie in
`[43/100, 57/100]`. -/
theorem vdoubling_above {lam : ℝ} (h0 : L0 ≤ lam) (h1 : lam ≤ L1) :
    VDoubling lam (43/100 : ℝ) (57/100 : ℝ) Tbound := by
  have h0' : (((3457/2000 : ℚ) : ℚ) : ℝ) ≤ lam := by push_cast; exact h0
  have h1' : lam ≤ (((4331/2500 : ℚ) : ℚ) : ℝ) := by push_cast; exact h1
  have hne : pcells ≠ [] := by
    simp only [pcells, pcellsG0]
    exact List.append_ne_nil_of_left_ne_nil (List.cons_ne_nil _ _) _
  have h := vdoubling_of_window (a' := 43/100) (b' := 57/100) (T := Tbound)
    pcells_chained hne pcells_ok h0' h1'
  simpa using h

/-- **T32 — an exponential lower bound for the kind count above the golden
ratio.**  For every parameter in the window `[3457/2000, 4331/2500]`, the
number of length-`m` branch words along which `1/2` survives is at least
`2 ^ (m / Tbound)`. -/
theorem two_pow_le_K_above {lam : ℝ} (h0 : L0 ≤ lam) (h1 : lam ≤ L1) (m : ℕ) :
    2 ^ (m / Tbound) ≤ K lam m := by
  have hlam1 : (1 : ℝ) < lam := lt_of_lt_of_le (by norm_num [L0]) h0
  have hlam2 : lam < 2 := lt_of_le_of_lt h1 (by norm_num [L1])
  exact two_pow_le_K_of_vdoubling hlam1 hlam2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (vdoubling_above h0 h1) m

/-- The window lies entirely above the golden ratio. -/
theorem golden_lt_window : Real.goldenRatio < L0 := by
  have h5 : Real.sqrt 5 < 2.3 := by
    have : Real.sqrt 5 < Real.sqrt (2.3 ^ 2) := by
      apply Real.sqrt_lt_sqrt (by norm_num)
      norm_num
    rwa [Real.sqrt_sq (by norm_num)] at this
  rw [L0]
  unfold Real.goldenRatio
  linarith

/-- `√3` lies in the certified window. -/
theorem sqrt_three_mem_window : L0 ≤ Real.sqrt 3 ∧ Real.sqrt 3 ≤ L1 := by
  constructor
  · rw [L0, show ((3457/2000 : ℝ)) = Real.sqrt ((3457/2000 : ℝ) ^ 2) by
      rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  · rw [L1, show ((4331/2500 : ℝ)) = Real.sqrt ((4331/2500 : ℝ) ^ 2) by
      rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)

/-- **T32 at `√3`.**  The kind count at `lam = √3` — a parameter above the
golden ratio — is at least `2 ^ (m / Tbound)`. -/
theorem two_pow_le_K_sqrt_three (m : ℕ) : 2 ^ (m / Tbound) ≤ K (Real.sqrt 3) m :=
  two_pow_le_K_above sqrt_three_mem_window.1 sqrt_three_mem_window.2 m

/-- The kind count is unbounded at every parameter of the window; in particular
at `√3`. -/
theorem K_unbounded_above {lam : ℝ} (h0 : L0 ≤ lam) (h1 : lam ≤ L1) (C : ℕ) :
    ∃ m : ℕ, C < K lam m := by
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (R := ℕ) C (by norm_num : (1:ℕ) < 2)
  refine ⟨Tbound * j, lt_of_lt_of_le hj ?_⟩
  have hT : (0 : ℕ) < Tbound := by norm_num [Tbound]
  have : Tbound * j / Tbound = j := by
    rw [Nat.mul_comm]
    exact Nat.mul_div_cancel j hT
  simpa [this] using two_pow_le_K_above h0 h1 (Tbound * j)

end ExpAbove
end KnotGame
