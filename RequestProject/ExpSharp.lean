import RequestProject.ExpSharpData

/-!
# A sharper exponential lower bound at `lam = 3/2` (round 7)

`RequestProject.ExpLower` gives `2 ^ (m / 5) ≤ K (3/2) m`, i.e. growth
`2^(1/5) ≈ 1.1487` per step.  Using the multiplicity machinery of
`RequestProject.ExpMulti` with `15` words of length `12` instead of two words of
length `5`, the same covering argument gives

  `15 ^ (m / 12) ≤ K (3/2) m`,

i.e. growth `15^(1/12) ≈ 1.2532` per step.  The measured growth is
`(2/lam)^m = (4/3)^m ≈ 1.3333^m`, so this is closer to, but still below, the
observed rate.

## Conventions (SCRUPLES)

* Same doubling interval `J = [1/4, 3/4]` as in `ExpLower`, and the same
  exact-rational check (`decide +kernel`) — at the single parameter `3/2` the
  enclosure of `ExpCert.iok` is an exact computation.
* The certificate was found by a greedy search (`scripts/gen_expsharp.py`); the
  search is not trusted, only its output, which the kernel re-checks.
* The exponent uses natural division, so the bound is trivial for `m < 12`.  It
  is stronger than `ExpLower.two_pow_le_K` in rate (`1.2532` against `1.1487`)
  but not uniformly in `m`: for small `m` the coarser division can make either
  bound the larger.
* `15` is the largest multiplicity the greedy search reached at length `12` on
  this interval; it is not claimed to be maximal.
-/

namespace KnotGame
namespace ExpSharp

open KnotGame.Branching KnotGame.ExpCount KnotGame.ExpCert KnotGame.ExpMulti
open KnotGame.ExpMultiCert

/-- The check of one group of cells: `15` distinct words of length `12` per
cell, each with its enclosure inside `J`.  The kernel runs one group at a
time. -/
abbrev P : MCell → Bool := mcellOK (3/2) (3/2) (1/4) (3/4) 12 15

lemma cells_chained : chained (1/4) cells (3/4) = true := by decide +kernel

lemma cellsG0_ok : cellsG0.all P = true := by decide +kernel
lemma cellsG1_ok : cellsG1.all P = true := by decide +kernel
lemma cellsG2_ok : cellsG2.all P = true := by decide +kernel
lemma cellsG3_ok : cellsG3.all P = true := by decide +kernel
lemma cellsG4_ok : cellsG4.all P = true := by decide +kernel
lemma cellsG5_ok : cellsG5.all P = true := by decide +kernel

lemma cells_ok : cells.all P = true := by
  simp only [cells, List.all_append, cellsG0_ok, cellsG1_ok, cellsG2_ok, cellsG3_ok,
    cellsG4_ok, cellsG5_ok, Bool.and_self]

/-- **Multiplicity `15` at `lam = 3/2`.**  Every `x ∈ [1/4, 3/4]` admits `15`
distinct branch words of length `12` whose images again lie in `[1/4, 3/4]`. -/
theorem mdoubling_three_halves : MDoubling (3/2 : ℝ) (1/4 : ℝ) (3/4 : ℝ) 12 15 := by
  have h := mdoubling_of_cert (l0 := 3/2) (l1 := 3/2) (a := 1/4) (b := 3/4) (T := 12) (k := 15)
    (lam := (3/2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) cells_chained (by decide)
    cells_ok
  simpa using h

/-- **A sharper exponential lower bound at `lam = 3/2`.**  The number of
length-`m` branch words along which `1/2` survives is at least `15 ^ (m / 12)`. -/
theorem fifteen_pow_le_K (m : ℕ) : 15 ^ (m / 12) ≤ K (3/2 : ℝ) m :=
  pow_le_K_of_mdoubling (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) mdoubling_three_halves m

end ExpSharp
end KnotGame
