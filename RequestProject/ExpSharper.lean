import RequestProject.ExpSharperData

/-!
# T31 — a sharper exponential lower bound at `lam = 3/2` (round 10)

Round 7 (`RequestProject.ExpSharp`) certified `15 ^ (m / 12) ≤ K (3/2) m`, a
growth rate of `15 ^ (1/12) ≈ 1.25316` per step.  Reusing the same `MDoubling`
machinery of `RequestProject.ExpMulti` with a longer word length and a wider
core interval, this file certifies

  `26 ^ (m / 14) ≤ K (3/2) m`,

a rate of `26 ^ (1/14) ≈ 1.26203` per step (`sharper_rate`, which states the
comparison `15 ^ 14 < 26 ^ 12` — the integer form of
`15 ^ (1/12) < 26 ^ (1/14)` — as a certified inequality).  The measured growth
is `(2/lam) ^ m = (4/3) ^ m ≈ 1.33333 ^ m`, so this is closer to, but still
below, the observed rate.

## Conventions (SCRUPLES)

* The core interval is `J = [1/6, 5/6]`, wider than the `[1/4, 3/4]` of round 7.
  At `lam = 3/2` the multiplicity attainable at length `14` is the same (`26`)
  on both, but the wider interval needs fewer cells (`747` against `1016`), so
  the kernel check is cheaper.  `J` must satisfy `0 < a ≤ 1/2 ≤ b < 1`, which it
  does.
* Everything is checked at the *single* parameter `3/2`, where
  `ExpCert.iok`'s interval arithmetic is exact rational arithmetic
  (`l0 = l1 = 3/2`).
* The certificate was found by the greedy search of
  `scripts/gen_expsharper.py` (with `scripts/expcert_dfs.py`); the search is not
  trusted, only its output, which the kernel re-checks with `decide +kernel`.
  As in round 7 the check is run group by group — `15` groups of at most `50`
  cells — since a single reduction over all `747` cells does not go through.
* `26` is the largest multiplicity the search reached at length `14`; it is not
  claimed to be maximal, and no sharpness is claimed for the rate.
* The exponent uses natural division, so the bound is trivial for `m < 14`, and
  it is *not* uniformly stronger than round 7's `15 ^ (m / 12)`: for small `m`
  the coarser division can make either bound the larger.  What improves is the
  rate.
* The practical ceiling reached at this word length is recorded in
  `CENSUS-round10.md` and `SCRUPLES-round10.md`: longer words give better rates
  (`34` words of length `15`, rate `1.26502`; `49` of length `16`, rate
  `1.27537`; `66` of length `17`, rate `1.27948`) but the number of cells and
  hence the kernel cost grows roughly like `lam ^ T`, and already at `T = 16`
  the check is some `6` times the size of the one below.  The commission's
  target rate `1.29` was not kernel-feasible.
-/

namespace KnotGame
namespace ExpSharper

open KnotGame.Branching KnotGame.ExpCount KnotGame.ExpCert KnotGame.ExpMulti
open KnotGame.ExpMultiCert

/-- The check of one group of cells: `26` distinct words of length `14` per
cell, each with its enclosure inside `J = [1/6, 5/6]`.  The kernel runs one
group at a time. -/
abbrev P : MCell → Bool := mcellOK (3/2) (3/2) (1/6) (5/6) 14 26

lemma cells_chained : chained (1/6) cells (5/6) = true := by decide +kernel

lemma cellsG0_ok : cellsG0.all P = true := by decide +kernel
lemma cellsG1_ok : cellsG1.all P = true := by decide +kernel
lemma cellsG2_ok : cellsG2.all P = true := by decide +kernel
lemma cellsG3_ok : cellsG3.all P = true := by decide +kernel
lemma cellsG4_ok : cellsG4.all P = true := by decide +kernel
lemma cellsG5_ok : cellsG5.all P = true := by decide +kernel
lemma cellsG6_ok : cellsG6.all P = true := by decide +kernel
lemma cellsG7_ok : cellsG7.all P = true := by decide +kernel
lemma cellsG8_ok : cellsG8.all P = true := by decide +kernel
lemma cellsG9_ok : cellsG9.all P = true := by decide +kernel
lemma cellsG10_ok : cellsG10.all P = true := by decide +kernel
lemma cellsG11_ok : cellsG11.all P = true := by decide +kernel
lemma cellsG12_ok : cellsG12.all P = true := by decide +kernel
lemma cellsG13_ok : cellsG13.all P = true := by decide +kernel
lemma cellsG14_ok : cellsG14.all P = true := by decide +kernel

lemma cells_ok : cells.all P = true := by
  simp only [cells, List.all_append, cellsG0_ok, cellsG1_ok, cellsG2_ok, cellsG3_ok,
    cellsG4_ok, cellsG5_ok, cellsG6_ok, cellsG7_ok, cellsG8_ok, cellsG9_ok, cellsG10_ok,
    cellsG11_ok, cellsG12_ok, cellsG13_ok, cellsG14_ok, Bool.and_self]

/-- **Multiplicity `26` at `lam = 3/2`.**  Every `x ∈ [1/6, 5/6]` admits `26`
distinct branch words of length `14` whose images again lie in `[1/6, 5/6]`. -/
theorem mdoubling_three_halves : MDoubling (3/2 : ℝ) (1/6 : ℝ) (5/6 : ℝ) 14 26 := by
  have h := mdoubling_of_cert (l0 := 3/2) (l1 := 3/2) (a := 1/6) (b := 5/6) (T := 14) (k := 26)
    (lam := (3/2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) cells_chained (by decide)
    cells_ok
  simpa using h

/-- **T31 — a sharper exponential lower bound at `lam = 3/2`.**  The number of
length-`m` branch words along which `1/2` survives is at least `26 ^ (m / 14)`,
a growth rate of `26 ^ (1/14) ≈ 1.26203` per step. -/
theorem twentysix_pow_le_K (m : ℕ) : 26 ^ (m / 14) ≤ K (3/2 : ℝ) m :=
  pow_le_K_of_mdoubling (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) mdoubling_three_halves m

/-- **The rate is an improvement on round 7.**  `15 ^ (1/12) < 26 ^ (1/14)`, in
the integer form `15 ^ 14 < 26 ^ 12`. -/
theorem sharper_rate : (15 : ℕ) ^ 14 < 26 ^ 12 := by norm_num

/-- The same comparison for the real rates:
`(15 : ℝ) ^ ((1 : ℝ)/12) < (26 : ℝ) ^ ((1 : ℝ)/14)`. -/
theorem sharper_rate_real : (15 : ℝ) ^ ((1 : ℝ)/12) < (26 : ℝ) ^ ((1 : ℝ)/14) := by
  have h15 : (0 : ℝ) ≤ 15 := by norm_num
  have h26 : (0 : ℝ) ≤ 26 := by norm_num
  have hkey : ((15 : ℝ) ^ ((1 : ℝ)/12)) ^ (168 : ℕ) < ((26 : ℝ) ^ ((1 : ℝ)/14)) ^ (168 : ℕ) := by
    rw [← Real.rpow_natCast ((15 : ℝ) ^ ((1 : ℝ)/12)) 168,
      ← Real.rpow_natCast ((26 : ℝ) ^ ((1 : ℝ)/14)) 168,
      ← Real.rpow_mul h15, ← Real.rpow_mul h26]
    norm_num
  exact lt_of_pow_lt_pow_left₀ 168 (Real.rpow_nonneg h26 _) hkey

end ExpSharper
end KnotGame
