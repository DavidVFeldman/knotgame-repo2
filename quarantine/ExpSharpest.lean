import RequestProject.ExpSharpestChecks0
import RequestProject.ExpSharpestChecks1
import RequestProject.ExpSharpestChecks2
import RequestProject.ExpSharpestChecks3
import RequestProject.ExpSharpestChecks4
import RequestProject.ExpSharpestChecks5
import RequestProject.ExpSharpestChecks6
import RequestProject.ExpSharpestChecks7
import RequestProject.ExpSharpestChecks8
import RequestProject.ExpSharper

/-!
# T31 — the sharpest certified rate at `lam = 3/2` (round 10)

Round 7 (`RequestProject.ExpSharp`) certified `15 ^ (m / 12) ≤ K (3/2) m`, a
rate of `15 ^ (1/12) ≈ 1.25316` per step; `RequestProject.ExpSharper` raised
this to `26 ^ (m / 14)`, a rate of `26 ^ (1/14) ≈ 1.26203`.  This file goes one
word longer and certifies

  `49 ^ (m / 16) ≤ K (3/2) m`,

a rate of `49 ^ (1/16) ≈ 1.27537` per step (`sharpest_rate`, the integer form
`26 ^ 16 < 49 ^ 14`, and `sharpest_rate_real`, the real form
`26 ^ (1/14) < 49 ^ (1/16)`; `sharpest_rate_vs_round7` compares directly with
round 7).  The measured growth is `(2/lam) ^ m = (4/3) ^ m ≈ 1.33333 ^ m`, so
this is closer to, but still below, the observed rate.

## Conventions (SCRUPLES)

* Same machinery, same core interval `J = [1/6, 5/6]`, same single parameter
  `3/2` as `RequestProject.ExpSharper`; only the word length (`16`) and the
  multiplicity (`49`) change.  `49` is the largest multiplicity the search
  reaches at length `16` — it fails at `50` — but it is not claimed to be
  maximal, and no sharpness is claimed for the rate.
* The price is the certificate size: `2008` cells against `747`, i.e.
  `2008 · 49 · 16 ≈ 1.57` million reduced "letters" against `272` thousand.  The
  data had to be split across nine files (`ExpSharpestData0` … `8`) to be
  elaborated at all, and the kernel check is run in `41` groups of at most `50`
  cells, themselves spread over nine files (`ExpSharpestChecks0` … `8`) because
  the kernel's working set for all of them in one file does not fit in memory.  This is the practical ceiling reached in round 10: the cell count
  grows like `lam ^ T`, so the next steps (`66` words of length `17`, rate
  `1.27948`, and beyond) multiply the cost again, and the commission's target
  rate of `1.29` — which needs `T ≈ 20`–`22` — was not kernel-feasible.  See
  `CENSUS-round10.md` §3.
* The exponent uses natural division, so the bound is trivial for `m < 16`, and
  it is *not* uniformly stronger than the `26 ^ (m / 14)` of
  `RequestProject.ExpSharper`: for small `m` the coarser division can make
  either bound the larger.  What improves is the rate.  Both bounds are kept.
* The certificate was found by the greedy search of
  `scripts/gen_expsharpest.py` (with `scripts/expcert_dfs.py`); the search is
  not trusted, only its output, which the kernel re-checks with
  `decide +kernel`.
-/

namespace KnotGame
namespace ExpSharpest

open KnotGame.Branching KnotGame.ExpCount KnotGame.ExpCert KnotGame.ExpMulti
open KnotGame.ExpMultiCert

set_option maxHeartbeats 4000000

lemma cells_chained : chained (1/6) cells (5/6) = true := by decide +kernel

lemma cells_ok : cells.all P = true := by
  simp only [cells, List.all_append, cellsG0_ok, cellsG1_ok, cellsG2_ok, cellsG3_ok,
    cellsG4_ok, cellsG5_ok, cellsG6_ok, cellsG7_ok, cellsG8_ok, cellsG9_ok, cellsG10_ok,
    cellsG11_ok, cellsG12_ok, cellsG13_ok, cellsG14_ok, cellsG15_ok, cellsG16_ok,
    cellsG17_ok, cellsG18_ok, cellsG19_ok, cellsG20_ok, cellsG21_ok, cellsG22_ok,
    cellsG23_ok, cellsG24_ok, cellsG25_ok, cellsG26_ok, cellsG27_ok, cellsG28_ok,
    cellsG29_ok, cellsG30_ok, cellsG31_ok, cellsG32_ok, cellsG33_ok, cellsG34_ok,
    cellsG35_ok, cellsG36_ok, cellsG37_ok, cellsG38_ok, cellsG39_ok, cellsG40_ok,
    Bool.and_self]

/-- **Multiplicity `49` at `lam = 3/2`.**  Every `x ∈ [1/6, 5/6]` admits `49`
distinct branch words of length `16` whose images again lie in `[1/6, 5/6]`. -/
theorem mdoubling_three_halves_16 : MDoubling (3/2 : ℝ) (1/6 : ℝ) (5/6 : ℝ) 16 49 := by
  have h := mdoubling_of_cert (l0 := 3/2) (l1 := 3/2) (a := 1/6) (b := 5/6) (T := 16) (k := 49)
    (lam := (3/2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) cells_chained (by decide)
    cells_ok
  simpa using h

/-- **T31 — the sharpest certified exponential lower bound at `lam = 3/2`.**
The number of length-`m` branch words along which `1/2` survives is at least
`49 ^ (m / 16)`, a growth rate of `49 ^ (1/16) ≈ 1.27537` per step. -/
theorem fortynine_pow_le_K (m : ℕ) : 49 ^ (m / 16) ≤ K (3/2 : ℝ) m :=
  pow_le_K_of_mdoubling (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) mdoubling_three_halves_16 m

/-- **The rate improves on `RequestProject.ExpSharper`.**
`26 ^ (1/14) < 49 ^ (1/16)`, in the integer form `26 ^ 16 < 49 ^ 14`. -/
theorem sharpest_rate : (26 : ℕ) ^ 16 < 49 ^ 14 := by norm_num

/-- **The rate improves on round 7.**  `15 ^ (1/12) < 49 ^ (1/16)`, in the
integer form `15 ^ 16 < 49 ^ 12`. -/
theorem sharpest_rate_vs_round7 : (15 : ℕ) ^ 16 < 49 ^ 12 := by norm_num

/-- The same comparison for the real rates:
`(26 : ℝ) ^ ((1 : ℝ)/14) < (49 : ℝ) ^ ((1 : ℝ)/16)`. -/
theorem sharpest_rate_real : (26 : ℝ) ^ ((1 : ℝ)/14) < (49 : ℝ) ^ ((1 : ℝ)/16) := by
  have h26 : (0 : ℝ) ≤ 26 := by norm_num
  have h49 : (0 : ℝ) ≤ 49 := by norm_num
  have hkey : ((26 : ℝ) ^ ((1 : ℝ)/14)) ^ (224 : ℕ) < ((49 : ℝ) ^ ((1 : ℝ)/16)) ^ (224 : ℕ) := by
    rw [← Real.rpow_natCast ((26 : ℝ) ^ ((1 : ℝ)/14)) 224,
      ← Real.rpow_natCast ((49 : ℝ) ^ ((1 : ℝ)/16)) 224,
      ← Real.rpow_mul h26, ← Real.rpow_mul h49]
    norm_num
  exact lt_of_pow_lt_pow_left₀ 224 (Real.rpow_nonneg h49 _) hkey

end ExpSharpest
end KnotGame
