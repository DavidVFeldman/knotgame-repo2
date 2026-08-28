import RequestProject.ExpCert

/-!
# An exponential lower bound for the kind count at `lam = 3/2` (round 7)

`K lam m` (see `RequestProject.BranchingCount`) counts the length-`m` branch
words along which `1/2` survives.  Round 4 certified the unconditional linear
bound `m/(B+1) ≤ K lam m`.  Here we prove, at `lam = 3/2`, the **exponential**
bound

  `2 ^ (m / 5) ≤ K (3/2) m`   (natural division),

by the covering argument of `RequestProject.ExpCount` and
`RequestProject.ExpCert` rather than by the return-time renewal of the note.

The certificate `cells` below has `15` cells tiling `J = [1/4, 3/4]`, each
carrying two distinct branch words of length `5` mapping the cell into `J`; it
is checked by kernel reduction over exact rationals (`cells_ok`), which at the
single parameter `lam = 3/2` is an exact computation rather than an enclosure.

## Conventions (SCRUPLES)

* `J = [1/4, 3/4]` is closed; it contains the window `(1/3, 2/3)` of `lam = 3/2`
  and, in particular, the starting point `1/2`.
* The growth rate obtained is `2 ^ (1/5) ≈ 1.1487` per step.  The measured growth
  at `3/2` is `(2/lam)^m = (4/3)^m`; the argument is not tuned for the true rate,
  and none of the note's open items is used.
-/

namespace KnotGame
namespace ExpLower

open KnotGame.Branching KnotGame.ExpCount KnotGame.ExpCert

/-- The certificate: `15` cells tiling `[1/4, 3/4]`, each carrying two distinct
words of length `5` mapping the cell into `[1/4, 3/4]`.  Produced by
`scripts/expcert_interval.py`. -/
def cells : List Cell :=
  [(1/4, 64/243, [0,0,1,0,1], [0,0,0,1,1]),
   (64/243, 76/243, [0,1,0,0,0], [0,0,1,0,1]),
   (76/243, 26/81, [0,0,1,1,0], [0,1,0,0,0]),
   (26/81, 28/81, [0,1,0,0,1], [0,0,1,1,0]),
   (28/81, 94/243, [0,0,1,1,1], [0,1,0,0,1]),
   (94/243, 34/81, [1,0,0,0,0], [0,1,0,1,0]),
   (34/81, 38/81, [0,1,0,1,1], [0,1,1,0,0]),
   (38/81, 43/81, [0,1,1,0,1], [1,0,0,1,0]),
   (43/81, 47/81, [1,0,0,1,1], [1,0,1,0,0]),
   (47/81, 154/243, [1,0,1,0,1], [0,1,1,1,1]),
   (154/243, 53/81, [1,0,1,1,0], [1,1,0,0,0]),
   (53/81, 55/81, [1,1,0,0,1], [1,0,1,1,0]),
   (55/81, 175/243, [1,0,1,1,1], [1,1,0,0,1]),
   (175/243, 181/243, [1,1,0,1,0], [1,0,1,1,1]),
   (181/243, 61/81, [1,1,1,0,0], [1,1,0,1,0])]

lemma cells_chained : chained (1/4) cells (3/4) = true := by decide +kernel

lemma cells_ok : cells.all (cellOK (3/2) (3/2) (1/4) (3/4) 5) = true := by decide +kernel

/-- **The doubling lemma at `lam = 3/2`.**  Every `x ∈ [1/4, 3/4]` admits two
distinct branch words of length `5` whose images again lie in `[1/4, 3/4]`. -/
theorem doubling_three_halves : Doubling (3/2 : ℝ) (1/4 : ℝ) (3/4 : ℝ) 5 := by
  have h := doubling_of_cert (l0 := 3/2) (l1 := 3/2) (a := 1/4) (b := 3/4) (T := 5)
    (lam := (3/2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) cells_chained (by decide) cells_ok
  simpa using h

/-- **An exponential lower bound for the kind count at `lam = 3/2`.**  The number
of length-`m` branch words along which `1/2` survives is at least `2 ^ (m / 5)`. -/
theorem two_pow_le_K (m : ℕ) : 2 ^ (m / 5) ≤ K (3/2 : ℝ) m :=
  two_pow_le_K_of_doubling (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) doubling_three_halves m

end ExpLower
end KnotGame
