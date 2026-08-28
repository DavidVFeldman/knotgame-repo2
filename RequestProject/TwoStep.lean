import RequestProject.RunRational
import RequestProject.Suffix

/-!
# T21 — the two-step containment at `λ = 3/2` (paper Proposition `prop:twostep`)

The paper's Proposition `prop:twostep` is an observation about *record*
configurations at `λ = 3/2`: writing `d(k)` for the least length of a run
producing `k` simultaneous knots, every configuration attaining `k+2` knots in
`d(k+2)` moves contains one attaining `k` knots in `d(k)` moves, for
`1 ≤ k ≤ 5`.  Figure `fig:records32` draws particular representatives, which
nest along the two chains `k = 2 ⊂ 3 ⊂ 5 ⊂ 7` and `k = 4 ⊂ 6`.

## Scope of what is certified here

*The paper's drawn representatives are not listed in the source materials* —
neither the commission nor the paper's text records the seven record words, and
the figure is an included graphic.  The words below were therefore obtained
independently, by an exhaustive breadth-first search over all reachable
configurations at `λ = 3/2` (configurations deduplicated at each depth); each is
the first word, in the order `L < M < R`, attaining its knot count at the least
depth at which that count occurs.  The lengths `1, 3, 5, 9, 19, 23` agree with
the values of `d_{3/2}(k)` quoted in the paper, and the `k = 5` word is the
`19`-move run of Remark `rem:candidates` (see `CandidateInstance.lean`).

What is certified below, by the kernel on exact integer arithmetic through the
bridge `run_eq_image_runZ`:

* the configuration after each word, as a set of numerators over `2^{|w|}`;
* that it has the stated number of knots, hence `d_{3/2}(k) ≤ |w|`;
* the containments `k = 2 ⊂ 3 ⊂ 5 ⊂ 7` and `k = 4 ⊂ 6` between these
  configurations, as sets of points of `(0,1)`.

The `k = 7` word, of length `52`, is beyond exhaustive enumeration (the
breadth-first search has more than `10^8` reachable configurations at that
depth, even after discarding configurations contained in others); it was found
by a beam search (`scripts/game32_beam.py`) and, like the others, is verified
here by the kernel on exact integers.  Its configuration does contain the five
points of the `k = 5` configuration, so the chain `2 ⊂ 3 ⊂ 5 ⊂ 7` closes.  Note
that the containment is between *point sets*: `record7` is not an extension of
`record5` on the right, and the five shared points are shared as positions, not
as knots with a common history.

What is **not** certified: that these lengths are minimal (`d_{3/2}(k) = |w|`)
beyond `k ≤ 4`, where `RecordDepths.lean` certifies `d_{3/2}(2) = 3`,
`d_{3/2}(3) = 5` and `d_{3/2}(4) = 9`; that these are *all* the record
configurations at each depth; or the statement of `prop:twostep` itself, which
quantifies over all record configurations.  The exhaustiveness at `k = 7` is the
hard half of the commission and is not attempted.
-/

namespace KnotGame

set_option maxRecDepth 400000

/-- Any word gives a lower bound for `N` at its own length. -/
lemma card_run_le_N {lam : ℝ} (h : 1 < lam) (w : List Move) :
    (run lam w).card ≤ N lam w.length := by
  rw [card_run h]
  exact births_le_N h w

lemma one_lt_three_halves : (1:ℝ) < 3/2 := by norm_num

open Move in
/-- A record word for `k = 2`, of length `3`. -/
def record2 : List Move := [M, L, M]

open Move in
/-- A record word for `k = 3`, of length `5`. -/
def record3 : List Move := [M, L, M, L, M]

open Move in
/-- A record word for `k = 4`, of length `9`. -/
def record4 : List Move := [M, L, M, L, M, R, M, R, M]

open Move in
/-- A record word for `k = 5`, of length `19`.  This is the word of Remark
`rem:candidates`. -/
def record5 : List Move := [M, L, M, L, M, M, M, M, M, L, M, R, L, R, M, L, M, L, M]

open Move in
/-- A record word for `k = 6`, of length `23`. -/
def record6 : List Move :=
  [M, L, M, L, M, R, M, R, M, L, M, M, L, R, M, L, R, L, M, R, M, R, M]

open Move in
/-- A word of length `52` producing `7` simultaneous knots, whose configuration
contains the `k = 5` configuration of `record5`.  Exhaustive search is out of
reach at this depth (see the header); this word was found by a beam search and
is checked here by exact integer arithmetic. -/
def record7 : List Move :=
  [M, L, M, R, L, R, L, M, R, L, L, R, R, M, L, M, R, R, L, L, R, M, M, L, M, M, M, M, L, M,
    R, M, R, M, L, M, L, M, R, M, M, R, L, M, R, L, R, M, L, M, L, M]

/-! ## The configurations -/

/-- The configuration after `record2`, as numerators over `2^3`:
`{3/8, 1/2}`. -/
theorem runZ_record2 : runZ record2 = {3, 4} := by decide

/-- The configuration after `record3`, as numerators over `2^5`:
`{3/32, 3/8, 1/2}`. -/
theorem runZ_record3 : runZ record3 = {3, 12, 16} := by decide

/-- The configuration after `record4`, as numerators over `2^9`:
`{243/512, 1/2, 5/8, 29/32}`. -/
theorem runZ_record4 : runZ record4 = {243, 256, 320, 464} := by decide

/-- The configuration after `record5`, as numerators over `2^19`. -/
theorem runZ_record5 : runZ record5 = {7275, 49152, 196608, 262144, 275456} := by decide

/-- The configuration after `record6`, as numerators over `2^23`. -/
theorem runZ_record6 :
    runZ record6 = {589275, 3981312, 4194304, 5242880, 7602176, 8272208} := by decide

/-- The configuration after `record7`, as numerators over `2^52`.  Five of the
seven numerators are `2^33` times the five numerators of `runZ record5`. -/
theorem runZ_record7 :
    runZ record7 = {62491774156800, 285503792501337, 422212465065984, 1688849860263936,
      2251799813685248, 2366149022973952, 4187235020701696} := by decide

/-! ## The knot counts -/

theorem card_run_record2 : (run (3/2 : ℝ) record2).card = 2 := by
  rw [card_run_eq_card_runZ]; decide

theorem card_run_record3 : (run (3/2 : ℝ) record3).card = 3 := by
  rw [card_run_eq_card_runZ]; decide

theorem card_run_record4 : (run (3/2 : ℝ) record4).card = 4 := by
  rw [card_run_eq_card_runZ]; decide

theorem card_run_record5 : (run (3/2 : ℝ) record5).card = 5 := by
  rw [card_run_eq_card_runZ]; decide

theorem card_run_record6 : (run (3/2 : ℝ) record6).card = 6 := by
  rw [card_run_eq_card_runZ]; decide

theorem card_run_record7 : (run (3/2 : ℝ) record7).card = 7 := by
  rw [card_run_eq_card_runZ]; decide

/-! ## Upper bounds on `d_{3/2}(k)` -/

theorem d_le_three : d (3/2 : ℝ) 2 ≤ 3 :=
  Nat.sInf_le (by
    have := card_run_le_N one_lt_three_halves record2
    rw [card_run_record2] at this
    exact this)

theorem d_le_five : d (3/2 : ℝ) 3 ≤ 5 :=
  Nat.sInf_le (by
    have := card_run_le_N one_lt_three_halves record3
    rw [card_run_record3] at this
    exact this)

theorem d_le_nine : d (3/2 : ℝ) 4 ≤ 9 :=
  Nat.sInf_le (by
    have := card_run_le_N one_lt_three_halves record4
    rw [card_run_record4] at this
    exact this)

theorem d_le_nineteen : d (3/2 : ℝ) 5 ≤ 19 :=
  Nat.sInf_le (by
    have := card_run_le_N one_lt_three_halves record5
    rw [card_run_record5] at this
    exact this)

theorem d_le_twentythree : d (3/2 : ℝ) 6 ≤ 23 :=
  Nat.sInf_le (by
    have := card_run_le_N one_lt_three_halves record6
    rw [card_run_record6] at this
    exact this)

theorem d_le_fiftytwo : d (3/2 : ℝ) 7 ≤ 52 :=
  Nat.sInf_le (by
    have := card_run_le_N one_lt_three_halves record7
    rw [card_run_record7] at this
    exact this)

/-! ## The containments -/

/-- **T21, easy half**: the `k = 2` record configuration sits inside the
`k = 3` one. -/
theorem record_subset_two_three :
    run (3/2 : ℝ) record2 ⊆ run (3/2 : ℝ) record3 := by
  rw [run_subset_run_iff (k := 2) rfl]
  decide

/-- **T21, easy half**: the `k = 3` record configuration sits inside the
`k = 5` one. -/
theorem record_subset_three_five :
    run (3/2 : ℝ) record3 ⊆ run (3/2 : ℝ) record5 := by
  rw [run_subset_run_iff (k := 14) rfl]
  decide

/-- **T21, easy half**: the `k = 4` record configuration sits inside the
`k = 6` one. -/
theorem record_subset_four_six :
    run (3/2 : ℝ) record4 ⊆ run (3/2 : ℝ) record6 := by
  rw [run_subset_run_iff (k := 14) rfl]
  decide

/-- **T21, easy half**: the `k = 5` configuration sits inside the `k = 7` one,
which closes the chain `k = 2 ⊂ 3 ⊂ 5 ⊂ 7`. -/
theorem record_subset_five_seven :
    run (3/2 : ℝ) record5 ⊆ run (3/2 : ℝ) record7 := by
  rw [run_subset_run_iff (k := 33) rfl]
  decide

end KnotGame
