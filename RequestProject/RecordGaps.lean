import RequestProject.TwoStep

/-!
# T28 — the record-configuration facts of Figure `fig:records32`

Round 5 (`TwoStep.lean`) exhibited record words at `λ = 3/2` for
`k = 2, …, 7`, certified the configurations they produce as exact sets of
dyadic rationals, and certified the two containment chains
`2 ⊂ 3 ⊂ 5 ⊂ 7` and `4 ⊂ 6`.  This file adds the remaining exact claims of the
caption of Figure `fig:records32`, for the *same* exhibited configurations
(together with the one-move word `record1`, so that all seven values
`k = 1, …, 7` are covered):

* **(a)** the birth point `1/2` belongs to every one of the seven
  configurations;
* **(b)** for `k = 2, 3` the minimum gap is exactly `1/8`, realised by the pair
  `(3/8, 1/2)`;
* **(c)** for `k = 4, 5, 6, 7` the minimum gap is exactly `13/512`, realised by
  `(243/512, 1/2)` at `k = 4, 6` and by `(1/2, 269/512)` at `k = 5, 7`.

Everything is checked by the kernel on exact integers, through the bridge
`run_eq_image_runZ` of `RunRational.lean`: a configuration after a word of
length `j` is a finite set of numerators over `2^j`, and both the membership
statements and the gap bounds are decidable statements about those integers.

## Scope guard (SCRUPLES)

**These are statements about the exhibited configurations only.**  The paper's
caption speaks of "the records", and `prop:twostep` quantifies over *all*
configurations attaining `k` knots in `d_{3/2}(k)` moves.  Nothing below
asserts that the words `record1, …, record7` are the only records, that their
lengths are the minimal depths `d_{3/2}(k)` (minimality is certified only for
`k ≤ 4`, in `RecordDepths.lean`), or that the configurations listed here
exhaust the records at their depth.  Exhaustiveness is explicitly **not**
commissioned and is **not** proved.  What is proved is: for each of the seven
listed words, the configuration it produces contains `1/2`, and its minimum
gap is the stated rational, realised by the stated pair.

The minimum-gap statements are packaged by `IsMinGapAt S δ a b`, which says
that `a` and `b` are points of `S` at distance exactly `δ` and that no two
distinct points of `S` are closer than `δ`.  This is exactly "the minimum gap
is `δ`, realised by the pair `(a,b)`"; no separate `minGap` function is
introduced.
-/

namespace KnotGame

set_option maxRecDepth 400000

/-! ## Two small bridges to the integer model -/

/-- A numerator of the integer configuration is a point of the real one. -/
lemma mem_run_of_emb_eq {w : List Move} {A : ℤ} {x : ℝ}
    (hx : x = (A : ℝ) / 2 ^ w.length) (h : A ∈ runZ w) :
    x ∈ run (3 / 2 : ℝ) w := by
  rw [run_eq_image_runZ, hx]
  exact Finset.mem_image_of_mem _ h

/-- A gap bound in the integer model is a gap bound in the real one. -/
lemma gap_lower_bound_of_runZ {w : List Move} {D : ℤ} {c : ℝ}
    (hc : c = (D : ℝ) / 2 ^ w.length)
    (h : ∀ A ∈ runZ w, ∀ B ∈ runZ w, A ≠ B → D ≤ |A - B|) :
    ∀ x ∈ run (3 / 2 : ℝ) w, ∀ y ∈ run (3 / 2 : ℝ) w, x ≠ y → c ≤ |x - y| := by
  intro x hx y hy hxy
  rw [run_eq_image_runZ, Finset.mem_image] at hx hy
  obtain ⟨A, hA, rfl⟩ := hx
  obtain ⟨B, hB, rfl⟩ := hy
  have hAB : A ≠ B := fun hh => hxy (by rw [hh])
  have hpos : (0 : ℝ) < 2 ^ w.length := by positivity
  have hkey : |emb w.length A - emb w.length B| = ((|A - B| : ℤ) : ℝ) / 2 ^ w.length := by
    simp only [emb, div_sub_div_same, abs_div, abs_of_pos hpos]
    push_cast
    rfl
  rw [hc, hkey, div_le_div_iff_of_pos_right hpos]
  exact_mod_cast h A hA B hB hAB

/-- `δ` is the **minimum gap** of the configuration `S`, realised by the pair
`(a, b)`: both `a` and `b` lie in `S`, they are `δ` apart, and no two distinct
points of `S` are closer than `δ`. -/
def IsMinGapAt (S : Finset ℝ) (delta a b : ℝ) : Prop :=
  a ∈ S ∧ b ∈ S ∧ b - a = delta ∧
    ∀ x ∈ S, ∀ y ∈ S, x ≠ y → delta ≤ |x - y|

/-! ## The one-knot record -/

open Move in
/-- The record word for `k = 1`: a single birth. -/
def record1 : List Move := [M]

/-- The configuration after `record1`, as numerators over `2^1`: `{1/2}`. -/
theorem runZ_record1 : runZ record1 = {1} := by decide

theorem card_run_record1 : (run (3 / 2 : ℝ) record1).card = 1 := by
  rw [card_run_eq_card_runZ]; decide

theorem d_le_one : d (3 / 2 : ℝ) 1 ≤ 1 :=
  Nat.sInf_le (by
    have := card_run_le_N one_lt_three_halves record1
    rw [card_run_record1] at this
    exact this)

/-! ## (a) The birth point `1/2` lies in every record configuration -/

theorem half_mem_record1 : (1 / 2 : ℝ) ∈ run (3 / 2 : ℝ) record1 :=
  mem_run_of_emb_eq (A := 1) (by rw [show record1.length = 1 from rfl]; norm_num)
    (by rw [runZ_record1]; decide)

theorem half_mem_record2 : (1 / 2 : ℝ) ∈ run (3 / 2 : ℝ) record2 :=
  mem_run_of_emb_eq (A := 4) (by rw [show record2.length = 3 from rfl]; norm_num)
    (by rw [runZ_record2]; decide)

theorem half_mem_record3 : (1 / 2 : ℝ) ∈ run (3 / 2 : ℝ) record3 :=
  mem_run_of_emb_eq (A := 16) (by rw [show record3.length = 5 from rfl]; norm_num)
    (by rw [runZ_record3]; decide)

theorem half_mem_record4 : (1 / 2 : ℝ) ∈ run (3 / 2 : ℝ) record4 :=
  mem_run_of_emb_eq (A := 256) (by rw [show record4.length = 9 from rfl]; norm_num)
    (by rw [runZ_record4]; decide)

theorem half_mem_record5 : (1 / 2 : ℝ) ∈ run (3 / 2 : ℝ) record5 :=
  mem_run_of_emb_eq (A := 262144) (by rw [show record5.length = 19 from rfl]; norm_num)
    (by rw [runZ_record5]; decide)

theorem half_mem_record6 : (1 / 2 : ℝ) ∈ run (3 / 2 : ℝ) record6 :=
  mem_run_of_emb_eq (A := 4194304) (by rw [show record6.length = 23 from rfl]; norm_num)
    (by rw [runZ_record6]; decide)

theorem half_mem_record7 : (1 / 2 : ℝ) ∈ run (3 / 2 : ℝ) record7 :=
  mem_run_of_emb_eq (A := 2251799813685248)
    (by rw [show record7.length = 52 from rfl]; norm_num)
    (by rw [runZ_record7]; decide)

/-- **(a)**: the birth point `1/2` belongs to each of the seven exhibited
record configurations. -/
theorem half_mem_records :
    (1 / 2 : ℝ) ∈ run (3 / 2 : ℝ) record1 ∧ (1 / 2 : ℝ) ∈ run (3 / 2 : ℝ) record2 ∧
    (1 / 2 : ℝ) ∈ run (3 / 2 : ℝ) record3 ∧ (1 / 2 : ℝ) ∈ run (3 / 2 : ℝ) record4 ∧
    (1 / 2 : ℝ) ∈ run (3 / 2 : ℝ) record5 ∧ (1 / 2 : ℝ) ∈ run (3 / 2 : ℝ) record6 ∧
    (1 / 2 : ℝ) ∈ run (3 / 2 : ℝ) record7 :=
  ⟨half_mem_record1, half_mem_record2, half_mem_record3, half_mem_record4,
    half_mem_record5, half_mem_record6, half_mem_record7⟩

/-! ## (b) The minimum gap at `k = 2, 3` -/

/-- **(b)** at `k = 2`: the minimum gap of the two-knot record configuration is
exactly `1/8`, realised by `(3/8, 1/2)`. -/
theorem minGap_record2 :
    IsMinGapAt (run (3 / 2 : ℝ) record2) (1 / 8) (3 / 8) (1 / 2) :=
  ⟨mem_run_of_emb_eq (A := 3) (by rw [show record2.length = 3 from rfl]; norm_num)
      (by rw [runZ_record2]; decide),
    half_mem_record2, by norm_num,
    gap_lower_bound_of_runZ (D := 1) (by rw [show record2.length = 3 from rfl]; norm_num)
      (by rw [runZ_record2]; decide)⟩

/-- **(b)** at `k = 3`: the minimum gap of the three-knot record configuration
is exactly `1/8`, realised by `(3/8, 1/2)`. -/
theorem minGap_record3 :
    IsMinGapAt (run (3 / 2 : ℝ) record3) (1 / 8) (3 / 8) (1 / 2) :=
  ⟨mem_run_of_emb_eq (A := 12) (by rw [show record3.length = 5 from rfl]; norm_num)
      (by rw [runZ_record3]; decide),
    half_mem_record3, by norm_num,
    gap_lower_bound_of_runZ (D := 4) (by rw [show record3.length = 5 from rfl]; norm_num)
      (by rw [runZ_record3]; decide)⟩

/-! ## (c) The minimum gap at `k = 4, 5, 6, 7` -/

/-- **(c)** at `k = 4`: the minimum gap is exactly `13/512`, realised by
`(243/512, 1/2)`. -/
theorem minGap_record4 :
    IsMinGapAt (run (3 / 2 : ℝ) record4) (13 / 512) (243 / 512) (1 / 2) :=
  ⟨mem_run_of_emb_eq (A := 243) (by rw [show record4.length = 9 from rfl]; norm_num)
      (by rw [runZ_record4]; decide),
    half_mem_record4, by norm_num,
    gap_lower_bound_of_runZ (D := 13) (by rw [show record4.length = 9 from rfl]; norm_num)
      (by rw [runZ_record4]; decide)⟩

/-- **(c)** at `k = 5`: the minimum gap is exactly `13/512`, realised by
`(1/2, 269/512)`. -/
theorem minGap_record5 :
    IsMinGapAt (run (3 / 2 : ℝ) record5) (13 / 512) (1 / 2) (269 / 512) :=
  ⟨half_mem_record5,
    mem_run_of_emb_eq (A := 275456) (by rw [show record5.length = 19 from rfl]; norm_num)
      (by rw [runZ_record5]; decide),
    by norm_num,
    gap_lower_bound_of_runZ (D := 13312)
      (by rw [show record5.length = 19 from rfl]; norm_num)
      (by rw [runZ_record5]; decide)⟩

/-- **(c)** at `k = 6`: the minimum gap is exactly `13/512`, realised by
`(243/512, 1/2)`. -/
theorem minGap_record6 :
    IsMinGapAt (run (3 / 2 : ℝ) record6) (13 / 512) (243 / 512) (1 / 2) :=
  ⟨mem_run_of_emb_eq (A := 3981312)
      (by rw [show record6.length = 23 from rfl]; norm_num)
      (by rw [runZ_record6]; decide),
    half_mem_record6, by norm_num,
    gap_lower_bound_of_runZ (D := 212992)
      (by rw [show record6.length = 23 from rfl]; norm_num)
      (by rw [runZ_record6]; decide)⟩

/-- **(c)** at `k = 7`: the minimum gap is exactly `13/512`, realised by
`(1/2, 269/512)`. -/
theorem minGap_record7 :
    IsMinGapAt (run (3 / 2 : ℝ) record7) (13 / 512) (1 / 2) (269 / 512) :=
  ⟨half_mem_record7,
    mem_run_of_emb_eq (A := 2366149022973952)
      (by rw [show record7.length = 52 from rfl]; norm_num)
      (by rw [runZ_record7]; decide),
    by norm_num,
    gap_lower_bound_of_runZ (D := 114349209288704)
      (by rw [show record7.length = 52 from rfl]; norm_num)
      (by rw [runZ_record7]; decide)⟩

end KnotGame
