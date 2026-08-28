import RequestProject.Candidates

/-!
# T20, the instance (paper Remark `rem:candidates`)

The paper records, for the `19`-move run

```
w = M L M L M M M M M L M R L R M L M L M
```

attaining five simultaneous knots at `λ = 3/2`, that there are `2^11 = 2048`
candidate itineraries — one Boolean per `M` of `w` — of which exactly six are
genuine (have a nonempty cell), and that the six cells tile a set of length
exactly `(2/3)^19 = 524288/1162261467`.

`Candidates.lean` supplies the two general ingredients: the cells partition the
survivor set `S(w)` (`followsItin_partition`), and at `λ = 3/2` each cell is the
open interval whose endpoints `cellZ` computes exactly, over the common
denominator `2·3^{|w|}` (`followsItin_iff_cellZ`).  Here the finite claims are
settled by the kernel on exact integer arithmetic.
-/

namespace KnotGame

set_option maxRecDepth 100000

/-! ## The cell as an interval, and its length -/

lemma two_mul_three_pow_pos (w : List Move) : (0:ℝ) < 2 * 3 ^ w.length := by positivity

/-- At `λ = 3/2` the candidate cell of `w` and `t` is the open interval whose
endpoints `cellZ w t` computes over the denominator `2·3^{|w|}`. -/
theorem followsItin_eq_Ioo (w : List Move) (t : List Bool) :
    {x : ℝ | FollowsItin (3/2) w t x} =
      Set.Ioo (((cellZ w t).1 : ℝ) / (2 * 3 ^ w.length))
        (((cellZ w t).2 : ℝ) / (2 * 3 ^ w.length)) := by
  have hpos := two_mul_three_pow_pos w
  ext x
  rw [Set.mem_setOf_eq, followsItin_iff_cellZ, Set.mem_Ioo, div_lt_iff₀ hpos,
    lt_div_iff₀ hpos]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

/-- A candidate is genuine exactly when the computed endpoints are in order. -/
theorem cell_nonempty_iff (w : List Move) (t : List Bool) :
    {x : ℝ | FollowsItin (3/2) w t x}.Nonempty ↔ (cellZ w t).1 < (cellZ w t).2 := by
  have hpos := two_mul_three_pow_pos w
  rw [followsItin_eq_Ioo, Set.nonempty_Ioo, div_lt_div_iff_of_pos_right hpos,
    Int.cast_lt]

/-- The length of a candidate cell. -/
theorem volume_cell (w : List Move) (t : List Bool) :
    MeasureTheory.volume {x : ℝ | FollowsItin (3/2) w t x}
      = ENNReal.ofReal ((((cellZ w t).2 - (cellZ w t).1 : ℤ) : ℝ) / (2 * 3 ^ w.length)) := by
  rw [followsItin_eq_Ioo, Real.volume_Ioo]
  congr 1
  push_cast
  ring

/-! ## Enumerating the candidates -/

/-- All itineraries of a given length. -/
def allItin : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allItin n).flatMap (fun t => [false :: t, true :: t])

/-- `allItin n` is exactly the list of itineraries of length `n`. -/
lemma mem_allItin : ∀ (n : ℕ) (t : List Bool), t ∈ allItin n ↔ t.length = n
  | 0, t => by
      constructor
      · intro ht
        rw [allItin, List.mem_singleton] at ht
        simp [ht]
      · intro ht
        rw [allItin, List.mem_singleton]
        exact List.eq_nil_of_length_eq_zero ht
  | n + 1, t => by
      rw [allItin]
      simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro ⟨s, hs, rfl | rfl⟩ <;>
          simp [(mem_allItin n s).mp hs]
      · intro ht
        match t with
        | [] => simp at ht
        | b :: s =>
            refine ⟨s, (mem_allItin n s).mpr (by simpa using ht), ?_⟩
            cases b <;> simp

/-- The genuine candidates of `w` among the itineraries of length `n`. -/
def liveItin (w : List Move) (n : ℕ) : List (List Bool) :=
  (allItin n).filter (fun t => decide ((cellZ w t).1 < (cellZ w t).2))

lemma mem_liveItin (w : List Move) (n : ℕ) (t : List Bool) :
    t ∈ liveItin w n ↔ (t.length = n ∧ {x : ℝ | FollowsItin (3/2) w t x}.Nonempty) := by
  rw [liveItin, List.mem_filter, mem_allItin, cell_nonempty_iff]
  simp

/-! ## The `19`-move record word at `λ = 3/2` -/

open Move in
/-- The `19`-move run `MLMLMMMMMLMRLRMLMLM` attaining five simultaneous knots at
`λ = 3/2`. -/
def wordT20 : List Move := [M, L, M, L, M, M, M, M, M, L, M, R, L, R, M, L, M, L, M]

lemma length_wordT20 : wordT20.length = 19 := rfl

/-- The word has eleven `M`'s, hence `2^11 = 2048` candidates. -/
lemma countM_wordT20 : countM wordT20 = 11 := by decide

lemma card_allItin_eleven : (allItin 11).length = 2048 := by decide

/-- **T20, first finite claim.**  Of the `2048` candidates, exactly six are
genuine. -/
theorem candidate_count : (liveItin wordT20 11).length = 6 := by decide

/-- **T20, second finite claim**, in integer form: the six genuine cells have
total length `1048576 / (2·3^19)`. -/
theorem candidate_total_int :
    ((liveItin wordT20 11).map
      (fun t => (cellZ wordT20 t).2 - (cellZ wordT20 t).1)).sum = 1048576 := by
  decide

/-- **T20, second finite claim.**  The six genuine cells tile a set of length
exactly `(2/3)^19 = 524288/1162261467`. -/
theorem candidate_total_length :
    ((((liveItin wordT20 11).map
        (fun t => (cellZ wordT20 t).2 - (cellZ wordT20 t).1)).sum : ℤ) : ℚ)
        / (2 * 3 ^ 19) = (2 / 3 : ℚ) ^ 19 := by
  rw [candidate_total_int]
  norm_num

/-- **T20, put together.**  A point of `(0,1)` survives the record word exactly
when it lies in one — and then exactly one — of the six genuine candidate
cells. -/
theorem candidates_partition_survivorSet (x : ℝ) :
    (0 < x ∧ x < 1 ∧ survivesWord (3/2) x wordT20) ↔
      ∃! t, t ∈ liveItin wordT20 11 ∧ FollowsItin (3/2) wordT20 t x := by
  have h32 : (1:ℝ) < 3/2 := by norm_num
  constructor
  · intro hx
    obtain ⟨t, ht, huniq⟩ := (followsItin_partition h32 wordT20 x).mp hx
    refine ⟨t, ⟨?_, ht⟩, fun t' ht' => huniq t' ht'.2⟩
    rw [mem_liveItin]
    exact ⟨by rw [followsItin_length wordT20 t x ht, countM_wordT20], ⟨x, ht⟩⟩
  · rintro ⟨t, ⟨-, ht⟩, -⟩
    exact (followsItin_partition h32 wordT20 x).mpr
      ⟨t, ht, fun t' ht' => followsItin_unique h32 wordT20 t' t x ht' ht⟩

end KnotGame
