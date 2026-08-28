import RequestProject.KindDim

/-!
# The kind set at `λ = 3/2`: the dimension lower bound

Round 11 (`RequestProject/KindDim.lean`) certified the two *upper* halves of the
paper's `prop:kinddim` at `λ = 3/2`: the kind set `K = K_{3/2}` is Lebesgue null
and `dimH K ≤ log 2 / log 3`.  This file supplies the matching lower bound, and
hence the exact value

* `le_dimH_K` : `log 2 / log 3 ≤ dimH K`;
* `dimH_K_eq` : `dimH K = log 2 / log 3`.

## The argument

The proof is the mass distribution principle, in Mathlib's form
`MeasureTheory.Measure.le_hausdorffMeasure`.  The mass is transported from
Lebesgue measure on `[0,1)` by an explicit *coding map* `G`:

* at every node of the survival tree exactly one of the three moves is fatal
  (round 8's `Ternary.exists_unique_fatal`, available because the reachable
  positions are dyadic and so never sit on a cell boundary), so every node has
  exactly two children; `nextMove y b` names them, `b = false` for the one with
  the smaller base-three digit;
* the binary digits of `t` drive a descent through the tree: `wordOf t n` is the
  node reached after `n` steps, and `G t := ⨆ n, cval (wordOf t n)` is the point
  of `K` it converges to (`G_mem_K`);
* `kindMeasure` is the push-forward of Lebesgue measure on `[0,1)` along `G`;
  it gives `K` mass one (`kindMeasure_K`);
* a set of diameter at most `3^{-n}` meets at most four level-`n` cylinders, and
  the `G`-preimage of a single level-`n` cylinder is one dyadic interval of
  length `2^{-n}`, whence the Frostman estimate
  `kindMeasure A ≤ 4 · 2^{-n}` (`kindMeasure_le`).

The same estimate gives the covering-number bounds `coverK_lower` and
`coverK_upper`, i.e. the box dimension along the triadic scales
(`box_dimension_triadic`).

## Conventions (SCRUPLES)

* The binary digits of `t` are read off the integer parts `⌊2^n t⌋`; no choice
  is involved, and the map `G` is defined for every real `t` (only its values on
  `[0,1)` are used).
* The constant `4` in the Frostman estimate is not optimal; only its finiteness
  matters.
-/

namespace KnotGame
namespace KindLower

open MeasureTheory Set Filter Topology KindDim
open scoped ENNReal Classical

/-! ### The two children of a node -/

/-- The two moves that a knot at `y` survives, ordered by their base-three
digit: `nextMove y false` is the smaller, `nextMove y true` the larger.  (The
ordering is only used through the fact that the two are distinct.) -/
noncomputable def nextMove (y : ℝ) (b : Bool) : Move :=
  if survives (3 / 2 : ℝ) Move.L y then
    if survives (3 / 2 : ℝ) Move.M y then (if b then Move.M else Move.L)
    else (if b then Move.R else Move.L)
  else (if b then Move.R else Move.M)

lemma nextMove_ne (y : ℝ) : nextMove y false ≠ nextMove y true := by
  unfold nextMove
  by_cases hL : survives (3 / 2 : ℝ) Move.L y <;> by_cases hM : survives (3 / 2 : ℝ) Move.M y <;>
    simp [hL, hM]

lemma nextMove_injective (y : ℝ) {b b' : Bool} (h : nextMove y b = nextMove y b') : b = b' := by
  cases b <;> cases b' <;> first
    | rfl
    | exact absurd h (nextMove_ne y)
    | exact absurd h.symm (nextMove_ne y)

/-- If at most one move is fatal at `y`, then both children are legal moves. -/
lemma survives_nextMove {y : ℝ}
    (huniq : ∀ m m' : Move, ¬ survives (3 / 2 : ℝ) m y → ¬ survives (3 / 2 : ℝ) m' y → m = m')
    (b : Bool) : survives (3 / 2 : ℝ) (nextMove y b) y := by
  unfold nextMove
  split_ifs with hL hM hb hb hb
  · exact hM
  · exact hL
  · by_contra hR
    exact absurd (huniq Move.M Move.R hM hR) (by decide)
  · exact hL
  · by_contra hR
    exact absurd (huniq Move.L Move.R hL hR) (by decide)
  · by_contra hM
    exact absurd (huniq Move.L Move.M hL hM) (by decide)

/-! ### Positions along the survival tree -/

/-- The position of the knot born at `1/2` after playing the word `w`. -/
noncomputable def pos (w : List Move) : ℝ := posAfter (3 / 2 : ℝ) (1 / 2 : ℝ) w

lemma posAfter_mem_Ioo : ∀ (w : List Move) {x : ℝ}, 0 < x → x < 1 →
    survivesWord (3 / 2 : ℝ) x w →
      0 < posAfter (3 / 2 : ℝ) x w ∧ posAfter (3 / 2 : ℝ) x w < 1
  | [], _, h0, h1, _ => ⟨h0, h1⟩
  | m :: w, x, h0, h1, hs => by
      obtain ⟨ha0, ha1⟩ := act_mem_Ioo Ternary.one_lt_lam32 ⟨h0, h1⟩ hs.1
      simpa using posAfter_mem_Ioo w ha0 ha1 hs.2

lemma pos_mem_Ioo {w : List Move} (hw : survivesWord (3 / 2 : ℝ) (1 / 2 : ℝ) w) :
    0 < pos w ∧ pos w < 1 :=
  posAfter_mem_Ioo w (by norm_num) (by norm_num) hw

/-- At a reachable position at most one move is fatal. -/
lemma unique_fatal_pos {w : List Move} (hw : survivesWord (3 / 2 : ℝ) (1 / 2 : ℝ) w) :
    ∀ m m' : Move, ¬ survives (3 / 2 : ℝ) m (pos w) → ¬ survives (3 / 2 : ℝ) m' (pos w) →
      m = m' := by
  obtain ⟨h0, h1⟩ := pos_mem_Ioo hw
  have hd : Ternary.Dyadic w.length (pos w) := Ternary.dyadic_posAfter w
  obtain ⟨m₀, -, huniq⟩ :=
    Ternary.exists_unique_fatal h0 h1 (Ternary.three_mul_ne_one hd) (Ternary.three_mul_ne_two hd)
  intro m m' hm hm'
  rw [huniq m hm, huniq m' hm']

/-! ### Binary digits -/

/-- The integer part of `2 ^ n t`. -/
noncomputable def flr (n : ℕ) (t : ℝ) : ℤ := ⌊(2 : ℝ) ^ n * t⌋

/-- The `n`-th binary digit of `t`. -/
noncomputable def bitAt (n : ℕ) (t : ℝ) : Bool := decide (flr (n + 1) t = 2 * flr n t + 1)

lemma flr_succ_cases (n : ℕ) (t : ℝ) :
    flr (n + 1) t = 2 * flr n t ∨ flr (n + 1) t = 2 * flr n t + 1 := by
  have h1 : ((flr n t : ℤ) : ℝ) ≤ 2 ^ n * t := Int.floor_le _
  have h2 : (2:ℝ) ^ n * t < (flr n t : ℝ) + 1 := Int.lt_floor_add_one _
  have hx : (2:ℝ) ^ (n + 1) * t = 2 * (2 ^ n * t) := by ring
  have hlow : ((2 * flr n t : ℤ) : ℝ) ≤ 2 ^ (n + 1) * t := by push_cast; rw [hx]; linarith
  have hhigh : (2:ℝ) ^ (n + 1) * t < ((2 * flr n t + 2 : ℤ) : ℝ) := by
    push_cast; rw [hx]; linarith
  have hle : 2 * flr n t ≤ flr (n + 1) t := Int.le_floor.mpr hlow
  have hlt : flr (n + 1) t < 2 * flr n t + 2 := Int.floor_lt.mpr hhigh
  omega

lemma flr_succ_eq (n : ℕ) (t : ℝ) :
    flr (n + 1) t = 2 * flr n t + (if bitAt n t then 1 else 0) := by
  rcases flr_succ_cases n t with h | h
  · have hb : bitAt n t = false := by
      simp only [bitAt, decide_eq_false_iff_not]
      omega
    rw [hb]
    simpa using h
  · have hb : bitAt n t = true := by
      simp only [bitAt, decide_eq_true_eq]
      exact h
    rw [hb]
    simpa using h

lemma flr_congr_of_succ {n : ℕ} {t s : ℝ} (h : flr (n + 1) t = flr (n + 1) s) :
    flr n t = flr n s ∧ bitAt n t = bitAt n s := by
  have hfst : flr n t = flr n s := by
    rcases flr_succ_cases n t with ht | ht <;> rcases flr_succ_cases n s with hs | hs <;> omega
  refine ⟨hfst, ?_⟩
  unfold bitAt
  rw [h, hfst]

lemma flr_congr_add : ∀ (i d : ℕ) {t s : ℝ}, flr (i + d) t = flr (i + d) s → flr i t = flr i s := by
  intro i d
  induction d with
  | zero => intro t s h; simpa using h
  | succ d ih =>
      intro t s h
      refine ih ?_
      have h' : flr ((i + d) + 1) t = flr ((i + d) + 1) s := h
      exact (flr_congr_of_succ h').1

lemma flr_congr_of_le {i n : ℕ} (hin : i ≤ n) {t s : ℝ} (h : flr n t = flr n s) :
    flr i t = flr i s := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hin
  exact flr_congr_add i d h

lemma bitAt_congr {i n : ℕ} (hin : i < n) {t s : ℝ} (h : flr n t = flr n s) :
    bitAt i t = bitAt i s :=
  (flr_congr_of_succ (flr_congr_of_le hin h)).2

/-! ### The coding map -/

/-- The node of the survival tree reached after `n` steps of the descent driven
by the binary digits of `t`. -/
noncomputable def wordOf (t : ℝ) : ℕ → List Move
  | 0 => []
  | n + 1 => wordOf t n ++ [nextMove (pos (wordOf t n)) (bitAt n t)]

@[simp] lemma wordOf_zero (t : ℝ) : wordOf t 0 = [] := rfl

lemma wordOf_succ (t : ℝ) (n : ℕ) :
    wordOf t (n + 1) = wordOf t n ++ [nextMove (pos (wordOf t n)) (bitAt n t)] := rfl

lemma wordOf_length (t : ℝ) (n : ℕ) : (wordOf t n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [wordOf_succ, ih]

lemma wordOf_survives (t : ℝ) (n : ℕ) : survivesWord (3 / 2 : ℝ) (1 / 2 : ℝ) (wordOf t n) := by
  induction n with
  | zero => trivial
  | succ n ih =>
      rw [wordOf_succ, survivesWord_append]
      exact ⟨ih, ⟨survives_nextMove (unique_fatal_pos ih) _, trivial⟩⟩

lemma wordOf_mem_kindWords (t : ℝ) (n : ℕ) :
    wordOf t n ∈ KindTree.kindWords (3 / 2 : ℝ) (1 / 2 : ℝ) n :=
  KindTree.mem_kindWords.mpr ⟨wordOf_length t n, wordOf_survives t n⟩

lemma wordOf_le_append (t : ℝ) {n m : ℕ} (h : n ≤ m) :
    ∃ u : List Move, wordOf t m = wordOf t n ++ u := by
  induction m with
  | zero => exact ⟨[], by rw [Nat.le_zero.mp h]; simp⟩
  | succ m ih =>
      rcases Nat.eq_or_lt_of_le h with rfl | hlt
      · exact ⟨[], by simp⟩
      · obtain ⟨u, hu⟩ := ih (Nat.lt_succ_iff.mp hlt)
        exact ⟨u ++ [nextMove (pos (wordOf t m)) (bitAt m t)], by
          rw [wordOf_succ, hu, List.append_assoc]⟩

/-! ### Cylinders along the descent -/

lemma cval_mem_cyl (w : List Move) : cval w ∈ cyl w := by
  constructor
  · exact le_rfl
  · have : (0:ℝ) < (1/3 : ℝ) ^ w.length := by positivity
    linarith

lemma cyl_append (v : List Move) : ∀ u : List Move, cyl (v ++ u) ⊆ cyl v := by
  intro u
  induction u using List.reverseRecOn with
  | nil => simp
  | append_singleton u m ih =>
      have : v ++ (u ++ [m]) = (v ++ u) ++ [m] := by simp
      rw [this]
      exact (cyl_append_subset (v ++ u) m).trans ih

/-- The point of `K` coded by the binary digits of `t`. -/
noncomputable def G (t : ℝ) : ℝ := ⨆ n, cval (wordOf t n)

lemma cval_le_one (w : List Move) : cval w ≤ 1 := by
  have h := cval_add_le_one w
  have : (0:ℝ) < (1/3 : ℝ) ^ w.length := by positivity
  linarith

lemma bddAbove_cval (t : ℝ) : BddAbove (range fun n => cval (wordOf t n)) := by
  refine ⟨1, ?_⟩
  rintro y ⟨n, rfl⟩
  exact cval_le_one _

lemma cval_wordOf_mem_cyl (t : ℝ) {n m : ℕ} (h : n ≤ m) : cval (wordOf t m) ∈ cyl (wordOf t n) := by
  obtain ⟨u, hu⟩ := wordOf_le_append t h
  have := cval_mem_cyl (wordOf t m)
  rw [hu] at this ⊢
  exact cyl_append _ _ this

lemma monotone_cval_wordOf (t : ℝ) : Monotone fun n => cval (wordOf t n) := by
  intro n m h
  exact (cval_wordOf_mem_cyl t h).1

lemma G_mem_cyl (t : ℝ) (n : ℕ) : G t ∈ cyl (wordOf t n) := by
  constructor
  · exact le_ciSup (bddAbove_cval t) n
  · refine ciSup_le fun m => ?_
    rcases le_total n m with h | h
    · exact (cval_wordOf_mem_cyl t h).2
    · exact le_trans (monotone_cval_wordOf t h) (cval_mem_cyl (wordOf t n)).2

lemma G_mem_K (t : ℝ) : G t ∈ K := by
  refine Set.mem_iInter.mpr fun n => ?_
  exact Set.mem_biUnion (wordOf_mem_kindWords t n) (G_mem_cyl t n)

/-! ### Measurability -/

/-- The node reached after `n` steps, as a function of `⌊2^n t⌋`. -/
noncomputable def wrd (n : ℕ) (k : ℤ) : List Move := wordOf ((k : ℝ) / 2 ^ n) n

lemma flr_of_div (n : ℕ) (k : ℤ) : flr n ((k : ℝ) / 2 ^ n) = k := by
  have h : (2:ℝ) ^ n * ((k : ℝ) / 2 ^ n) = (k : ℝ) := by
    have : ((2:ℝ) ^ n) ≠ 0 := by positivity
    field_simp
  unfold flr
  rw [h, Int.floor_intCast]

lemma wordOf_congr : ∀ (n : ℕ) {t s : ℝ}, flr n t = flr n s → wordOf t n = wordOf s n := by
  intro n
  induction n with
  | zero => intro t s _; rfl
  | succ n ih =>
      intro t s h
      obtain ⟨h1, h2⟩ := flr_congr_of_succ h
      rw [wordOf_succ, wordOf_succ, ih h1, h2]

lemma wordOf_eq_wrd (t : ℝ) (n : ℕ) : wordOf t n = wrd n (flr n t) := by
  refine wordOf_congr n ?_
  rw [flr_of_div]

lemma measurable_flr (n : ℕ) : Measurable (flr n) :=
  (measurable_const.mul measurable_id).floor

lemma measurable_cval_wordOf (n : ℕ) : Measurable fun t => cval (wordOf t n) := by
  have : (fun t => cval (wordOf t n)) = (fun k : ℤ => cval (wrd n k)) ∘ (flr n) := by
    funext t; simp [Function.comp, wordOf_eq_wrd t n]
  rw [this]
  exact measurable_from_top.comp (measurable_flr n)

lemma tendsto_cval_wordOf (t : ℝ) :
    Tendsto (fun n => cval (wordOf t n)) atTop (𝓝 (G t)) :=
  tendsto_atTop_ciSup (monotone_cval_wordOf t) (bddAbove_cval t)

lemma measurable_G : Measurable G := by
  refine measurable_of_tendsto_metrizable (f := fun n t => cval (wordOf t n))
    (fun n => measurable_cval_wordOf n) ?_
  rw [tendsto_pi_nhds]
  exact fun t => tendsto_cval_wordOf t

/-! ### The mass distribution -/

/-- The mass distribution on the kind set: the push-forward of Lebesgue measure
on `[0,1)` along the coding map. -/
noncomputable def kindMeasure : Measure ℝ := Measure.map G (volume.restrict (Ico (0:ℝ) 1))

lemma measurableSet_E (n : ℕ) : MeasurableSet (E n) := by
  rw [E, ← Finset.set_biUnion_coe]
  refine MeasurableSet.biUnion (Finset.countable_toSet _) fun w _ => ?_
  rw [cyl]
  exact measurableSet_Icc

lemma measurableSet_K : MeasurableSet K :=
  MeasurableSet.iInter fun n => measurableSet_E n

/-- The kind set carries all the mass. -/
theorem kindMeasure_K : kindMeasure K = 1 := by
  rw [kindMeasure, Measure.map_apply measurable_G measurableSet_K]
  have hpre : G ⁻¹' K = univ := by
    ext t; simp [G_mem_K t]
  rw [hpre, Measure.restrict_apply_univ, Real.volume_Ico]
  norm_num

/-! ### The Frostman estimate -/

/-- The base-three numerator of a word: `cval w = cnum w / 3 ^ |w|`. -/
def cnum : List Move → ℤ
  | [] => 0
  | m :: w => (dig m : ℤ) * 3 ^ w.length + cnum w

lemma dig_injective {m m' : Move} (h : dig m = dig m') : m = m' := by
  cases m <;> cases m' <;> simp_all [dig]

lemma cnum_nonneg : ∀ w : List Move, 0 ≤ cnum w
  | [] => le_rfl
  | m :: w => by
      have hw := cnum_nonneg w
      have h : (0:ℤ) ≤ (dig m : ℤ) * 3 ^ w.length := by positivity
      simp only [cnum]
      linarith

lemma cnum_lt : ∀ w : List Move, cnum w < 3 ^ w.length
  | [] => by simp [cnum]
  | m :: w => by
      have hw := cnum_lt w
      have hd : (dig m : ℤ) ≤ 2 := by exact_mod_cast dig_le_two m
      have h3 : (0:ℤ) < 3 ^ w.length := by positivity
      simp only [cnum, List.length_cons, pow_succ]
      nlinarith

lemma cval_eq_cnum : ∀ w : List Move, cval w = (cnum w : ℝ) / 3 ^ w.length
  | [] => by simp [cnum]
  | m :: w => by
      have ih := cval_eq_cnum w
      have h3 : ((3:ℝ) ^ w.length) ≠ 0 := by positivity
      simp only [cval_cons, cnum, List.length_cons, ih]
      push_cast
      field_simp
      ring

lemma cnum_injective : ∀ (v w : List Move), v.length = w.length → cnum v = cnum w → v = w := by
  intro v
  induction v with
  | nil =>
      intro w hl _
      cases w with
      | nil => rfl
      | cons m' w => simp at hl
  | cons m v ih =>
      intro w hl h
      cases w with
      | nil => simp at hl
      | cons m' w =>
          have hlen : v.length = w.length := by simpa using hl
          have hv := cnum_lt v
          have hw := cnum_lt w
          have hv0 := cnum_nonneg v
          have hw0 := cnum_nonneg w
          have h3 : (0:ℤ) < 3 ^ w.length := by positivity
          simp only [cnum, hlen] at h
          have hd : (dig m : ℤ) = (dig m' : ℤ) := by
            rcases lt_trichotomy (dig m : ℤ) (dig m' : ℤ) with hlt | heq | hgt
            · exfalso
              have : (dig m : ℤ) + 1 ≤ (dig m' : ℤ) := hlt
              nlinarith [hlen ▸ hv]
            · exact heq
            · exfalso
              have : (dig m' : ℤ) + 1 ≤ (dig m : ℤ) := hgt
              nlinarith [hlen ▸ hv]
          have hm : m = m' := dig_injective (by exact_mod_cast hd)
          have hc : cnum v = cnum w := by
            rw [hd] at h; linarith
          rw [hm, ih w hlen hc]

/-- The word read off the descent determines the dyadic index it came from. -/
lemma flr_eq_of_wordOf_eq : ∀ (n : ℕ) {t s : ℝ}, flr 0 t = flr 0 s → wordOf t n = wordOf s n →
    flr n t = flr n s := by
  intro n
  induction n with
  | zero => intro t s h0 _; exact h0
  | succ n ih =>
      intro t s h0 h
      rw [wordOf_succ, wordOf_succ] at h
      have hlen : (wordOf t n).length = (wordOf s n).length := by
        rw [wordOf_length, wordOf_length]
      obtain ⟨hw, hlast⟩ := List.append_inj h hlen
      have hn := ih h0 hw
      have hb : bitAt n t = bitAt n s := by
        have hmv : nextMove (pos (wordOf t n)) (bitAt n t)
            = nextMove (pos (wordOf s n)) (bitAt n s) := by
          simpa using hlast
        rw [hw] at hmv
        exact nextMove_injective _ hmv
      rw [flr_succ_eq n t, flr_succ_eq n s, hn, hb]

/-- Distinct dyadic indices give distinct nodes. -/
lemma wrd_injective {n : ℕ} {k k' : ℤ} (hk : 0 ≤ k) (hk' : k < 2 ^ n) (hl : 0 ≤ k')
    (hl' : k' < 2 ^ n) (h : wrd n k = wrd n k') : k = k' := by
  have hfloor : ∀ j : ℤ, 0 ≤ j → j < 2 ^ n → flr 0 ((j : ℝ) / 2 ^ n) = 0 := by
    intro j hj0 hj1
    have h2 : (0:ℝ) < 2 ^ n := by positivity
    have hj0' : (0:ℝ) ≤ (j : ℝ) := by exact_mod_cast hj0
    have hj1' : (j : ℝ) < 2 ^ n := by exact_mod_cast hj1
    have h1 : (0:ℝ) ≤ (j : ℝ) / 2 ^ n := by positivity
    have h2' : (j : ℝ) / 2 ^ n < 1 := by rw [div_lt_one h2]; exact hj1'
    unfold flr
    simp only [pow_zero, one_mul]
    exact Int.floor_eq_zero_iff.mpr ⟨h1, h2'⟩
  have h0 : flr 0 ((k : ℝ) / 2 ^ n) = flr 0 ((k' : ℝ) / 2 ^ n) := by
    rw [hfloor k hk hk', hfloor k' hl hl']
  have := flr_eq_of_wordOf_eq n h0 h
  rwa [flr_of_div, flr_of_div] at this

/-- **The Frostman estimate.**  A set of diameter at most `3^{-n}` has mass at
most `4 · 2^{-n}`. -/
theorem kindMeasure_le (n : ℕ) {A : Set ℝ} (hA : MeasurableSet A)
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, |x - y| ≤ (1/3 : ℝ) ^ n) :
    kindMeasure A ≤ ENNReal.ofReal (4 * (1/2 : ℝ) ^ n) := by
  classical
  rcases A.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simp
  have h2 : (0:ℝ) < 2 ^ n := by positivity
  have h3 : (0:ℝ) < 3 ^ n := by positivity
  have hthird : (1/3:ℝ) ^ n = 1 / 3 ^ n := by rw [div_pow, one_pow]
  set S : Finset ℤ :=
    (Finset.Ico (0:ℤ) (2 ^ n)).filter (fun k => (cyl (wrd n k) ∩ A).Nonempty) with hSdef
  have hmemS : ∀ k ∈ S, 0 ≤ k ∧ k < 2 ^ n ∧ (cyl (wrd n k) ∩ A).Nonempty := by
    intro k hk
    rw [hSdef, Finset.mem_filter, Finset.mem_Ico] at hk
    exact ⟨hk.1.1, hk.1.2, hk.2⟩
  -- (1) the dyadic covering of the preimage
  have hcover : G ⁻¹' A ∩ Ico (0:ℝ) 1 ⊆ ⋃ k ∈ S, Ico ((k : ℝ) / 2 ^ n) (((k : ℝ) + 1) / 2 ^ n) := by
    intro t ht
    obtain ⟨htA, ht0, ht1⟩ : t ∈ G ⁻¹' A ∧ 0 ≤ t ∧ t < 1 := ⟨ht.1, ht.2.1, ht.2.2⟩
    have hkle : ((flr n t : ℤ) : ℝ) ≤ 2 ^ n * t := Int.floor_le _
    have hklt : (2:ℝ) ^ n * t < (flr n t : ℝ) + 1 := Int.lt_floor_add_one _
    have hk0 : 0 ≤ flr n t := by
      refine Int.le_floor.mpr ?_
      push_cast
      positivity
    have hk1 : flr n t < 2 ^ n := by
      refine Int.floor_lt.mpr ?_
      push_cast
      nlinarith
    have hmem : t ∈ Ico ((flr n t : ℝ) / 2 ^ n) (((flr n t : ℝ) + 1) / 2 ^ n) := by
      constructor
      · rw [div_le_iff₀ h2]; linarith
      · rw [lt_div_iff₀ h2]; linarith
    have hkS : flr n t ∈ S := by
      rw [hSdef, Finset.mem_filter, Finset.mem_Ico]
      exact ⟨⟨hk0, hk1⟩, ⟨G t, by rw [← wordOf_eq_wrd t n]; exact G_mem_cyl t n, htA⟩⟩
    exact Set.mem_biUnion hkS hmem
  -- (2) at most four cylinders of level `n` meet a set of diameter `3 ^ -n`
  have hcard : S.card ≤ 4 := by
    have hprod : (1/3:ℝ) ^ n * 3 ^ n = 1 := by rw [← mul_pow]; norm_num
    have hsub : ∀ k ∈ S,
        cnum (wrd n k) ∈ Finset.Icc ⌈(3:ℝ) ^ n * a - 2⌉ ⌊(3:ℝ) ^ n * a + 1⌋ := by
      intro k hk
      obtain ⟨-, -, x, hx1, hx2⟩ := hmemS k hk
      have hlen : (wrd n k).length = n := by rw [wrd, wordOf_length]
      have hcv : cval (wrd n k) = (cnum (wrd n k) : ℝ) / 3 ^ n := by
        rw [cval_eq_cnum, hlen]
      have hx1a : cval (wrd n k) ≤ x := hx1.1
      have hx1b : x ≤ cval (wrd n k) + (1/3:ℝ) ^ n := by
        have := hx1.2; rwa [hlen] at this
      obtain ⟨hd1, hd2⟩ := abs_le.mp (hdiam x hx2 a ha)
      rw [hcv] at hx1a hx1b
      have e1 : -1 ≤ (x - a) * 3 ^ n := by
        have h := mul_le_mul_of_nonneg_right hd1 (le_of_lt h3)
        rwa [neg_mul, hprod] at h
      have e2 : (x - a) * 3 ^ n ≤ 1 := by
        have h := mul_le_mul_of_nonneg_right hd2 (le_of_lt h3)
        rwa [hprod] at h
      have e3 : (cnum (wrd n k) : ℝ) ≤ x * 3 ^ n := by
        rw [div_le_iff₀ h3] at hx1a; exact hx1a
      have e4 : x * 3 ^ n ≤ (cnum (wrd n k) : ℝ) + 1 := by
        have h := mul_le_mul_of_nonneg_right hx1b (le_of_lt h3)
        rwa [add_mul, div_mul_cancel₀ _ (ne_of_gt h3), hprod] at h
      rw [Finset.mem_Icc]
      exact ⟨Int.ceil_le.mpr (by linarith), Int.le_floor.mpr (by linarith)⟩
    have hinj : Set.InjOn (fun k => cnum (wrd n k)) (S : Set ℤ) := by
      intro k hk k' hk' h
      obtain ⟨hk0, hk1, -⟩ := hmemS k (by simpa using hk)
      obtain ⟨hl0, hl1, -⟩ := hmemS k' (by simpa using hk')
      have hlen : (wrd n k).length = (wrd n k').length := by
        rw [wrd, wrd, wordOf_length, wordOf_length]
      exact wrd_injective hk0 hk1 hl0 hl1 (cnum_injective _ _ hlen h)
    have hle := Finset.card_le_card_of_injOn
      (t := Finset.Icc ⌈(3:ℝ) ^ n * a - 2⌉ ⌊(3:ℝ) ^ n * a + 1⌋)
      (fun k => cnum (wrd n k)) (fun k hk => hsub k hk) hinj
    refine le_trans hle ?_
    rw [Int.card_Icc]
    have hfl : ((⌊(3:ℝ) ^ n * a + 1⌋ : ℤ) : ℝ) ≤ (3:ℝ) ^ n * a + 1 := Int.floor_le _
    have hce : (3:ℝ) ^ n * a - 2 ≤ ((⌈(3:ℝ) ^ n * a - 2⌉ : ℤ) : ℝ) := Int.le_ceil _
    have hdiff : (⌊(3:ℝ) ^ n * a + 1⌋ : ℤ) - ⌈(3:ℝ) ^ n * a - 2⌉ ≤ 3 := by
      have : ((⌊(3:ℝ) ^ n * a + 1⌋ - ⌈(3:ℝ) ^ n * a - 2⌉ : ℤ) : ℝ) ≤ 3 := by push_cast; linarith
      exact_mod_cast this
    omega
  -- (3) the measure estimate
  have hmeas : kindMeasure A ≤ ∑ _k ∈ S, ENNReal.ofReal ((1/2:ℝ) ^ n) := by
    rw [kindMeasure, Measure.map_apply measurable_G hA,
      Measure.restrict_apply (measurable_G hA)]
    refine le_trans (measure_mono hcover) ?_
    refine le_trans (measure_biUnion_finset_le S _) ?_
    refine Finset.sum_le_sum fun k _ => ?_
    have hval : ((k:ℝ) + 1) / 2 ^ n - (k:ℝ) / 2 ^ n = (1/2:ℝ) ^ n := by
      rw [div_pow, one_pow]
      field_simp
      ring
    rw [Real.volume_Ico, hval]
  calc kindMeasure A ≤ ∑ _k ∈ S, ENNReal.ofReal ((1/2:ℝ) ^ n) := hmeas
    _ = (S.card : ℝ≥0∞) * ENNReal.ofReal ((1/2:ℝ) ^ n) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (4 : ℝ≥0∞) * ENNReal.ofReal ((1/2:ℝ) ^ n) := by
        gcongr
        exact_mod_cast hcard
    _ = ENNReal.ofReal (4 * (1/2:ℝ) ^ n) := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num

/-! ### The dimension -/

lemma abs_sub_le_of_ediam {s : Set ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : Metric.ediam s ≤ ENNReal.ofReal c) : ∀ x ∈ s, ∀ y ∈ s, |x - y| ≤ c := by
  intro x hx y hy
  have h1 : edist x y ≤ ENNReal.ofReal c := le_trans (Metric.edist_le_ediam_of_mem hx hy) h
  rw [edist_dist] at h1
  have h2 := (ENNReal.ofReal_le_ofReal_iff hc).mp h1
  rwa [Real.dist_eq] at h2

lemma exists_pow_bracket {r : ℝ} (hr : 0 < r) (hr3 : r ≤ 1/3) :
    ∃ n : ℕ, (1/3:ℝ) ^ (n + 1) ≤ r ∧ r ≤ (1/3:ℝ) ^ n := by
  classical
  have hex : ∃ n : ℕ, (1/3:ℝ) ^ n < r := exists_pow_lt_of_lt_one hr (by norm_num)
  have hN : (1/3:ℝ) ^ Nat.find hex < r := Nat.find_spec hex
  have hN0 : Nat.find hex ≠ 0 := by
    intro h
    rw [h, pow_zero] at hN
    linarith
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hN0
  rw [hm] at hN
  refine ⟨m, le_of_lt hN, ?_⟩
  have hmin := Nat.find_min hex (m := m) (by omega)
  push_neg at hmin
  exact hmin

/-- The Frostman estimate in the form the mass distribution principle wants. -/
lemma kindMeasure_le_of_ediam (n : ℕ) {s : Set ℝ}
    (hn : Metric.ediam s ≤ ENNReal.ofReal ((1/3:ℝ) ^ n)) :
    kindMeasure s ≤ ENNReal.ofReal (4 * (1/2:ℝ) ^ n) := by
  refine le_trans (measure_mono subset_closure) ?_
  refine kindMeasure_le n measurableSet_closure ?_
  refine abs_sub_le_of_ediam (by positivity) ?_
  rwa [Metric.ediam_closure]

/-- **The lower bound.**  The kind set at `λ = 3/2` has Hausdorff dimension at
least `log 2 / log 3`. -/
theorem le_dimH_K : ENNReal.ofReal dexp ≤ dimH K := by
  have hdom : (ENNReal.ofReal (1/8 : ℝ)) • kindMeasure ≤ μH[dexp] := by
    refine Measure.le_hausdorffMeasure dexp _ (ENNReal.ofReal (1/3 : ℝ)) (by simp) ?_
    intro s hs
    have hne : Metric.ediam s ≠ ⊤ := ne_top_of_le_ne_top (by simp) hs
    set r : ℝ := (Metric.ediam s).toReal with hrdef
    have he : Metric.ediam s = ENNReal.ofReal r := (ENNReal.ofReal_toReal hne).symm
    have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
    have hr13 : r ≤ 1/3 := by
      have := ENNReal.toReal_mono (by simp) hs
      rwa [ENNReal.toReal_ofReal (by norm_num)] at this
    rcases eq_or_lt_of_le hr0 with hzero | hpos
    · -- a set of diameter zero has no mass at all
      have hmass : kindMeasure s = 0 := by
        have htend : Tendsto (fun n : ℕ => ENNReal.ofReal (4 * (1/2:ℝ) ^ n)) atTop (𝓝 0) := by
          have h : Tendsto (fun n : ℕ => 4 * (1/2:ℝ) ^ n) atTop (𝓝 0) := by
            have hbase : Tendsto (fun n : ℕ => (1/2:ℝ) ^ n) atTop (𝓝 0) :=
              tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
            simpa using hbase.const_mul (4:ℝ)
          have h2 := (ENNReal.continuous_ofReal.tendsto 0).comp h
          rwa [ENNReal.ofReal_zero] at h2
        refine le_antisymm (ge_of_tendsto htend (Eventually.of_forall fun n => ?_)) (zero_le _)
        refine kindMeasure_le_of_ediam n ?_
        rw [he, ← hzero]
        simp only [ENNReal.ofReal_zero]
        exact zero_le _
      rw [Measure.smul_apply, smul_eq_mul, hmass, mul_zero]
      exact zero_le _
    · obtain ⟨n, hlow, hhigh⟩ := exists_pow_bracket hpos hr13
      have hkm : kindMeasure s ≤ ENNReal.ofReal (4 * (1/2:ℝ) ^ n) :=
        kindMeasure_le_of_ediam n (by rw [he]; exact ENNReal.ofReal_le_ofReal hhigh)
      calc (ENNReal.ofReal (1/8:ℝ) • kindMeasure) s
          = ENNReal.ofReal (1/8:ℝ) * kindMeasure s := by
            rw [Measure.smul_apply, smul_eq_mul]
        _ ≤ ENNReal.ofReal (1/8:ℝ) * ENNReal.ofReal (4 * (1/2:ℝ) ^ n) := by gcongr
        _ = ENNReal.ofReal ((1/2:ℝ) ^ (n + 1)) := by
            rw [← ENNReal.ofReal_mul (by norm_num)]
            congr 1
            rw [pow_succ]
            ring
        _ = ENNReal.ofReal ((((1/3:ℝ)) ^ (n + 1)) ^ dexp) := by rw [rpow_pow_third_dexp]
        _ = (ENNReal.ofReal ((1/3:ℝ) ^ (n + 1))) ^ dexp := by
            rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) dexp_pos.le]
        _ ≤ (ENNReal.ofReal r) ^ dexp :=
            ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hlow) dexp_pos.le
        _ = Metric.ediam s ^ dexp := by rw [he]
  have hK : μH[dexp] K ≠ 0 := by
    have h1 : (ENNReal.ofReal (1/8:ℝ) • kindMeasure) K ≤ μH[dexp] K := hdom K
    rw [Measure.smul_apply, smul_eq_mul, kindMeasure_K, mul_one] at h1
    intro h0
    rw [h0] at h1
    have hzero : ENNReal.ofReal (1/8:ℝ) = 0 := le_antisymm h1 (zero_le _)
    simp at hzero
  have hd : μH[(dexp.toNNReal : ℝ)] K ≠ 0 := by
    rwa [Real.coe_toNNReal _ dexp_pos.le]
  have hfin := le_dimH_of_hausdorffMeasure_ne_zero hd
  rwa [show ((dexp.toNNReal : NNReal) : ℝ≥0∞) = ENNReal.ofReal dexp from rfl] at hfin

/-- **Paper `prop:kinddim`, the Hausdorff dimension.**  The kind set at
`λ = 3/2` has Hausdorff dimension exactly `log 2 / log 3`. -/
theorem dimH_K_eq : dimH K = ENNReal.ofReal dexp :=
  le_antisymm dimH_K_le le_dimH_K

end KindLower
end KnotGame
