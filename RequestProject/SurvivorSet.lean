import RequestProject.Gaps

/-!
# T14 — the structure of the survivor set (paper Lemma `lem:survivorset`)

`S(v)` is the set of starting points `x ∈ (0,1)` that survive the word `v`.
This file builds, by recursion from the right through the inverse branches, an
explicit finite list `cells lam v` of *disjoint open intervals*, listed from
left to right, whose union is exactly `S(v)`, and proves:

* `inCells_cells` — the union of the cells is `S(v)`;
* `tidy_cells` — the cells are nonempty open intervals inside `[0,1]`,
  pairwise disjoint and increasing;
* `sum_cells` — the total length of the cells is exactly `r ^ |v|`;
* `length_cells_le` — there are at most `1 + #{M's in v}` cells;
* `exists_long_cell` — hence some cell has length at least `r ^ |v| / (|v|+1)`;
* `volume_survivorSet` — the Lebesgue measure of `S(v)` is `r ^ |v|`.

The intervals are open because survival is defined by strict inequalities.
-/

namespace KnotGame

open scoped BigOperators

variable {lam : ℝ}

/-- `x` lies in the union of the open intervals listed by `L`. -/
def inCells (L : List (ℝ × ℝ)) (x : ℝ) : Prop := ∃ p ∈ L, p.1 < x ∧ x < p.2

/-- The invariant carried by the cell lists: each entry is a nonempty open
subinterval of `[0,1]`, and the entries are listed from left to right with
disjoint interiors. -/
structure Tidy (L : List (ℝ × ℝ)) : Prop where
  bounds : ∀ p ∈ L, 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 1
  sorted : L.Pairwise (fun p q => p.2 ≤ q.1)

lemma Tidy.tail {p : ℝ × ℝ} {t : List (ℝ × ℝ)} (h : Tidy (p :: t)) : Tidy t :=
  ⟨fun q hq => h.bounds q (List.mem_cons_of_mem _ hq), (List.pairwise_cons.mp h.sorted).2⟩

lemma Tidy.head_le {p : ℝ × ℝ} {t : List (ℝ × ℝ)} (h : Tidy (p :: t)) :
    ∀ q ∈ t, p.2 ≤ q.1 := (List.pairwise_cons.mp h.sorted).1

/-! ## Splitting the cells at `1/2` -/

/-- Splitting every cell at `1/2`: this removes the single point `1/2` from the
union and increases the number of cells by at most one. -/
noncomputable def splitHalf : List (ℝ × ℝ) → List (ℝ × ℝ)
  | [] => []
  | p :: t =>
      if p.2 ≤ 1/2 then p :: splitHalf t
      else if p.1 < 1/2 then (p.1, 1/2) :: (1/2, p.2) :: t
      else p :: t

lemma splitHalf_length_le : ∀ L : List (ℝ × ℝ), (splitHalf L).length ≤ L.length + 1
  | [] => by simp [splitHalf]
  | p :: t => by
      rw [splitHalf]
      split
      · have := splitHalf_length_le t
        simp only [List.length_cons]
        omega
      · split <;> simp

lemma splitHalf_ne_nil : ∀ {L : List (ℝ × ℝ)}, L ≠ [] → splitHalf L ≠ []
  | [], h => absurd rfl h
  | p :: t, _ => by
      rw [splitHalf]
      split
      · simp
      · split <;> simp

lemma splitHalf_sum : ∀ L : List (ℝ × ℝ),
    ((splitHalf L).map (fun p => p.2 - p.1)).sum = (L.map (fun p => p.2 - p.1)).sum
  | [] => by simp [splitHalf]
  | p :: t => by
      rw [splitHalf]
      split
      · simp [splitHalf_sum t]
      · split
        · simp; ring
        · simp

/-- Every cell produced by the split starts no further left than some original
cell. -/
lemma splitHalf_fst_mem : ∀ (L : List (ℝ × ℝ)), ∀ q ∈ splitHalf L, ∃ p ∈ L, p.1 ≤ q.1
  | [], q, hq => by simp [splitHalf] at hq
  | p :: t, q, hq => by
      rw [splitHalf] at hq
      split at hq
      · rcases List.mem_cons.mp hq with rfl | hq
        · exact ⟨q, List.mem_cons_self .., le_refl _⟩
        · obtain ⟨s, hs, hsq⟩ := splitHalf_fst_mem t q hq
          exact ⟨s, List.mem_cons_of_mem _ hs, hsq⟩
      · split at hq
        · rename_i hlt
          rcases List.mem_cons.mp hq with rfl | hq
          · exact ⟨p, List.mem_cons_self .., le_refl _⟩
          · rcases List.mem_cons.mp hq with rfl | hq
            · exact ⟨p, List.mem_cons_self .., le_of_lt hlt⟩
            · exact ⟨q, List.mem_cons_of_mem _ hq, le_refl _⟩
        · rcases List.mem_cons.mp hq with rfl | hq
          · exact ⟨q, List.mem_cons_self .., le_refl _⟩
          · exact ⟨q, List.mem_cons_of_mem _ hq, le_refl _⟩

lemma tidy_splitHalf : ∀ {L : List (ℝ × ℝ)}, Tidy L → Tidy (splitHalf L)
  | [], h => by simpa [splitHalf] using h
  | p :: t, h => by
      have hp := h.bounds p (List.mem_cons_self ..)
      have hht := h.head_le
      have ht : Tidy t := h.tail
      rw [splitHalf]
      split
      · rename_i hle
        have hst := tidy_splitHalf ht
        refine ⟨?_, ?_⟩
        · intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact hp
          · exact hst.bounds q hq
        · rw [List.pairwise_cons]
          refine ⟨?_, hst.sorted⟩
          intro q hq
          obtain ⟨s, hs, hsq⟩ := splitHalf_fst_mem t q hq
          exact le_trans (hht s hs) hsq
      · rename_i hgt
        push_neg at hgt
        split
        · rename_i hlt
          refine ⟨?_, ?_⟩
          · intro q hq
            rcases List.mem_cons.mp hq with rfl | hq
            · exact ⟨hp.1, hlt, by norm_num⟩
            · rcases List.mem_cons.mp hq with rfl | hq
              · exact ⟨by norm_num, hgt, hp.2.2⟩
              · exact ht.bounds q hq
          · rw [List.pairwise_cons]
            refine ⟨?_, ?_⟩
            · intro q hq
              rcases List.mem_cons.mp hq with rfl | hq
              · exact le_refl _
              · exact le_trans (le_of_lt hgt) (hht q hq)
            · rw [List.pairwise_cons]
              exact ⟨fun q hq => hht q hq, ht.sorted⟩
        · exact h

/-- After the split no cell contains `1/2`: each one lies on one side of it. -/
lemma splitHalf_side : ∀ {L : List (ℝ × ℝ)}, Tidy L →
    ∀ q ∈ splitHalf L, q.2 ≤ 1/2 ∨ 1/2 ≤ q.1
  | [], _, q, hq => by simp [splitHalf] at hq
  | p :: t, h, q, hq => by
      have hp := h.bounds p (List.mem_cons_self ..)
      have hht := h.head_le
      have ht : Tidy t := h.tail
      rw [splitHalf] at hq
      split at hq
      · rename_i hle
        rcases List.mem_cons.mp hq with rfl | hq
        · exact Or.inl hle
        · exact splitHalf_side ht q hq
      · rename_i hgt
        push_neg at hgt
        split at hq
        · rename_i hlt
          rcases List.mem_cons.mp hq with rfl | hq
          · exact Or.inl (le_refl _)
          · rcases List.mem_cons.mp hq with rfl | hq
            · exact Or.inr (le_refl _)
            · exact Or.inr (le_trans (le_of_lt hgt) (hht q hq))
        · rename_i hnlt
          push_neg at hnlt
          rcases List.mem_cons.mp hq with rfl | hq
          · exact Or.inr hnlt
          · exact Or.inr (le_trans hnlt (le_trans (le_of_lt hp.2.1) (hht q hq)))

lemma inCells_splitHalf : ∀ {L : List (ℝ × ℝ)}, Tidy L → ∀ x : ℝ,
    (inCells (splitHalf L) x ↔ inCells L x ∧ x ≠ 1/2)
  | [], _, x => by simp [splitHalf, inCells]
  | p :: t, h, x => by
      have hp := h.bounds p (List.mem_cons_self ..)
      have hht := h.head_le
      have ht : Tidy t := h.tail
      have htail : ∀ y : ℝ, p.2 ≤ y → ¬ inCells t y → True := fun _ _ _ => trivial
      rw [splitHalf]
      split
      · rename_i hle
        have IH := inCells_splitHalf ht x
        constructor
        · rintro ⟨q, hq, hq1, hq2⟩
          rcases List.mem_cons.mp hq with rfl | hq
          · exact ⟨⟨q, List.mem_cons_self .., hq1, hq2⟩, by intro hx; rw [hx] at hq2; linarith⟩
          · obtain ⟨hm, hne⟩ := IH.mp ⟨q, hq, hq1, hq2⟩
            obtain ⟨s, hs, hs1, hs2⟩ := hm
            exact ⟨⟨s, List.mem_cons_of_mem _ hs, hs1, hs2⟩, hne⟩
        · rintro ⟨⟨q, hq, hq1, hq2⟩, hne⟩
          rcases List.mem_cons.mp hq with rfl | hq
          · exact ⟨q, List.mem_cons_self .., hq1, hq2⟩
          · obtain ⟨s, hs, hs1, hs2⟩ := IH.mpr ⟨⟨q, hq, hq1, hq2⟩, hne⟩
            exact ⟨s, List.mem_cons_of_mem _ hs, hs1, hs2⟩
      · rename_i hgt
        push_neg at hgt
        split
        · rename_i hlt
          constructor
          · rintro ⟨q, hq, hq1, hq2⟩
            rcases List.mem_cons.mp hq with rfl | hq
            · refine ⟨⟨p, List.mem_cons_self .., hq1, lt_trans hq2 hgt⟩, ?_⟩
              intro hx; rw [hx] at hq2; simp at hq2
            · rcases List.mem_cons.mp hq with rfl | hq
              · refine ⟨⟨p, List.mem_cons_self .., lt_trans hlt hq1, hq2⟩, ?_⟩
                intro hx; rw [hx] at hq1; simp at hq1
              · refine ⟨⟨q, List.mem_cons_of_mem _ hq, hq1, hq2⟩, ?_⟩
                intro hx
                have := hht q hq
                rw [hx] at hq1
                linarith
          · rintro ⟨⟨q, hq, hq1, hq2⟩, hne⟩
            rcases List.mem_cons.mp hq with rfl | hq
            · rcases lt_or_gt_of_ne hne with hx | hx
              · exact ⟨(q.1, 1/2), List.mem_cons_self .., hq1, hx⟩
              · exact ⟨(1/2, q.2), List.mem_cons_of_mem _ (List.mem_cons_self ..), hx, hq2⟩
            · exact ⟨q, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq), hq1, hq2⟩
        · rename_i hnlt
          push_neg at hnlt
          constructor
          · rintro ⟨q, hq, hq1, hq2⟩
            refine ⟨⟨q, hq, hq1, hq2⟩, ?_⟩
            rcases List.mem_cons.mp hq with rfl | hq
            · intro hx; rw [hx] at hq1; linarith
            · intro hx
              have := hht q hq
              rw [hx] at hq1
              linarith
          · rintro ⟨hm, -⟩; exact hm

/-! ## The cells of a word -/

/-- The affine image of a cell under the inverse branch `y ↦ r y + s`. -/
noncomputable def scaleCell (rr s : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (rr * p.1 + s, rr * p.2 + s)

/-- The cells of a word, built from the right through the inverse branches.
For `L` the inverse branch is `y ↦ r y + (1-r)`, for `R` it is `y ↦ r y`, and
for `M` the cells are first split at `1/2` — the point that the move
annihilates — and each piece is then carried by the branch belonging to its
side. -/
noncomputable def cells (lam : ℝ) : List Move → List (ℝ × ℝ)
  | [] => [(0, 1)]
  | Move.L :: v => (cells lam v).map (scaleCell (r lam) (1 - r lam))
  | Move.R :: v => (cells lam v).map (scaleCell (r lam) 0)
  | Move.M :: v => (splitHalf (cells lam v)).map
      (fun p => if p.2 ≤ 1/2 then scaleCell (r lam) 0 p else scaleCell (r lam) (1 - r lam) p)

@[simp] lemma cells_nil : cells lam [] = [(0, 1)] := rfl

lemma cells_cons_L (v : List Move) :
    cells lam (Move.L :: v) = (cells lam v).map (scaleCell (r lam) (1 - r lam)) := rfl

lemma cells_cons_R (v : List Move) :
    cells lam (Move.R :: v) = (cells lam v).map (scaleCell (r lam) 0) := rfl

lemma cells_cons_M (v : List Move) :
    cells lam (Move.M :: v) = (splitHalf (cells lam v)).map
      (fun p => if p.2 ≤ 1/2 then scaleCell (r lam) 0 p else scaleCell (r lam) (1 - r lam) p) :=
  rfl

/-! ## The invariant is preserved -/

lemma tidy_map_scale (h : 1 < lam) {L : List (ℝ × ℝ)} (hL : Tidy L) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 - r lam) : Tidy (L.map (scaleCell (r lam) s)) := by
  have hr0 : 0 < r lam := r_pos lam h
  refine ⟨?_, ?_⟩
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    obtain ⟨h1, h2, h3⟩ := hL.bounds p hp
    have hmul : 0 ≤ r lam * p.1 := mul_nonneg (le_of_lt hr0) h1
    refine ⟨by simp only [scaleCell]; linarith, ?_, ?_⟩
    · simpa [scaleCell] using (mul_lt_mul_of_pos_left h2 hr0)
    · have : r lam * p.2 ≤ r lam * 1 := mul_le_mul_of_nonneg_left h3 (le_of_lt hr0)
      simp only [scaleCell]
      linarith
  · rw [List.pairwise_map]
    refine hL.sorted.imp ?_
    intro p q hpq
    simp only [scaleCell]
    have := mul_le_mul_of_nonneg_left hpq (le_of_lt hr0)
    linarith

lemma tidy_cells (h : 1 < lam) : ∀ v : List Move, Tidy (cells lam v)
  | [] => ⟨by rintro p hp; simp at hp; subst hp; norm_num, by simp⟩
  | Move.L :: v => by
      have hr0 : 0 < r lam := r_pos lam h
      exact tidy_map_scale h (tidy_cells h v) (by linarith [r_lt_one lam h]) (le_refl _)
  | Move.R :: v => by
      have hr1 : r lam < 1 := r_lt_one lam h
      exact tidy_map_scale h (tidy_cells h v) (le_refl 0) (by linarith)
  | Move.M :: v => by
      have hr0 : 0 < r lam := r_pos lam h
      have hr1 : r lam < 1 := r_lt_one lam h
      have hsp : Tidy (splitHalf (cells lam v)) := tidy_splitHalf (tidy_cells h v)
      have hside := splitHalf_side (tidy_cells h v)
      rw [cells_cons_M]
      refine ⟨?_, ?_⟩
      · intro q hq
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
        obtain ⟨h1, h2, h3⟩ := hsp.bounds p hp
        by_cases hc : p.2 ≤ 1/2
        · simp only [hc, if_true, scaleCell, add_zero]
          refine ⟨by positivity, by simpa using mul_lt_mul_of_pos_left h2 hr0, ?_⟩
          have : r lam * p.2 ≤ r lam * 1 := mul_le_mul_of_nonneg_left h3 (le_of_lt hr0)
          simpa using by linarith
        · simp only [hc, if_false, scaleCell]
          have hmul : 0 ≤ r lam * p.1 := mul_nonneg (le_of_lt hr0) h1
          refine ⟨by linarith, by simpa using mul_lt_mul_of_pos_left h2 hr0, ?_⟩
          have : r lam * p.2 ≤ r lam * 1 := mul_le_mul_of_nonneg_left h3 (le_of_lt hr0)
          linarith
      · rw [List.pairwise_map]
        refine hsp.sorted.imp_of_mem ?_
        intro p q hp hq hpq
        obtain ⟨hp1, hp2, hp3⟩ := hsp.bounds p hp
        obtain ⟨hq1, hq2, hq3⟩ := hsp.bounds q hq
        by_cases hcp : p.2 ≤ 1/2 <;> by_cases hcq : q.2 ≤ 1/2
        · simp only [hcp, hcq, if_true, scaleCell, add_zero]
          exact mul_le_mul_of_nonneg_left hpq (le_of_lt hr0)
        · simp only [hcp, hcq, if_true, if_false, scaleCell, add_zero]
          have := mul_le_mul_of_nonneg_left hpq (le_of_lt hr0)
          linarith
        · exfalso; push_neg at hcp; linarith
        · simp only [hcp, hcq, if_false, scaleCell]
          have := mul_le_mul_of_nonneg_left hpq (le_of_lt hr0)
          linarith

/-! ## The cells are exactly the survivor set -/

lemma inCells_map_scale {rr s : ℝ} (hrr : 0 < rr) (L : List (ℝ × ℝ)) (x : ℝ) :
    inCells (L.map (scaleCell rr s)) x ↔ inCells L ((x - s) / rr) := by
  constructor
  · rintro ⟨q, hq, hq1, hq2⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    simp only [scaleCell] at hq1 hq2
    refine ⟨p, hp, ?_, ?_⟩
    · rw [lt_div_iff₀ hrr]; linarith
    · rw [div_lt_iff₀ hrr]; linarith
  · rintro ⟨p, hp, hp1, hp2⟩
    rw [lt_div_iff₀ hrr] at hp1
    rw [div_lt_iff₀ hrr] at hp2
    exact ⟨scaleCell rr s p, List.mem_map_of_mem hp, by simp only [scaleCell]; linarith,
      by simp only [scaleCell]; linarith⟩

/-- The `M` step of the cell recursion, in terms of the move itself. -/
lemma inCells_M_map (h : 1 < lam) {C : List (ℝ × ℝ)} (hC : Tidy C) (x : ℝ) :
    inCells ((splitHalf C).map (fun p => if p.2 ≤ 1/2 then scaleCell (r lam) 0 p
        else scaleCell (r lam) (1 - r lam) p)) x ↔
      (survives lam Move.M x ∧ inCells (splitHalf C) (act lam Move.M x)) := by
  have hr0 : 0 < r lam := r_pos lam h
  have hr1 : r lam < 1 := r_lt_one lam h
  have hlam : (0:ℝ) < lam := lt_trans zero_lt_one h
  have hlr : lam * r lam = 1 := lam_mul_r h
  have hsp : Tidy (splitHalf C) := tidy_splitHalf hC
  have hside := splitHalf_side hC
  constructor
  · rintro ⟨q, hq, hq1, hq2⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    obtain ⟨hb1, hb2, hb3⟩ := hsp.bounds p hp
    by_cases hc : p.2 ≤ 1/2
    · simp only [hc, if_true, scaleCell, add_zero] at hq1 hq2
      have hx2 : x < r lam / 2 := by nlinarith
      have hsurv : survives lam Move.M x := Or.inl hx2
      refine ⟨hsurv, p, hp, ?_, ?_⟩
      · rw [act_M_of_lt lam x hx2]; nlinarith
      · rw [act_M_of_lt lam x hx2]; nlinarith
    · simp only [hc, if_false, scaleCell] at hq1 hq2
      have hhalf : 1/2 ≤ p.1 := (hside p hp).resolve_left hc
      have hx2 : 1 - r lam / 2 < x := by nlinarith
      have hnlt : ¬ x < r lam / 2 := by
        have : r lam / 2 < 1 - r lam / 2 := half_lt_one_sub_half h
        push_neg; linarith
      refine ⟨Or.inr hx2, p, hp, ?_, ?_⟩
      · rw [act_M_of_gt lam x hnlt]; nlinarith
      · rw [act_M_of_gt lam x hnlt]; nlinarith
  · rintro ⟨hsurv, p, hp, hp1, hp2⟩
    obtain ⟨hb1, hb2, hb3⟩ := hsp.bounds p hp
    by_cases hx2 : x < r lam / 2
    · rw [act_M_of_lt lam x hx2] at hp1 hp2
      have hhalf : ¬ (1/2 ≤ p.1) := by nlinarith
      have hc : p.2 ≤ 1/2 := (hside p hp).resolve_right hhalf
      refine ⟨scaleCell (r lam) 0 p, ?_, ?_, ?_⟩
      · have : (if p.2 ≤ 1/2 then scaleCell (r lam) 0 p else scaleCell (r lam) (1 - r lam) p)
            = scaleCell (r lam) 0 p := if_pos hc
        rw [← this]; exact List.mem_map_of_mem hp
      · simp only [scaleCell, add_zero]; nlinarith
      · simp only [scaleCell, add_zero]; nlinarith
    · have hx3 : 1 - r lam / 2 < x := by
        rcases hsurv with hh | hh
        · exact absurd hh hx2
        · exact hh
      rw [act_M_of_gt lam x hx2] at hp1 hp2
      have hc : ¬ (p.2 ≤ 1/2) := by nlinarith
      refine ⟨scaleCell (r lam) (1 - r lam) p, ?_, ?_, ?_⟩
      · have : (if p.2 ≤ 1/2 then scaleCell (r lam) 0 p else scaleCell (r lam) (1 - r lam) p)
            = scaleCell (r lam) (1 - r lam) p := if_neg hc
        rw [← this]; exact List.mem_map_of_mem hp
      · simp only [scaleCell]; nlinarith
      · simp only [scaleCell]; nlinarith

/-- **T14, first part** (paper Lemma `lem:survivorset`).  The cells of `v` are
exactly the survivor set `S(v) = {x ∈ (0,1) : x survives v}`. -/
theorem inCells_cells (h : 1 < lam) : ∀ (v : List Move) (x : ℝ),
    inCells (cells lam v) x ↔ (0 < x ∧ x < 1 ∧ survivesWord lam x v) := by
  have hr0 : 0 < r lam := r_pos lam h
  have hr1 : r lam < 1 := r_lt_one lam h
  have hlam : (0:ℝ) < lam := lt_trans zero_lt_one h
  have hlr : lam * r lam = 1 := lam_mul_r h
  intro v
  induction v with
  | nil => intro x; simp [inCells, cells]
  | cons c v ih =>
      intro x
      cases c with
      | L =>
          rw [cells_cons_L, inCells_map_scale hr0, ih]
          have hact : (x - (1 - r lam)) / r lam = act lam Move.L x := by
            rw [act_L, div_eq_iff (ne_of_gt hr0)]; linear_combination (1 - x) * hlr
          rw [hact]
          simp only [survivesWord_cons, survives_L, act_L, g]
          constructor
          · rintro ⟨h1, h2, h3⟩
            refine ⟨by nlinarith, by nlinarith, by nlinarith, h3⟩
          · rintro ⟨h1, h2, h3, h4⟩
            exact ⟨by nlinarith, by nlinarith, h4⟩
      | M =>
          rw [cells_cons_M, inCells_M_map h (tidy_cells h v),
            inCells_splitHalf (tidy_cells h v), ih]
          simp only [survivesWord_cons]
          constructor
          · rintro ⟨hs, ⟨h1, h2, h3⟩, -⟩
            rcases hs with hh | hh
            · refine ⟨by nlinarith [act_M_of_lt lam x hh], ?_, Or.inl hh, h3⟩
              have : act lam Move.M x = lam * x := act_M_of_lt lam x hh
              nlinarith [this]
            · have hnlt : ¬ x < r lam / 2 := by
                have := half_lt_one_sub_half h; push_neg; linarith
              have hact : act lam Move.M x = lam * x - (lam - 1) := act_M_of_gt lam x hnlt
              refine ⟨by nlinarith [hact], by nlinarith [hact], Or.inr hh, h3⟩
          · rintro ⟨h1, h2, hs, h3⟩
            have hIoo := act_mem_Ioo h (Set.mem_Ioo.mpr ⟨h1, h2⟩) hs
            refine ⟨hs, ⟨hIoo.1, hIoo.2, h3⟩, act_M_ne_half h hs⟩
      | R =>
          rw [cells_cons_R, inCells_map_scale hr0, ih]
          have hact : (x - 0) / r lam = act lam Move.R x := by
            rw [act_R, div_eq_iff (ne_of_gt hr0)]; linear_combination (-x) * hlr
          rw [hact]
          simp only [survivesWord_cons, survives_R, act_R]
          constructor
          · rintro ⟨h1, h2, h3⟩
            refine ⟨by nlinarith, by nlinarith, by nlinarith, h3⟩
          · rintro ⟨h1, h2, h3, h4⟩
            exact ⟨by nlinarith, by nlinarith, h4⟩

/-! ## Total length, number of cells, and a long cell -/

/-- The total length of a list of cells. -/
def cellsLen (L : List (ℝ × ℝ)) : ℝ := (L.map (fun p => p.2 - p.1)).sum

/-- The number of `M`'s in a word. -/
def countM (v : List Move) : ℕ := v.countP (fun m => decide (m = Move.M))

@[simp] lemma countM_nil : countM [] = 0 := rfl

lemma countM_cons (c : Move) (v : List Move) :
    countM (c :: v) = countM v + (if c = Move.M then 1 else 0) := by
  simp [countM, List.countP_cons]

lemma countM_le_length (v : List Move) : countM v ≤ v.length :=
  List.countP_le_length

lemma cellsLen_map_scale (rr s : ℝ) (L : List (ℝ × ℝ)) :
    cellsLen (L.map (scaleCell rr s)) = rr * cellsLen L := by
  simp only [cellsLen, List.map_map]
  rw [show ((fun p : ℝ × ℝ => p.2 - p.1) ∘ scaleCell rr s) = (fun p : ℝ × ℝ => rr * (p.2 - p.1))
      from funext fun p => by simp only [Function.comp_apply, scaleCell]; ring]
  exact List.sum_map_mul_left L (fun p => p.2 - p.1) rr

lemma cellsLen_map_M (rr : ℝ) (L : List (ℝ × ℝ)) :
    cellsLen (L.map (fun p => if p.2 ≤ 1/2 then scaleCell rr 0 p else scaleCell rr (1 - rr) p))
      = rr * cellsLen L := by
  simp only [cellsLen, List.map_map]
  rw [show ((fun p : ℝ × ℝ => p.2 - p.1) ∘
      (fun p : ℝ × ℝ => if p.2 ≤ 1/2 then scaleCell rr 0 p else scaleCell rr (1 - rr) p))
      = (fun p : ℝ × ℝ => rr * (p.2 - p.1)) from funext fun p => by
        by_cases hc : p.2 ≤ 1/2 <;>
          simp only [Function.comp_apply, hc, if_true, if_false, scaleCell] <;> ring]
  exact List.sum_map_mul_left L (fun p => p.2 - p.1) rr

/-- **T14, second part.**  The cells of `v` have total length exactly `r ^ |v|`. -/
theorem cellsLen_cells (h : 1 < lam) : ∀ v : List Move,
    cellsLen (cells lam v) = (r lam) ^ v.length
  | [] => by simp [cellsLen, cells]
  | Move.L :: v => by
      rw [cells_cons_L, cellsLen_map_scale, cellsLen_cells h v]
      simp [pow_succ]; ring
  | Move.R :: v => by
      rw [cells_cons_R, cellsLen_map_scale, cellsLen_cells h v]
      simp [pow_succ]; ring
  | Move.M :: v => by
      rw [cells_cons_M, cellsLen_map_M]
      have : cellsLen (splitHalf (cells lam v)) = cellsLen (cells lam v) := splitHalf_sum _
      rw [this, cellsLen_cells h v]
      simp [pow_succ]; ring

/-- **T14, third part.**  There are at most `1 + #{M's in v}` cells. -/
theorem length_cells_le : ∀ v : List Move, (cells lam v).length ≤ 1 + countM v
  | [] => by simp [cells, countM]
  | Move.L :: v => by
      rw [cells_cons_L, List.length_map, countM_cons]
      simpa using length_cells_le v
  | Move.R :: v => by
      rw [cells_cons_R, List.length_map, countM_cons]
      simpa using length_cells_le v
  | Move.M :: v => by
      have h1 := splitHalf_length_le (cells lam v)
      have h2 := length_cells_le v
      have h3 : countM (Move.M :: v) = countM v + 1 := by simp [countM_cons]
      rw [cells_cons_M, List.length_map, h3]
      omega

lemma cells_ne_nil : ∀ v : List Move, cells lam v ≠ []
  | [] => by simp [cells]
  | Move.L :: v => by
      rw [cells_cons_L]
      simpa using cells_ne_nil v
  | Move.R :: v => by
      rw [cells_cons_R]
      simpa using cells_ne_nil v
  | Move.M :: v => by
      rw [cells_cons_M]
      simpa using splitHalf_ne_nil (cells_ne_nil v)

private lemma exists_max_mem : ∀ (l : List ℝ), l ≠ [] → ∃ x ∈ l, ∀ y ∈ l, y ≤ x
  | [], hl => absurd rfl hl
  | [a], _ => ⟨a, by simp, by simp⟩
  | a :: b :: t, _ => by
      obtain ⟨x, hx, hmax⟩ := exists_max_mem (b :: t) (by simp)
      rcases le_total a x with hax | hax
      · refine ⟨x, List.mem_cons_of_mem _ hx, ?_⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hax
        · exact hmax y hy
      · refine ⟨a, List.mem_cons_self .., ?_⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact le_refl _
        · exact le_trans (hmax y hy) hax

/-- **T14, fourth part** (paper Lemma `lem:survivorset`).  Some cell of `v` has
length at least `r ^ |v| / (|v| + 1)`; being a cell, it is an open interval
contained in the survivor set `S(v)`. -/
theorem exists_long_cell (h : 1 < lam) (v : List Move) :
    ∃ p ∈ cells lam v, (r lam) ^ v.length / (v.length + 1) ≤ p.2 - p.1 ∧
      ∀ x, p.1 < x → x < p.2 → (0 < x ∧ x < 1 ∧ survivesWord lam x v) := by
  have hr0 : 0 < r lam := r_pos lam h
  set L := (cells lam v).map (fun p => p.2 - p.1) with hL
  have hLne : L ≠ [] := by
    simpa [hL] using cells_ne_nil (lam := lam) v
  obtain ⟨x, hxL, hmax⟩ := exists_max_mem L hLne
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hxL
  have hsum : L.sum ≤ L.length • (p.2 - p.1) := List.sum_le_card_nsmul L _ hmax
  have hlen : L.length ≤ v.length + 1 := by
    have := length_cells_le (lam := lam) v
    have h2 := countM_le_length v
    simp only [hL, List.length_map]
    omega
  have hpos : 0 < p.2 - p.1 := by
    have := (tidy_cells h v).bounds p hp
    linarith [this.2.1]
  have hsum' : (r lam) ^ v.length ≤ (L.length : ℝ) * (p.2 - p.1) := by
    have : L.sum = (r lam) ^ v.length := cellsLen_cells h v
    rw [← this]
    simpa [nsmul_eq_mul] using hsum
  have hstep : ((L.length : ℝ)) * (p.2 - p.1) ≤ ((v.length : ℝ) + 1) * (p.2 - p.1) := by
    have : ((L.length : ℝ)) ≤ (v.length : ℝ) + 1 := by exact_mod_cast hlen
    nlinarith
  refine ⟨p, hp, ?_, ?_⟩
  · rw [div_le_iff₀ (by positivity)]
    linarith
  · intro y hy1 hy2
    exact (inCells_cells h v y).mp ⟨p, hp, hy1, hy2⟩

/-! ## The survivor set and its measure -/

/-- `S(v)`: the points of `(0,1)` that survive the word `v`. -/
def survivorSet (lam : ℝ) (v : List Move) : Set ℝ :=
  {x | 0 < x ∧ x < 1 ∧ survivesWord lam x v}

lemma survivorSet_eq_biUnion (h : 1 < lam) (v : List Move) :
    survivorSet lam v = ⋃ p ∈ cells lam v, Set.Ioo p.1 p.2 := by
  ext x
  simp only [survivorSet, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_Ioo, exists_prop]
  rw [← inCells_cells h v x]
  exact ⟨fun ⟨p, hp, h1, h2⟩ => ⟨p, hp, h1, h2⟩, fun ⟨p, hp, h1, h2⟩ => ⟨p, hp, h1, h2⟩⟩

lemma volume_biUnion_cells : ∀ {L : List (ℝ × ℝ)}, Tidy L →
    MeasureTheory.volume (⋃ p ∈ L, Set.Ioo p.1 p.2) = ENNReal.ofReal (cellsLen L)
  | [], _ => by simp [cellsLen]
  | p :: t, hT => by
      have ht : Tidy t := hT.tail
      have hbp := hT.bounds p (List.mem_cons_self ..)
      have hdisj : Disjoint (Set.Ioo p.1 p.2) (⋃ q ∈ t, Set.Ioo q.1 q.2) := by
        rw [Set.disjoint_left]
        rintro x ⟨hx1, hx2⟩ hx
        simp only [Set.mem_iUnion, Set.mem_Ioo, exists_prop] at hx
        obtain ⟨q, hq, hq1, hq2⟩ := hx
        exact absurd hq1 (by have := hT.head_le q hq; linarith)
      have hmeas : MeasurableSet (⋃ q ∈ t, Set.Ioo q.1 q.2) := by
        exact MeasurableSet.biUnion (List.finite_toSet t).countable
          (fun q _ => measurableSet_Ioo)
      have hnn : 0 ≤ cellsLen t := by
        refine List.sum_nonneg ?_
        intro y hy
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
        have := ht.bounds q hq
        linarith [this.2.1]
      rw [show (⋃ q ∈ (p :: t), Set.Ioo q.1 q.2)
            = Set.Ioo p.1 p.2 ∪ ⋃ q ∈ t, Set.Ioo q.1 q.2 by
          simp]
      rw [MeasureTheory.measure_union hdisj hmeas, volume_biUnion_cells ht, Real.volume_Ioo,
        ← ENNReal.ofReal_add (by linarith [hbp.2.1]) hnn]
      simp [cellsLen]

/-- **T14, measure form** (paper Lemma `lem:survivorset`).  The survivor set of
`v` has Lebesgue measure exactly `r ^ |v|`. -/
theorem volume_survivorSet (h : 1 < lam) (v : List Move) :
    MeasureTheory.volume (survivorSet lam v) = ENNReal.ofReal ((r lam) ^ v.length) := by
  rw [survivorSet_eq_biUnion h v, volume_biUnion_cells (tidy_cells h v), cellsLen_cells h v]

end KnotGame
