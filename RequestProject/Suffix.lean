import RequestProject.Distinct

/-!
# Lemma 2.1 and Theorem 2.2: the suffix decomposition (Work Order 3)

The knot count after a run equals the number of `M` positions whose subsequent
suffix keeps `1/2` alive; consequently `N` is monotone.
-/

namespace KnotGame

variable {lam : ℝ}

lemma mem_step {m : Move} {S : Finset ℝ} {y : ℝ} :
    y ∈ step lam m S ↔
      ((∃ x ∈ S, survives lam m x ∧ act lam m x = y) ∨ (m = Move.M ∧ y = 1/2)) := by
  cases m
  · simp only [step_L, Finset.mem_image, survivors, Finset.mem_filter, reduceCtorEq,
      false_and, or_false]
    constructor
    · rintro ⟨x, ⟨hxS, hx⟩, rfl⟩; exact ⟨x, hxS, hx, rfl⟩
    · rintro ⟨x, hxS, hx, rfl⟩; exact ⟨x, ⟨hxS, hx⟩, rfl⟩
  · simp only [step_M, Finset.mem_union, Finset.mem_image, survivors, Finset.mem_filter,
      Finset.mem_singleton, true_and]
    constructor
    · rintro (⟨x, ⟨hxS, hx⟩, rfl⟩ | h)
      · exact Or.inl ⟨x, hxS, hx, rfl⟩
      · exact Or.inr h
    · rintro (⟨x, hxS, hx, rfl⟩ | h)
      · exact Or.inl ⟨x, ⟨hxS, hx⟩, rfl⟩
      · exact Or.inr h
  · simp only [step_R, Finset.mem_image, survivors, Finset.mem_filter, reduceCtorEq,
      false_and, or_false]
    constructor
    · rintro ⟨x, ⟨hxS, hx⟩, rfl⟩; exact ⟨x, hxS, hx, rfl⟩
    · rintro ⟨x, hxS, hx, rfl⟩; exact ⟨x, ⟨hxS, hx⟩, rfl⟩

/-- The survivors of a whole word, after one move, are the images of the
survivors of the whole longer word, together with a possible newborn knot. -/
lemma filter_step (m : Move) (w : List Move) (S : Finset ℝ) :
    (step lam m S).filter (fun y => survivesWord lam y w) =
      (S.filter (fun x => survivesWord lam x (m :: w))).image (act lam m) ∪
        (if m = Move.M ∧ survivesWord lam (1/2) w then {(1:ℝ)/2} else ∅) := by
  ext y
  simp only [Finset.mem_filter, mem_step, Finset.mem_union, Finset.mem_image,
    survivesWord_cons]
  constructor
  · rintro ⟨hy | ⟨hm, rfl⟩, hyw⟩
    · obtain ⟨x, hxS, hx, rfl⟩ := hy
      exact Or.inl ⟨x, ⟨hxS, hx, hyw⟩, rfl⟩
    · refine Or.inr ?_
      rw [if_pos ⟨hm, hyw⟩]
      exact Finset.mem_singleton_self _
  · rintro (⟨x, hx, rfl⟩ | hy)
    · exact ⟨Or.inl ⟨x, hx.1, hx.2.1, rfl⟩, hx.2.2⟩
    · by_cases hc : m = Move.M ∧ survivesWord lam (1/2) w
      · rw [if_pos hc, Finset.mem_singleton] at hy
        subst hy
        exact ⟨Or.inr ⟨hc.1, rfl⟩, hc.2⟩
      · rw [if_neg hc] at hy
        exact absurd hy (Finset.notMem_empty _)

/-- **Lemma 2.1 (suffix decomposition), general form.** Starting from a
configuration `S`, the knots after the run `w` are the survivors of `S` along
`w` together with one for each `M` whose suffix keeps `1/2` alive. -/
theorem card_runFrom (h : 1 < lam) (w : List Move) (S : Finset ℝ) :
    (runFrom lam S w).card
      = (S.filter (fun x => survivesWord lam x w)).card + births lam w := by
  induction w generalizing S with
  | nil => simp
  | cons m w ih =>
      rw [runFrom_cons, ih, filter_step, births_cons]
      set A := S.filter (fun x => survivesWord lam x (m :: w)) with hA
      have hAsub : ∀ x ∈ A, survives lam m x := by
        intro x hx
        rw [hA, Finset.mem_filter] at hx
        exact hx.2.1
      have hinj : (A.image (act lam m)).card = A.card := by
        apply Finset.card_image_of_injOn
        intro x hx y hy hxy
        exact act_injOn h m (hAsub x hx) (hAsub y hy) hxy
      by_cases hc : m = Move.M ∧ survivesWord lam (1/2) w
      · have hm : m = Move.M := hc.1
        rw [if_pos hc, if_pos hc]
        have hdisj : Disjoint (A.image (act lam m)) ({(1:ℝ)/2} : Finset ℝ) := by
          simp only [Finset.disjoint_singleton_right, Finset.mem_image, not_exists]
          rintro x ⟨hx, hxa⟩
          subst hm
          exact act_M_ne_half h (hAsub x hx) hxa
        rw [Finset.card_union_of_disjoint hdisj, hinj, Finset.card_singleton]
        omega
      · rw [if_neg hc, if_neg hc, Finset.union_empty, hinj]
        omega

/-- **Lemma 2.1.** The number of knots after a run `w` equals the number of
positions carrying `M` whose subsequent suffix keeps `1/2` alive. -/
theorem card_run (h : 1 < lam) (w : List Move) :
    (run lam w).card = births lam w := by
  simp [run, card_runFrom h w ∅]

lemma births_cons_L (w : List Move) : births lam (Move.L :: w) = births lam w := by
  simp [births_cons]

lemma births_cons_R (w : List Move) : births lam (Move.R :: w) = births lam w := by
  simp [births_cons]

/-- Prepending letters never decreases the birth count. -/
lemma births_le_append (a b : List Move) : births lam b ≤ births lam (a ++ b) := by
  induction a with
  | nil => simp
  | cons m a ih =>
      rw [List.cons_append, births_cons]
      exact le_trans ih (Nat.le_add_right _ _)

/-- Any word gives a lower bound for `N` at its own length. -/
lemma births_le_N (h : 1 < lam) (w : List Move) : births lam w ≤ N lam w.length := by
  have hw : List.ofFn (fun i : Fin w.length => w.get i) = w := List.ofFn_get w
  have h1 : (run lam (List.ofFn (fun i : Fin w.length => w.get i))).card = births lam w := by
    rw [hw, card_run h]
  rw [← h1]
  exact Finset.le_sup (f := fun u : Fin w.length → Move => (run lam (List.ofFn u)).card)
    (Finset.mem_univ _)

/-- **Theorem 2.2.** `N` is non-decreasing. -/
theorem N_mono (h : 1 < lam) (n : ℕ) : N lam n ≤ N lam (n + 1) := by
  apply Finset.sup_le
  intro v _
  have h1 : (run lam (List.ofFn v)).card = births lam (List.ofFn v) := card_run h _
  set v' : Fin (n+1) → Move := Fin.cons Move.L v with hv'
  have h2 : List.ofFn v' = Move.L :: List.ofFn v := by
    rw [List.ofFn_succ]
    simp [hv']
  have h3 : (run lam (List.ofFn v')).card = births lam (List.ofFn v) := by
    rw [card_run h, h2, births_cons_L]
  rw [h1, ← h3]
  exact Finset.le_sup (f := fun u : Fin (n+1) → Move => (run lam (List.ofFn u)).card)
    (Finset.mem_univ v')

end KnotGame
