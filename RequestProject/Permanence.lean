import RequestProject.Backward

/-!
# T15 — permanence (paper Lemma `lem:permanent`)

A knot alive at the end of a run is determined by the suffix following its
birth (round 1's `card_run`, Lemma `lem:suffix`): it exists exactly when its
birth letter is `M` and `1/2` survives that suffix, and its position is the
image of `1/2` under the suffix.  `KnotAt lam w a x` records that the run `w`
carries a knot of age `a` at position `x`.

* `mem_run_iff` — the configuration after `w` is exactly the set of such knots;
* `knotAt_cons` — **T15**: the knots of `c :: v` are the knots of `v`, with the
  same positions and ages, together with one new knot of age `|v|`, present
  exactly when `c = M` and `1/2` survives `v`;
* `knotAt_age_inj` — knots of different ages sit at different positions;
* `card_run_ge_of_ages` — a run with `k` distinct knot ages carries at least
  `k` knots.
-/

namespace KnotGame

variable {lam : ℝ}

/-- `KnotAt lam w a x`: the run `w` carries a knot of age `a` at position `x`,
i.e. `w` factors as `p ++ M :: s` with `|s| = a`, `1/2` surviving `s`, and
`x` the image of `1/2` under `s`. -/
def KnotAt (lam : ℝ) (w : List Move) (a : ℕ) (x : ℝ) : Prop :=
  ∃ p s, w = p ++ Move.M :: s ∧ s.length = a ∧ survivesWord lam (1/2) s ∧
    posAfter lam (1/2) s = x

/-- `HasKnotAge lam w a`: the run `w` carries a knot of age `a`. -/
def HasKnotAge (lam : ℝ) (w : List Move) (a : ℕ) : Prop := ∃ x, KnotAt lam w a x

lemma KnotAt.age_lt {w : List Move} {a : ℕ} {x : ℝ} (hk : KnotAt lam w a x) : a < w.length := by
  obtain ⟨p, s, rfl, rfl, -, -⟩ := hk
  simp
  omega

@[simp] lemma knotAt_nil (a : ℕ) (x : ℝ) : ¬ KnotAt lam [] a x := by
  rintro ⟨p, s, hp, -, -, -⟩
  exact absurd hp.symm (List.append_ne_nil_of_right_ne_nil p (List.cons_ne_nil _ _))

/-- **T15 (permanence)** (paper Lemma `lem:permanent`).  The knots of `c :: v`
are exactly the knots of `v`, with identical positions and ages, together with
one new knot of age `|v|`, present exactly when `c = M` and `1/2` survives
`v`. -/
theorem knotAt_cons (c : Move) (v : List Move) (a : ℕ) (x : ℝ) :
    KnotAt lam (c :: v) a x ↔
      (KnotAt lam v a x ∨
        (c = Move.M ∧ a = v.length ∧ survivesWord lam (1/2) v ∧ posAfter lam (1/2) v = x)) := by
  constructor
  · rintro ⟨p, s, hw, hlen, hsurv, hpos⟩
    cases p with
    | nil =>
        simp only [List.nil_append, List.cons.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        exact Or.inr ⟨rfl, hlen.symm, hsurv, hpos⟩
    | cons d p =>
        simp only [List.cons_append, List.cons.injEq] at hw
        obtain ⟨rfl, hv⟩ := hw
        exact Or.inl ⟨p, s, hv, hlen, hsurv, hpos⟩
  · rintro (⟨p, s, hv, hlen, hsurv, hpos⟩ | ⟨rfl, rfl, hsurv, hpos⟩)
    · exact ⟨c :: p, s, by rw [hv]; rfl, hlen, hsurv, hpos⟩
    · exact ⟨[], v, rfl, rfl, hsurv, hpos⟩

/-- Prepending a letter never destroys or moves a knot. -/
theorem knotAt_cons_of_knotAt (c : Move) {v : List Move} {a : ℕ} {x : ℝ}
    (hk : KnotAt lam v a x) : KnotAt lam (c :: v) a x :=
  (knotAt_cons c v a x).mpr (Or.inl hk)

/-- The new knot created by prepending `M`. -/
theorem knotAt_cons_M {v : List Move} (hs : survivesWord lam (1/2) v) :
    KnotAt lam (Move.M :: v) v.length (posAfter lam (1/2) v) :=
  (knotAt_cons Move.M v _ _).mpr (Or.inr ⟨rfl, rfl, hs, rfl⟩)

/-! ## The configuration is the set of knots -/

lemma mem_runFrom_iff (h : 1 < lam) : ∀ (w : List Move) (S : Finset ℝ) (y : ℝ),
    y ∈ runFrom lam S w ↔
      ((∃ x ∈ S, survivesWord lam x w ∧ posAfter lam x w = y) ∨ ∃ a, KnotAt lam w a y)
  | [], S, y => by
      simp only [runFrom_nil, survivesWord_nil, posAfter_nil, true_and, knotAt_nil,
        exists_false, or_false]
      exact ⟨fun hy => ⟨y, hy, rfl⟩, fun ⟨x, hx, hxy⟩ => hxy ▸ hx⟩
  | m :: w, S, y => by
      rw [runFrom_cons, mem_runFrom_iff h w (step lam m S) y]
      constructor
      · rintro (⟨z, hz, hzw, hzy⟩ | ⟨a, ha⟩)
        · rcases mem_step.mp hz with ⟨x, hxS, hxs, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inl ⟨x, hxS, ⟨hxs, hzw⟩, hzy⟩
          · exact Or.inr ⟨w.length, hzy ▸ knotAt_cons_M (lam := lam) hzw⟩
        · exact Or.inr ⟨a, knotAt_cons_of_knotAt m ha⟩
      · rintro (⟨x, hxS, hxw, hxy⟩ | ⟨a, ha⟩)
        · rw [survivesWord_cons] at hxw
          rw [posAfter_cons] at hxy
          exact Or.inl ⟨act lam m x, mem_step.mpr (Or.inl ⟨x, hxS, hxw.1, rfl⟩), hxw.2, hxy⟩
        · rcases (knotAt_cons m w a y).mp ha with hk | ⟨rfl, rfl, hsurv, hpos⟩
          · exact Or.inr ⟨a, hk⟩
          · exact Or.inl ⟨1/2, mem_step.mpr (Or.inr ⟨rfl, rfl⟩), hsurv, hpos⟩

/-- The configuration after the run `w` is exactly the set of knots of `w`. -/
theorem mem_run_iff (h : 1 < lam) (w : List Move) (y : ℝ) :
    y ∈ run lam w ↔ ∃ a, KnotAt lam w a y := by
  rw [run, mem_runFrom_iff h w ∅ y]
  simp

/-! ## Knots of different ages are at different places -/

/-- **Distinctness of ages.**  A run cannot carry two knots of different ages
at the same position. -/
theorem knotAt_age_inj (h : 1 < lam) {w : List Move} {a b : ℕ} {x : ℝ}
    (ha : KnotAt lam w a x) (hb : KnotAt lam w b x) : a = b := by
  -- the general step: `a < b` is impossible
  have key : ∀ {c d : ℕ}, c < d → KnotAt lam w c x → KnotAt lam w d x → False := by
    intro c d hcd hc hd
    obtain ⟨p, s, hws, hlens, hsurvs, hposs⟩ := hc
    obtain ⟨q, t, hwt, hlent, hsurvt, hpost⟩ := hd
    have hsuf1 : (Move.M :: s) <:+ w := ⟨p, hws.symm⟩
    have hsuf2 : t <:+ w := ⟨q ++ [Move.M], by rw [hwt]; simp⟩
    have hlen : (Move.M :: s).length ≤ t.length := by
      simp only [List.length_cons, hlens, hlent]
      omega
    obtain ⟨u, hu⟩ := List.suffix_of_suffix_length_le hsuf1 hsuf2 hlen
    -- `t = u ++ M :: s`, so the older knot's position is the image of `1/2`
    -- under `u ++ [M]` followed by `s`
    have hsplit : t = (u ++ [Move.M]) ++ s := by rw [← hu]; simp
    rw [hsplit] at hsurvt hpost
    rw [survivesWord_append] at hsurvt
    rw [posAfter_append] at hpost
    have hz : posAfter lam (1/2) (u ++ [Move.M]) = 1/2 :=
      posAfter_inj h s hsurvt.2 hsurvs (by rw [hpost, hposs])
    -- but the last letter of `u ++ [M]` is an `M`, which never lands on `1/2`
    have hu2 : survivesWord lam (1/2) (u ++ [Move.M]) := hsurvt.1
    rw [survivesWord_append] at hu2
    rw [posAfter_append] at hz
    simp only [posAfter_cons, posAfter_nil] at hz
    exact act_M_ne_half h (by simpa using hu2.2) hz
  rcases lt_trichotomy a b with hlt | heq | hgt
  · exact absurd (key hlt ha hb) (by simp)
  · exact heq
  · exact absurd (key hgt hb ha) (by simp)

/-- A run whose knot ages include `k` distinct values carries at least `k`
knots. -/
theorem card_run_ge_of_ages (h : 1 < lam) (w : List Move) (A : Finset ℕ)
    (hA : ∀ a ∈ A, HasKnotAge lam w a) : A.card ≤ (run lam w).card := by
  classical
  have hA' : ∀ a : ℕ, ∃ x : ℝ, a ∈ A → KnotAt lam w a x := by
    intro a
    by_cases ha : a ∈ A
    · obtain ⟨x, hx⟩ := hA a ha
      exact ⟨x, fun _ => hx⟩
    · exact ⟨0, fun hc => absurd hc ha⟩
  choose f hf using hA'
  refine Finset.card_le_card_of_injOn f ?_ ?_
  · intro a ha
    exact (mem_run_iff h w _).mpr ⟨a, hf a ha⟩
  · intro a ha b hb hab
    have ha' : a ∈ A := ha
    have hb' : b ∈ A := hb
    exact knotAt_age_inj h (hf a ha') (hab ▸ hf b hb')

end KnotGame
