import RequestProject.Pisot

/-!
# Order, gaps, and the scheduling bound (round 2, Targets T1–T5)

This file formalises the section *Order, gaps, and a scheduling bound* on top of
the round-1 development.  All definitions (`Move`, `r`, `g`, `survives`, `act`,
`step`, `run`, `births`, `N`) are reused verbatim from `RequestProject.Basic`.

Contents:

* `Straddles` — a pair straddles the interval deleted by `M`.
* `act_lt_act` (**T1**) — each move is strictly order preserving on its survivors.
* `gap_law` (**T2**) — the distance between two survivors is multiplied by `lam`,
  except for a straddling pair at an `M`, where `lam - 1` is subtracted.
* `straddles_unique` (**T3**) — two straddling pairs cannot be disjointly ordered,
  so at most one consecutive pair of an ordered set straddles a given move.
* `birth_head_ne_M`, `two_mul_births_le_length_succ` (**T4**) — surviving births
  are at least two apart, so a word of length `W` carries at most `⌈W/2⌉` of them.
* `card_le_length_succ`, `scheduling_bound`, `N_le_of_separated` (**T5**).
-/

namespace KnotGame

variable {lam : ℝ}

/-! ## Straddling -/

/-- The pair `x < y` *straddles* the interval deleted by the move `M`: `x` lies
strictly below it and `y` strictly above it. -/
def Straddles (lam x y : ℝ) : Prop := x < r lam / 2 ∧ 1 - r lam / 2 < y

lemma half_lt_one_sub_half (h : 1 < lam) : r lam / 2 < 1 - r lam / 2 := by
  have := r_lt_one lam h
  linarith

/-! ## T1: order -/

/-- **T1 (order).**  Each move, restricted to its survivors, is strictly order
preserving: if `x < y` and both survive the move `m`, then
`act m x < act m y`. -/
theorem act_lt_act (h : 1 < lam) (m : Move) {x y : ℝ}
    (hx : survives lam m x) (hy : survives lam m y) (hxy : x < y) :
    act lam m x < act lam m y := by
  have hlam : (0:ℝ) < lam := lt_trans zero_lt_one h
  have hr1 : r lam < 1 := r_lt_one lam h
  cases m
  · simp only [act_L]
    have : lam * x < lam * y := mul_lt_mul_of_pos_left hxy hlam
    linarith
  · simp only [survives_M] at hx hy
    by_cases hx' : x < r lam / 2 <;> by_cases hy' : y < r lam / 2
    · rw [act_M_of_lt lam x hx', act_M_of_lt lam y hy']
      exact mul_lt_mul_of_pos_left hxy hlam
    · rw [act_M_of_lt lam x hx', act_M_of_gt lam y hy']
      exact straddle h hx' (hy.resolve_left hy')
    · exact absurd (hx.resolve_left hx') (by linarith)
    · rw [act_M_of_gt lam x hx', act_M_of_gt lam y hy']
      have : lam * x < lam * y := mul_lt_mul_of_pos_left hxy hlam
      linarith
  · simp only [act_R]
    exact mul_lt_mul_of_pos_left hxy hlam

/-! ## T2: the gap law -/

/-- **T2 (gap law).**  If `x < y` both survive the move `m` then the new distance
is `lam * (y - x)`, unless `m = M` and the pair straddles the deleted interval,
in which case it is `lam * (y - x) - (lam - 1)`. -/
theorem gap_law (h : 1 < lam) (m : Move) {x y : ℝ}
    (hx : survives lam m x) (hy : survives lam m y) (hxy : x < y) :
    act lam m y - act lam m x = lam * (y - x) ∨
      (m = Move.M ∧ Straddles lam x y ∧
        act lam m y - act lam m x = lam * (y - x) - (lam - 1)) := by
  have hr1 : r lam < 1 := r_lt_one lam h
  cases m
  · left; simp only [act_L]; ring
  · simp only [survives_M] at hx hy
    by_cases hx' : x < r lam / 2 <;> by_cases hy' : y < r lam / 2
    · left; rw [act_M_of_lt lam x hx', act_M_of_lt lam y hy']; ring
    · right
      refine ⟨rfl, ⟨hx', hy.resolve_left hy'⟩, ?_⟩
      rw [act_M_of_lt lam x hx', act_M_of_gt lam y hy']; ring
    · exact absurd (hx.resolve_left hx') (by linarith)
    · left; rw [act_M_of_gt lam x hx', act_M_of_gt lam y hy']; ring
  · left; simp only [act_R]; ring

/-! ## T3: one service per move -/

/-- **T3 (one service per move).**  Two straddling pairs cannot be laid end to
end: if `x < y ≤ z < u` and both `(x, y)` and `(z, u)` straddle, we get a
contradiction.  Consequently at most one consecutive pair of an ordered finite
set of survivors straddles a given move. -/
theorem straddles_unique (h : 1 < lam) {x y z u : ℝ}
    (h₁ : Straddles lam x y) (h₂ : Straddles lam z u) (hyz : y ≤ z) : False := by
  have := half_lt_one_sub_half h
  have : (1:ℝ) - r lam / 2 < r lam / 2 := lt_of_lt_of_le h₁.2 (le_of_lt (lt_of_le_of_lt hyz h₂.1))
  linarith

/-- The consecutive-pair form of **T3**: in an ordered list of survivors, if the
pair `(x, y)` straddles then no later consecutive pair does. -/
theorem straddles_at_most_one (h : 1 < lam) {x y z u : ℝ}
    (h₁ : Straddles lam x y) (hyz : y ≤ z) : ¬ Straddles lam z u :=
  fun h₂ => straddles_unique h h₁ h₂ hyz

/-! ## T4: birth spacing -/

/-- A knot sitting at `1/2` never survives an `M`: `1/2` lies strictly inside the
interval deleted by `M` for every `lam ∈ (1, ∞)`. -/
theorem half_not_survives_M (h : 1 < lam) : ¬ survives lam Move.M (1/2) := by
  have := r_lt_one lam h
  simp only [survives_M, not_or, not_lt]
  constructor <;> linarith

/-- **T4 (birth spacing), local form.**  If the knot born at `1/2` survives the
next move, that move is not `M`; hence two surviving births are never adjacent. -/
theorem birth_head_ne_M (h : 1 < lam) {m : Move} {w : List Move}
    (hs : survivesWord lam (1/2) (m :: w)) : m ≠ Move.M := by
  rintro rfl
  exact half_not_survives_M h hs.1

/-- **T4 (birth spacing), counting form.**  Surviving births being at least two
apart, a word of length `n` carries at most `⌈n/2⌉` of them. -/
theorem two_mul_births_le_length_succ (h : 1 < lam) :
    ∀ (n : ℕ) (w : List Move), w.length = n → 2 * births lam w ≤ n + 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w hw
    match w with
    | [] => simp only [births_nil]; omega
    | m :: rest =>
      rw [births_cons]
      by_cases hc : m = Move.M ∧ survivesWord lam (1/2) rest
      · rw [if_pos hc]
        match rest with
        | [] =>
          simp only [births_nil] at *
          simp only [List.length_cons, List.length_nil] at hw
          omega
        | m' :: w'' =>
          have hm' : m' ≠ Move.M := birth_head_ne_M h hc.2
          have hb : births lam (m' :: w'') = births lam w'' := by
            rw [births_cons, if_neg (by rintro ⟨hh, -⟩; exact hm' hh)]
            omega
          have hlen : w''.length < n := by
            simp only [List.length_cons] at hw; omega
          have := ih w''.length hlen w'' rfl
          simp only [List.length_cons] at hw
          omega
      · rw [if_neg hc]
        have hlen : rest.length < n := by
          simp only [List.length_cons] at hw; omega
        have := ih rest.length hlen rest rfl
        simp only [List.length_cons] at hw
        omega

/-- **T4**, in the form used below: `births lam w ≤ ⌈|w|/2⌉`. -/
theorem births_le_ceil_half (h : 1 < lam) (w : List Move) :
    births lam w ≤ (w.length + 1) / 2 := by
  have := two_mul_births_le_length_succ h w.length w rfl
  omega

/-! ## Configurations live in the open unit interval -/

lemma step_subset_Ioo (h : 1 < lam) (m : Move) {S : Finset ℝ}
    (hS : ∀ x ∈ S, x ∈ Set.Ioo (0:ℝ) 1) :
    ∀ y ∈ step lam m S, y ∈ Set.Ioo (0:ℝ) 1 := by
  intro y hy
  rcases mem_step.mp hy with ⟨x, hxS, hx, rfl⟩ | ⟨-, rfl⟩
  · exact act_mem_Ioo h (hS x hxS) hx
  · constructor <;> norm_num

lemma runFrom_subset_Ioo (h : 1 < lam) (w : List Move) {S : Finset ℝ}
    (hS : ∀ x ∈ S, x ∈ Set.Ioo (0:ℝ) 1) :
    ∀ y ∈ runFrom lam S w, y ∈ Set.Ioo (0:ℝ) 1 := by
  induction w generalizing S with
  | nil => simpa using hS
  | cons m w ih =>
      rw [runFrom_cons]
      exact ih (step_subset_Ioo h m hS)

/-- Every knot of every reachable configuration lies in the open interval
`(0, 1)`. -/
theorem run_subset_Ioo (h : 1 < lam) (w : List Move) :
    ∀ y ∈ run lam w, y ∈ Set.Ioo (0:ℝ) 1 :=
  runFrom_subset_Ioo h w (by simp)

/-- A general invariance principle: if a set contains `1/2` and is closed under
the action of a move on its survivors, it contains every knot of every
reachable configuration. -/
theorem run_subset (A : Set ℝ) (hhalf : (1/2 : ℝ) ∈ A)
    (hclosed : ∀ x ∈ A, ∀ m : Move, survives lam m x → act lam m x ∈ A)
    (w : List Move) : ∀ y ∈ run lam w, y ∈ A := by
  have key : ∀ (w : List Move) (S : Finset ℝ), (∀ x ∈ S, x ∈ A) →
      ∀ y ∈ runFrom lam S w, y ∈ A := by
    intro w
    induction w with
    | nil => intro S hS; simpa using hS
    | cons m w ih =>
        intro S hS
        rw [runFrom_cons]
        refine ih _ ?_
        intro y hy
        rcases mem_step.mp hy with ⟨x, hxS, hx, rfl⟩ | ⟨-, rfl⟩
        · exact hclosed x (hS x hxS) m hx
        · exact hhalf
  exact key w ∅ (by simp)

lemma runFrom_append (S : Finset ℝ) (u v : List Move) :
    runFrom lam S (u ++ v) = runFrom lam (runFrom lam S u) v := by
  simp [runFrom, List.foldl_append]

/-! ## T5: the scheduling bound -/

/-- The combinatorial core of **T5**.  Let `T` be a finite set of knots inside
`(0, 1)`, each surviving the whole word `b`, and suppose every two of them are
far enough apart that `lam ^ |b|` times their distance is at least `1`.  Then
`T` has at most `|b| + 1` elements.

The proof is the induction behind the pigeonhole argument: after one move either
no pair straddles, and every distance is multiplied by `lam`, or one pair does,
and deleting the largest knot below the deleted interval restores the
hypothesis while lowering the count by one. -/
theorem card_le_length_succ (h : 1 < lam) (b : List Move) :
    ∀ T : Finset ℝ,
      (∀ x ∈ T, x ∈ Set.Ioo (0:ℝ) 1) →
      (∀ x ∈ T, survivesWord lam x b) →
      (∀ x ∈ T, ∀ y ∈ T, x < y → 1 ≤ lam ^ b.length * (y - x)) →
      T.card ≤ b.length + 1 := by
  have hlam0 : (0:ℝ) < lam := lt_trans zero_lt_one h
  induction b with
  | nil =>
    intro T h01 _ hgap
    simp only [List.length_nil, Nat.zero_add]
    rw [Finset.card_le_one]
    intro x hx y hy
    by_contra hne
    have hx01 := h01 x hx
    have hy01 := h01 y hy
    rcases lt_or_gt_of_ne hne with hxy | hxy
    · have := hgap x hx y hy hxy
      simp only [List.length_nil, pow_zero, one_mul] at this
      exact absurd this (by simp only [Set.mem_Ioo] at hx01 hy01; linarith)
    · have := hgap y hy x hx hxy
      simp only [List.length_nil, pow_zero, one_mul] at this
      exact absurd this (by simp only [Set.mem_Ioo] at hx01 hy01; linarith)
  | cons m b' ih =>
    intro T h01 hsurv hgap
    have hpow : (0:ℝ) < lam ^ b'.length := pow_pos hlam0 _
    have hsm : ∀ x ∈ T, survives lam m x := fun x hx => (hsurv x hx).1
    have hsw : ∀ x ∈ T, survivesWord lam (act lam m x) b' := fun x hx => (hsurv x hx).2
    -- the reduction step, applied to a subset `U` of `T`
    have key : ∀ U : Finset ℝ, U ⊆ T →
        (∀ x ∈ U, ∀ y ∈ U, x < y →
          1 ≤ lam ^ b'.length * (act lam m y - act lam m x)) →
        U.card ≤ b'.length + 1 := by
      intro U hUT hU
      have himg : (U.image (act lam m)).card = U.card :=
        Finset.card_image_of_injOn (fun x hx y hy hxy =>
          act_injOn h m (hsm x (hUT hx)) (hsm y (hUT hy)) hxy)
      rw [← himg]
      refine ih _ ?_ ?_ ?_
      · intro X hX
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hX
        exact act_mem_Ioo h (h01 x (hUT hx)) (hsm x (hUT hx))
      · intro X hX
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hX
        exact hsw x (hUT hx)
      · intro X hX Y hY hXY
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hX
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hY
        have hxy : x < y := by
          rcases lt_trichotomy x y with hlt | heq | hgt
          · exact hlt
          · rw [heq] at hXY; exact absurd hXY (lt_irrefl _)
          · exact absurd (act_lt_act h m (hsm y (hUT hy)) (hsm x (hUT hx)) hgt) (asymm hXY)
        exact hU x hx y hy hxy
    by_cases hstr : m = Move.M ∧ (T.filter (fun x => x < r lam / 2)).Nonempty ∧
        (T.filter (fun x => ¬ x < r lam / 2)).Nonempty
    · -- a straddling pair may exist: delete the largest knot below the deleted interval
      obtain ⟨hm, hlo, -⟩ := hstr
      set Slo := T.filter (fun x => x < r lam / 2) with hSlo
      set xm := Slo.max' hlo with hxm
      have hxmS : xm ∈ Slo := Slo.max'_mem hlo
      have hxmT : xm ∈ T := (Finset.mem_filter.mp hxmS).1
      have hxmlt : xm < r lam / 2 := (Finset.mem_filter.mp hxmS).2
      have hUcard : (T.erase xm).card + 1 = T.card := Finset.card_erase_add_one hxmT
      have hbound : (T.erase xm).card ≤ b'.length + 1 := by
        refine key (T.erase xm) (Finset.erase_subset _ _) ?_
        intro x hx y hy hxy
        have hxT : x ∈ T := Finset.mem_of_mem_erase hx
        have hyT : y ∈ T := Finset.mem_of_mem_erase hy
        rcases gap_law h m (hsm x hxT) (hsm y hyT) hxy with heq | ⟨-, hstrad, heq⟩
        · rw [heq]
          have := hgap x hxT y hyT hxy
          simp only [List.length_cons, pow_succ] at this ⊢
          calc (1:ℝ) ≤ lam ^ b'.length * lam * (y - x) := this
            _ = lam ^ b'.length * (lam * (y - x)) := by ring
        · -- `x` is below the deleted interval but is not the largest such knot
          have hxSlo : x ∈ Slo := Finset.mem_filter.mpr ⟨hxT, hstrad.1⟩
          have hxne : x ≠ xm := Finset.ne_of_mem_erase hx
          have hxlt : x < xm := lt_of_le_of_ne (Slo.le_max' x hxSlo) hxne
          have hpos : lam * xm < lam * y - (lam - 1) := straddle h hxmlt hstrad.2
          have hdiff : lam * (xm - x) < act lam m y - act lam m x := by
            rw [heq]; nlinarith
          have hbase := hgap x hxT xm hxmT hxlt
          simp only [List.length_cons, pow_succ] at hbase
          nlinarith [mul_lt_mul_of_pos_left hdiff hpow]
      simp only [List.length_cons]
      omega
    · -- no straddling pair: every distance is multiplied by `lam`
      have hnostr : ∀ x ∈ T, ∀ y ∈ T, x < y → ¬ (m = Move.M ∧ Straddles lam x y) := by
        rintro x hx y hy - ⟨hm, hs⟩
        refine hstr ⟨hm, ⟨x, Finset.mem_filter.mpr ⟨hx, hs.1⟩⟩,
          ⟨y, Finset.mem_filter.mpr ⟨hy, ?_⟩⟩⟩
        have := half_lt_one_sub_half h
        exact not_lt.mpr (le_of_lt (lt_trans this hs.2))
      have hbound : T.card ≤ b'.length + 1 := by
        refine key T (subset_refl _) ?_
        intro x hx y hy hxy
        rcases gap_law h m (hsm x hx) (hsm y hy) hxy with heq | ⟨hm, hs, -⟩
        · rw [heq]
          have := hgap x hx y hy hxy
          simp only [List.length_cons, pow_succ] at this ⊢
          calc (1:ℝ) ≤ lam ^ b'.length * lam * (y - x) := this
            _ = lam ^ b'.length * (lam * (y - x)) := by ring
        · exact absurd ⟨hm, hs⟩ (hnostr x hx y hy hxy)
      simp only [List.length_cons]
      omega

/-- **T5 (scheduling theorem).**  Fix `lam > 1` and a run `w`.  Suppose there is
a `delta > 0` such that at every moment of the run any two distinct coexisting
knots are at distance at least `delta`, and let `W` be a natural number with
`lam ^ W * delta ≥ 1`.  Then the number of knots at the end of the run is at
most `W + ⌈W/2⌉ + 1` (written `W + (W + 1) / 2 + 1` in natural-number
arithmetic).

"At every moment" is expressed as a condition on every prefix `u` of `w`:
`run lam u` is the configuration reached after the first `|u|` moves. -/
theorem scheduling_bound (h : 1 < lam) {delta : ℝ} (W : ℕ)
    (hW : 1 ≤ lam ^ W * delta) (w : List Move)
    (hsep : ∀ u v : List Move, w = u ++ v →
      ∀ x ∈ run lam u, ∀ y ∈ run lam u, x ≠ y → delta ≤ |x - y|) :
    (run lam w).card ≤ W + (W + 1) / 2 + 1 := by
  have hlam0 : (0:ℝ) < lam := lt_trans zero_lt_one h
  set n := w.length with hn
  set a := w.take (n - W) with ha
  set b := w.drop (n - W) with hb
  have hab : w = a ++ b := (List.take_append_drop _ _).symm
  have hcard : (run lam w).card
      = ((run lam a).filter (fun x => survivesWord lam x b)).card + births lam b := by
    conv_lhs => rw [hab]
    rw [run, runFrom_append, ← run, card_runFrom h]
  have hblen : b.length = n - (n - W) := by rw [hb, List.length_drop]
  by_cases hWn : W ≤ n
  · have hbW : b.length = W := by omega
    have hold : ((run lam a).filter (fun x => survivesWord lam x b)).card ≤ W + 1 := by
      have := card_le_length_succ (lam := lam) h b
        ((run lam a).filter (fun x => survivesWord lam x b)) ?_ ?_ ?_
      · rwa [hbW] at this
      · intro x hx
        exact run_subset_Ioo h a x (Finset.mem_filter.mp hx).1
      · intro x hx
        exact (Finset.mem_filter.mp hx).2
      · intro x hx y hy hxy
        have hxa : x ∈ run lam a := (Finset.mem_filter.mp hx).1
        have hya : y ∈ run lam a := (Finset.mem_filter.mp hy).1
        have hne : x ≠ y := ne_of_lt hxy
        have hdxy : delta ≤ y - x := by
          have := hsep a b hab x hxa y hya hne
          rwa [abs_of_neg (by linarith : x - y < 0), neg_sub] at this
        rw [hbW]
        calc (1:ℝ) ≤ lam ^ W * delta := hW
          _ ≤ lam ^ W * (y - x) := by
              exact mul_le_mul_of_nonneg_left hdxy (le_of_lt (pow_pos hlam0 W))
    have hnew : births lam b ≤ (W + 1) / 2 := by
      have := births_le_ceil_half h b
      rw [hbW] at this
      exact this
    omega
  · have hz : n - W = 0 := by omega
    have haempty : a = [] := by rw [ha, hz]; simp
    have hbw : b = w := by rw [hb, hz]; simp
    have hfilter : ((run lam a).filter (fun x => survivesWord lam x b)).card = 0 := by
      rw [haempty]
      simp [run]
    have hnew : births lam b ≤ (W + 1) / 2 := by
      have := births_le_ceil_half h b
      have hbl : b.length = n := by rw [hbw]
      omega
    omega

/-- **T5, applied to the knot count.**  If every two distinct coexisting knots
of every run are at distance at least `delta > 0`, and `lam ^ W * delta ≥ 1`,
then `N lam n ≤ W + ⌈W/2⌉ + 1` for every `n`. -/
theorem N_le_of_separated (h : 1 < lam) {delta : ℝ} (W : ℕ)
    (hW : 1 ≤ lam ^ W * delta)
    (hsep : ∀ u : List Move, ∀ x ∈ run lam u, ∀ y ∈ run lam u, x ≠ y → delta ≤ |x - y|)
    (n : ℕ) : N lam n ≤ W + (W + 1) / 2 + 1 := by
  apply Finset.sup_le
  intro v _
  exact scheduling_bound h W hW _ (fun u _ _ => hsep u)

/-- **Near-collisions are necessary** (the corollary the paper draws from T5 in
the other direction).  If a run reaches `k` simultaneous knots and
`3*m + 4 < 2*k` — that is, `m < 2(k-2)/3` — then at some moment of the run two
distinct coexisting knots lie within `(lam ^ m)⁻¹` of one another. -/
theorem near_collision (h : 1 < lam) (w : List Move) (m : ℕ)
    (hm : 3 * m + 4 < 2 * (run lam w).card) :
    ∃ u v : List Move, w = u ++ v ∧
      ∃ x ∈ run lam u, ∃ y ∈ run lam u, x ≠ y ∧ |x - y| < (lam ^ m)⁻¹ := by
  by_contra hc
  push_neg at hc
  have hpow : (0:ℝ) < lam ^ m := pow_pos (lt_trans zero_lt_one h) m
  have hW : 1 ≤ lam ^ m * (lam ^ m)⁻¹ := by
    rw [mul_inv_cancel₀ (ne_of_gt hpow)]
  have := scheduling_bound h m hW w (fun u v huv x hx y hy hxy => hc u v huv x hx y hy hxy)
  omega

end KnotGame
