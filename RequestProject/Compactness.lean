import RequestProject.Permanence

/-!
# T17 — the compactness criterion (paper Theorem `thm:compactness`)

A **left-infinite run** is a function `b : ℕ → Move`, read as ever-longer
suffixes: `b i` is the letter `i + 1` places from the end, so the last `a`
letters of the run form the word `sfx b a`.  The run carries a knot of age `a`
exactly when the letter `b a` is an `M` and `1/2` survives the `a` letters
after it (`InfKnotAge`); the point annihilated at backward step `a` is then
the image of `1/2` under those `a` letters.

The three conditions of the paper are rendered as

* `InfinitelyManyKnots` — (i) some left-infinite run carries infinitely many
  simultaneous knots;
* `InfinitelyManyAnnihilations` — (ii) in the backward reading of some run,
  infinitely many points are annihilated;
* `BoundedAgeWitnesses` — (iii) there are words with `k` knots for every `k`
  whose age vectors are pointwise bounded in `k`.

and the file proves `(i) ↔ (ii)`, `(i) → (iii)`, `(iii) → (i)` and that any of
them implies `N_λ = ∞`.  The rendering, and the fact that (i) and (ii) are two
readings of one definition, is recorded in `SCRUPLES-round5.md`.

The proof of `(iii) → (i)` is the compactness step.  It is carried out with a
non-principal ultrafilter on `ℕ` (`Filter.hyperfilter`) in place of a
diagonal subsequence: `Move` is finite and the ages are bounded, so both the
letters and the ages have ultrafilter limits, and along the ultrafilter the
witnesses agree with the limiting run on ever-longer suffixes.
-/

namespace KnotGame

open Filter

variable {lam : ℝ}

/-! ## Left-infinite runs -/

/-- The last `a` letters of the left-infinite run `b`, as a word read forward. -/
def sfx (b : ℕ → Move) : ℕ → List Move
  | 0 => []
  | a + 1 => b a :: sfx b a

@[simp] lemma sfx_zero (b : ℕ → Move) : sfx b 0 = [] := rfl

@[simp] lemma sfx_succ (b : ℕ → Move) (a : ℕ) : sfx b (a + 1) = b a :: sfx b a := rfl

@[simp] lemma length_sfx (b : ℕ → Move) : ∀ a, (sfx b a).length = a
  | 0 => rfl
  | a + 1 => by simp [length_sfx b a]

lemma sfx_congr {b b' : ℕ → Move} : ∀ (a : ℕ), (∀ n, n < a → b n = b' n) → sfx b a = sfx b' a
  | 0, _ => rfl
  | a + 1, hb => by
      rw [sfx_succ, sfx_succ, hb a (Nat.lt_succ_self a),
        sfx_congr a (fun n hn => hb n (Nat.lt_succ_of_lt hn))]

/-- Every letter of a left-infinite run heads a suffix of every longer one. -/
lemma sfx_split (b : ℕ → Move) : ∀ {a n : ℕ}, a < n → ∃ p, sfx b n = p ++ (b a :: sfx b a)
  | a, 0, h => absurd h (Nat.not_lt_zero a)
  | a, n + 1, h => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp h with hlt | rfl
      · obtain ⟨p, hp⟩ := sfx_split b hlt
        exact ⟨b n :: p, by rw [sfx_succ, hp]; rfl⟩
      · exact ⟨[], rfl⟩

/-- The left-infinite run `b` carries a knot of age `a`: the letter `b a` is an
`M` and `1/2` survives the `a` letters that follow it. -/
def InfKnotAge (lam : ℝ) (b : ℕ → Move) (a : ℕ) : Prop :=
  b a = Move.M ∧ survivesWord lam (1/2) (sfx b a)

/-- The position of the knot of age `a` of the left-infinite run `b`; read
backwards, this is the point annihilated at backward step `a`. -/
noncomputable def infKnotPos (lam : ℝ) (b : ℕ → Move) (a : ℕ) : ℝ :=
  posAfter lam (1/2) (sfx b a)

/-- A knot of a left-infinite run is a knot of each of its long enough
truncations, at the same position and the same age. -/
lemma knotAt_of_infKnotAge {b : ℕ → Move} {a n : ℕ} (hlt : a < n) (hk : InfKnotAge lam b a) :
    KnotAt lam (sfx b n) a (infKnotPos lam b a) := by
  obtain ⟨p, hp⟩ := sfx_split b hlt
  exact ⟨p, sfx b a, by rw [hp, hk.1], length_sfx b a, hk.2, rfl⟩

/-- **(i)** Some left-infinite run carries infinitely many simultaneous
knots. -/
def InfinitelyManyKnots (lam : ℝ) : Prop :=
  ∃ b : ℕ → Move, {a | InfKnotAge lam b a}.Infinite

/-- The set of points annihilated in the backward reading of the run `b`. -/
def annihilated (lam : ℝ) (b : ℕ → Move) : Set ℝ :=
  {x | ∃ a, InfKnotAge lam b a ∧ infKnotPos lam b a = x}

/-- **(ii)** In the backward reading of some run, infinitely many points are
annihilated. -/
def InfinitelyManyAnnihilations (lam : ℝ) : Prop :=
  ∃ b : ℕ → Move, (annihilated lam b).Infinite

/-- **(iii)** There are words `w k` carrying `k` knots — of ages
`ag k 0 < … < ag k (k-1)` — whose age vectors are pointwise bounded in `k`. -/
def BoundedAgeWitnesses (lam : ℝ) : Prop :=
  ∃ (A : ℕ → ℕ) (w : ℕ → List Move) (ag : ℕ → ℕ → ℕ),
    ∀ k, (∀ i, i < k → HasKnotAge lam (w k) (ag k i)) ∧
      (∀ i j, i < j → j < k → ag k i < ag k j) ∧
      (∀ i, i < k → ag k i ≤ A i)

/-! ## (i) ⟺ (ii): the two readings of one definition -/

lemma annihilated_eq_image (lam : ℝ) (b : ℕ → Move) :
    annihilated lam b = (infKnotPos lam b) '' {a | InfKnotAge lam b a} := by
  ext x
  simp only [annihilated, Set.mem_setOf_eq, Set.mem_image]

/-- Distinct ages of a left-infinite run carry distinct points. -/
lemma infKnotPos_injOn (h : 1 < lam) (b : ℕ → Move) :
    Set.InjOn (infKnotPos lam b) {a | InfKnotAge lam b a} := by
  intro a ha a' ha' hpos
  have h1 := knotAt_of_infKnotAge (lam := lam) (b := b) (a := a)
    (n := max a a' + 1) (by omega) ha
  have h2 := knotAt_of_infKnotAge (lam := lam) (b := b) (a := a')
    (n := max a a' + 1) (by omega) ha'
  rw [hpos] at h1
  exact knotAt_age_inj h h1 h2

/-- **T17, (i) ⟺ (ii)** (paper Theorem `thm:compactness`).  The two conditions
are the same statement read in the two directions. -/
theorem infinitelyManyKnots_iff_annihilations (h : 1 < lam) :
    InfinitelyManyKnots lam ↔ InfinitelyManyAnnihilations lam := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    rw [annihilated_eq_image]
    exact hb.image (infKnotPos_injOn h b)
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    rw [annihilated_eq_image] at hb
    exact hb.of_image _

/-! ## (i) ⟹ (iii) -/

/-- **T17, (i) ⟹ (iii)**.  Truncating a left-infinite run gives witnesses whose
age vectors are not merely bounded but constant in `k`. -/
theorem boundedAgeWitnesses_of_infinitelyManyKnots
    (H : InfinitelyManyKnots lam) : BoundedAgeWitnesses lam := by
  obtain ⟨b, hb⟩ := H
  have hinf : (setOf (fun a => InfKnotAge lam b a)).Infinite := hb
  refine ⟨fun i => Nat.nth (fun a => InfKnotAge lam b a) i,
    fun k => sfx b (Nat.nth (fun a => InfKnotAge lam b a) k + 1),
    fun _ i => Nat.nth (fun a => InfKnotAge lam b a) i, fun k => ⟨?_, ?_, ?_⟩⟩
  · intro i hik
    have hlt : Nat.nth (fun a => InfKnotAge lam b a) i
        < Nat.nth (fun a => InfKnotAge lam b a) k := (Nat.nth_lt_nth hinf).mpr hik
    have hknot := knotAt_of_infKnotAge (lam := lam) (b := b)
      (a := Nat.nth (fun a => InfKnotAge lam b a) i)
      (n := Nat.nth (fun a => InfKnotAge lam b a) k + 1) (by omega)
      (Nat.nth_mem_of_infinite hinf i)
    exact ⟨_, hknot⟩
  · intro i j hij _
    exact (Nat.nth_lt_nth hinf).mpr hij
  · intro i _
    exact le_refl _

/-! ## Reading a finite word backwards -/

/-- The letters of the word `W` read from the end, padded with `L`. -/
def back (W : List Move) (n : ℕ) : Move := W.reverse.getD n Move.L

lemma sfx_back_of_agree : ∀ (l : List Move) (b : ℕ → Move),
    (∀ n, n < l.length → b n = l.reverse.getD n Move.L) → sfx b l.length = l
  | [], _, _ => rfl
  | c :: t, b, hb => by
      have hlen : (c :: t).length = t.length + 1 := rfl
      have hrev : (c :: t).reverse = t.reverse ++ [c] := by simp
      have hc : b t.length = c := by
        rw [hb t.length (by simp), hrev,
          List.getD_append_right _ _ _ _ (by simp)]
        simp
      have ht : sfx b t.length = t := by
        refine sfx_back_of_agree t b ?_
        intro n hn
        rw [hb n (by simp; omega), hrev, List.getD_append _ _ _ n (by simpa using hn)]
      rw [hlen, sfx_succ, hc, ht]

/-- A knot of age `a` in the word `W` is a knot of age `a` of the left-infinite
run obtained by reading `W` backwards. -/
lemma infKnotAge_back {W : List Move} {a : ℕ} (hk : HasKnotAge lam W a) :
    InfKnotAge lam (back W) a := by
  obtain ⟨x, q, s, rfl, rfl, hsurv, -⟩ := hk
  have hrev : (q ++ Move.M :: s).reverse = s.reverse ++ (Move.M :: q.reverse) := by
    simp
  constructor
  · rw [back, hrev, List.getD_append_right _ _ _ _ (by simp)]
    simp
  · have : sfx (back (q ++ Move.M :: s)) s.length = s := by
      refine sfx_back_of_agree s _ ?_
      intro n hn
      rw [back, hrev, List.getD_append _ _ _ n (by simpa using hn)]
    rw [this]
    exact hsurv

/-! ## (iii) ⟹ (i): compactness -/

private lemma exists_ultrafilter_value (U : Ultrafilter ℕ) (g : ℕ → ℕ)
    (S : Finset ℕ) (hS : ∀ k, g k ∈ S) : ∃ v ∈ S, {k | g k = v} ∈ U := by
  have huniv : (⋃ v ∈ (S : Set ℕ), {k | g k = v}) ∈ U := by
    have : (⋃ v ∈ (S : Set ℕ), {k | g k = v}) = Set.univ := by
      ext k
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true, exists_prop]
      exact ⟨g k, hS k, rfl⟩
    rw [this]
    exact Filter.univ_mem
  obtain ⟨v, hv, hvU⟩ := (Ultrafilter.finite_biUnion_mem_iff (S.finite_toSet)).mp huniv
  exact ⟨v, hv, hvU⟩

private lemma exists_ultrafilter_move (U : Ultrafilter ℕ) (g : ℕ → Move) :
    ∃ m : Move, {k | g k = m} ∈ U := by
  have huniv : (⋃ m ∈ (Set.univ : Set Move), {k | g k = m}) ∈ U := by
    have : (⋃ m ∈ (Set.univ : Set Move), {k | g k = m}) = Set.univ := by
      ext k
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true, exists_prop]
      exact ⟨g k, trivial, rfl⟩
    rw [this]
    exact Filter.univ_mem
  obtain ⟨m, -, hm⟩ := (Ultrafilter.finite_biUnion_mem_iff (Set.finite_univ)).mp huniv
  exact ⟨m, hm⟩

/-- **T17, (iii) ⟹ (i)** (paper Theorem `thm:compactness`).  Bounded age
vectors produce a single left-infinite run with infinitely many knots. -/
theorem infinitelyManyKnots_of_boundedAgeWitnesses
    (H : BoundedAgeWitnesses lam) : InfinitelyManyKnots lam := by
  classical
  obtain ⟨A, w, ag, hw⟩ := H
  set U : Ultrafilter ℕ := hyperfilter ℕ with hU
  have hcof : ∀ s : Set ℕ, sᶜ.Finite → s ∈ U := by
    intro s hs
    exact Filter.hyperfilter_le_cofinite (Filter.mem_cofinite.mpr hs)
  -- the limiting run
  have hbex : ∀ n : ℕ, ∃ m : Move, {k | back (w k) n = m} ∈ U :=
    fun n => exists_ultrafilter_move U (fun k => back (w k) n)
  choose b hb using hbex
  -- the limiting ages
  have hagex : ∀ i : ℕ, ∃ v : ℕ, {k | ag k i = v} ∈ U := by
    intro i
    have hmem : ∀ k, (if i < k then ag k i else 0) ∈ Finset.range (A i + 1) := by
      intro k
      by_cases hik : i < k
      · rw [if_pos hik]
        exact Finset.mem_range.mpr (by have := (hw k).2.2 i hik; omega)
      · rw [if_neg hik]; simp
    obtain ⟨v, -, hv⟩ := exists_ultrafilter_value U _ (Finset.range (A i + 1)) hmem
    refine ⟨v, ?_⟩
    have hlarge : {k | i < k} ∈ U := hcof _ (by
      have : {k : ℕ | i < k}ᶜ ⊆ Set.Iic i := by
        intro k hk
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hk
        exact hk
      exact Set.Finite.subset (Set.finite_Iic i) this)
    have := Filter.inter_mem hv hlarge
    refine Filter.mem_of_superset this ?_
    rintro k ⟨hk1, hk2⟩
    simp only [Set.mem_setOf_eq] at hk1 hk2 ⊢
    rwa [if_pos hk2] at hk1
  choose alpha halpha using hagex
  -- the set of indices witnessing the `i`-th age
  have hTi : ∀ i : ℕ, {k | i < k} ∩ ({k | ag k i = alpha i} ∩
      {k | ∀ n, n ≤ alpha i → back (w k) n = b n}) ∈ U := by
    intro i
    have hlarge : {k | i < k} ∈ U := hcof _ (by
      have : {k : ℕ | i < k}ᶜ ⊆ Set.Iic i := by
        intro k hk
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hk
        exact hk
      exact Set.Finite.subset (Set.finite_Iic i) this)
    have hagree : {k | ∀ n, n ≤ alpha i → back (w k) n = b n} ∈ U := by
      have hfin : (⋂ n ∈ Finset.range (alpha i + 1), {k | back (w k) n = b n}) ∈ U :=
        (Filter.biInter_finset_mem _).mpr (fun n _ => hb n)
      refine Filter.mem_of_superset hfin ?_
      intro k hk n hn
      simp only [Set.mem_iInter, Set.mem_setOf_eq, Finset.mem_range] at hk
      exact hk n (by omega)
    exact Filter.inter_mem hlarge (Filter.inter_mem (halpha i) hagree)
  -- each limiting age is a knot age of the limiting run
  have hknot : ∀ i : ℕ, InfKnotAge lam b (alpha i) := by
    intro i
    obtain ⟨k, hk1, hk2, hk3⟩ := Filter.nonempty_of_mem (hTi i)
    have hka : HasKnotAge lam (w k) (alpha i) := by
      have := (hw k).1 i hk1
      rwa [hk2] at this
    obtain ⟨hM, hsurv⟩ := infKnotAge_back hka
    refine ⟨?_, ?_⟩
    · rw [← hk3 (alpha i) (le_refl _)]; exact hM
    · rwa [sfx_congr (alpha i) (fun n hn => hk3 n (le_of_lt hn))] at hsurv
  -- the limiting ages are distinct
  have hmono : ∀ i j, i < j → alpha i < alpha j := by
    intro i j hij
    obtain ⟨k, hki, hkj⟩ := Filter.nonempty_of_mem (Filter.inter_mem (hTi i) (hTi j))
    obtain ⟨-, hi2, -⟩ := hki
    obtain ⟨hj1, hj2, -⟩ := hkj
    have hlt := (hw k).2.1 i j hij hj1
    rwa [hi2, hj2] at hlt
  have hsm : StrictMono alpha := fun i j hij => hmono i j hij
  have hinj : Function.Injective alpha := hsm.injective
  exact ⟨b, Set.infinite_of_injective_forall_mem hinj hknot⟩

/-! ## Any of the three implies `N_λ = ∞` -/

/-- **T17, last part.**  Any of the three conditions implies that the knot
counts `N_λ(n)` are unbounded. -/
theorem N_unbounded_of_infinitelyManyKnots (h : 1 < lam) (H : InfinitelyManyKnots lam) :
    ∀ K : ℕ, ∃ n : ℕ, K ≤ N lam n := by
  obtain ⟨b, hb⟩ := H
  intro K
  have hinf : (setOf (fun a => InfKnotAge lam b a)).Infinite := hb
  refine ⟨Nat.nth (fun a => InfKnotAge lam b a) K + 1, ?_⟩
  classical
  set W := sfx b (Nat.nth (fun a => InfKnotAge lam b a) K + 1) with hW
  set Ages : Finset ℕ :=
    (Finset.range K).image (fun i => Nat.nth (fun a => InfKnotAge lam b a) i) with hAges
  have hcard : Ages.card = K := by
    rw [hAges, Finset.card_image_of_injective _ (Nat.nth_strictMono hinf).injective,
      Finset.card_range]
  have hages : ∀ a ∈ Ages, HasKnotAge lam W a := by
    intro a ha
    rw [hAges, Finset.mem_image] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    have hlt : Nat.nth (fun a => InfKnotAge lam b a) i
        < Nat.nth (fun a => InfKnotAge lam b a) K :=
      (Nat.nth_lt_nth hinf).mpr (Finset.mem_range.mp hi)
    have hknot := knotAt_of_infKnotAge (lam := lam) (b := b)
      (a := Nat.nth (fun a => InfKnotAge lam b a) i)
      (n := Nat.nth (fun a => InfKnotAge lam b a) K + 1) (by omega)
      (Nat.nth_mem_of_infinite hinf i)
    exact ⟨_, hknot⟩
  have hle : K ≤ (run lam W).card := by
    rw [← hcard]
    exact card_run_ge_of_ages h W Ages hages
  have hlen : W.length = Nat.nth (fun a => InfKnotAge lam b a) K + 1 := length_sfx b _
  calc K ≤ (run lam W).card := hle
    _ = births lam W := card_run h W
    _ ≤ N lam W.length := births_le_N h W
    _ = N lam (Nat.nth (fun a => InfKnotAge lam b a) K + 1) := by rw [hlen]

end KnotGame
