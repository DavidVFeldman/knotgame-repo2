import RequestProject.BranchingContinuum

/-!
# The linear count of surviving branch words (round 4, T12b)

Let `K lam m` be the number of length-`m` branch words along which `1/2`
survives.  On a window `[lam₀, lam₁] ⊆ (1, φ)` with return bound `B` (the data
of T11d) we prove the unconditional linear bound

  `m / (B+1) ≤ K lam m`   (natural division).

The argument is the one of the note: follow the *spine*, the orbit of `1/2` that
always takes the good child of T11c.  By T11c + T11d the spine visits the window
at times `visit 0 = 0 < visit 1 < ⋯` with gaps at most `B+1`, so at least
`m/(B+1)` of these times are `< m`.  Deviating from the spine at exactly one
window visit produces a surviving word, and words deviating at different visits
differ at the earlier of the two visits.

## Conventions (SCRUPLES)

* A *length-`m` branch word* is a function `Fin m → Fin 2`; it survives from
  `1/2` when every one of its `m` branches is legal at the point reached so far
  (`SurvivesUpTo`, and equivalently `bSurvives` on the corresponding list).
* Only `m/(B+1)` words are exhibited — the spine's own word is not counted, so
  the bound is not off by one in the wrong direction.
-/

namespace KnotGame
namespace Branching

open Set
open scoped Classical

variable {lam lam0 lam1 : ℝ}

/-! ### The spine: always take the good child -/

/-- One step of the canonical ("good child") dynamics. -/
noncomputable def cstep (lam : ℝ) (x : ℝ) : ℝ := f lam (cb lam x) x

/-- The canonical orbit of `x`. -/
noncomputable def spine (lam : ℝ) (x : ℝ) (n : ℕ) : ℝ := (cstep lam)^[n] x

@[simp] lemma spine_zero (lam x : ℝ) : spine lam x 0 = x := rfl

lemma spine_succ (lam x : ℝ) (n : ℕ) : spine lam x (n + 1) = cstep lam (spine lam x n) :=
  Function.iterate_succ_apply' _ _ _

lemma spine_add (lam x : ℝ) (n k : ℕ) : spine lam x (n + k) = spine lam (spine lam x n) k := by
  rw [spine, spine, spine, show n + k = k + n from Nat.add_comm _ _,
    Function.iterate_add_apply]

lemma Window_subset_Ioo (h1 : 1 < lam) {x : ℝ} (hx : x ∈ Window lam) :
    x ∈ Set.Ioo (0:ℝ) 1 :=
  ⟨lt_trans (g_pos lam h1) hx.1, lt_trans hx.2 (r_lt_one lam h1)⟩

lemma cstep_mem_Ioo (h1 : 1 < lam) (h2 : lam < 2) {x : ℝ} (hx : x ∈ Set.Ioo (0:ℝ) 1) :
    cstep lam x ∈ Set.Ioo (0:ℝ) 1 :=
  f_mem_Ioo h1 hx (cb_legal h1 h2 x)

lemma spine_mem_Ioo (h1 : 1 < lam) (h2 : lam < 2) {x : ℝ} (hx : x ∈ Set.Ioo (0:ℝ) 1) (n : ℕ) :
    spine lam x n ∈ Set.Ioo (0:ℝ) 1 := by
  induction n with
  | zero => simpa using hx
  | succ n ih => rw [spine_succ]; exact cstep_mem_Ioo h1 h2 ih

/-- While it stays in `(0, g]`, the spine is the forced branch-`0` orbit. -/
lemma spine_eq_iterate_zero (h1 : 1 < lam) (h2 : lam < 2) {y : ℝ} {k : ℕ}
    (hall : ∀ j < k, (f lam 0)^[j] y ≤ g lam) : spine lam y k = (f lam 0)^[k] y := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk := ih (fun j hj => hall j (by omega))
      rw [spine_succ, hk, cstep, cb_of_le_g h1 h2 (hall k (by omega)),
        Function.iterate_succ_apply']

/-- While it stays in `[r, 1)`, the spine is the forced branch-`1` orbit. -/
lemma spine_eq_iterate_one (h1 : 1 < lam) (h2 : lam < 2) {y : ℝ} {k : ℕ}
    (hall : ∀ j < k, r lam ≤ (f lam 1)^[j] y) : spine lam y k = (f lam 1)^[k] y := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk := ih (fun j hj => hall j (by omega))
      rw [spine_succ, hk, cstep, cb_of_r_le h1 h2 (hall k (by omega)),
        Function.iterate_succ_apply']

/-- **The spine returns to the window within `B+1` steps.** -/
theorem spine_return {B : ℕ} (hB1 : 1 ≤ B) (h0 : 1 < lam0) (h0l : lam0 ≤ lam)
    (hl1 : lam ≤ lam1) (hphi1 : lam1 ^ 2 < lam1 + 1)
    (hB : g lam1 < lam0 ^ (B - 1) * eta lam0 lam1)
    {x : ℝ} (hx : x ∈ Window lam) :
    ∃ k, 1 ≤ k ∧ k ≤ B + 1 ∧ spine lam x k ∈ Window lam := by
  have h1 : 1 < lam := lt_of_lt_of_le h0 h0l
  have h1' : 1 < lam1 := lt_of_lt_of_le h1 hl1
  have h2 : lam < 2 := lt_of_le_of_lt hl1 (lt_two_of_sq_lt h1' hphi1)
  have hy : spine lam x 1 = cstep lam x := by rw [spine_succ]; simp
  have hgc := good_child h0 h0l hl1 hphi1 hx
  have hyIoo : cstep lam x ∈ Set.Ioo (0:ℝ) 1 :=
    cstep_mem_Ioo h1 h2 (Window_subset_Ioo h1 hx)
  by_cases hw : cstep lam x ∈ Window lam
  · exact ⟨1, le_rfl, by omega, by rw [hy]; exact hw⟩
  · have hout : cstep lam x ≤ g lam ∨ r lam ≤ cstep lam x := by
      rcases lt_or_ge (g lam) (cstep lam x) with hgy | hgy
      · rcases lt_or_ge (cstep lam x) (r lam) with hyr | hyr
        · exact absurd (mem_Window.mpr ⟨hgy, hyr⟩) hw
        · exact Or.inr hyr
      · exact Or.inl hgy
    rcases hout with hlow | hhigh
    · obtain ⟨k, hk, hkwin, hkbefore⟩ :=
        bounded_return_low hB1 h0 h0l hl1 hphi1 hB hgc.1 hlow
      refine ⟨1 + k, by omega, by omega, ?_⟩
      rw [spine_add, hy]
      show spine lam (f lam (cb lam x) x) k ∈ Window lam
      rw [spine_eq_iterate_zero h1 h2 (fun j hj => (hkbefore j hj).2)]
      exact hkwin
    · obtain ⟨k, hk, hkwin, hkbefore⟩ :=
        bounded_return_high hB1 h0 h0l hl1 hphi1 hB hhigh hgc.2
      refine ⟨1 + k, by omega, by omega, ?_⟩
      rw [spine_add, hy]
      rw [spine_eq_iterate_one h1 h2 (fun j hj => (hkbefore j hj).1)]
      exact hkwin

/-! ### The sequence of window visits along the spine -/

/-- The first window visit strictly after time `n`. -/
noncomputable def nextVisit (lam : ℝ) (x : ℝ) (n : ℕ) : ℕ :=
  sInf {k | n < k ∧ spine lam x k ∈ Window lam}

/-- The `i`-th window visit of the spine of `x` (with `visit 0 = 0`). -/
noncomputable def visit (lam : ℝ) (x : ℝ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => nextVisit lam x (visit lam x i)

lemma nextVisit_props {B : ℕ} (hB1 : 1 ≤ B) (h0 : 1 < lam0) (h0l : lam0 ≤ lam)
    (hl1 : lam ≤ lam1) (hphi1 : lam1 ^ 2 < lam1 + 1)
    (hB : g lam1 < lam0 ^ (B - 1) * eta lam0 lam1)
    {x : ℝ} {n : ℕ} (hn : spine lam x n ∈ Window lam) :
    n < nextVisit lam x n ∧ nextVisit lam x n ≤ n + (B + 1) ∧
      spine lam x (nextVisit lam x n) ∈ Window lam := by
  obtain ⟨k, hk1, hk2, hkwin⟩ := spine_return hB1 h0 h0l hl1 hphi1 hB hn
  have hmem : n + k ∈ {k | n < k ∧ spine lam x k ∈ Window lam} := by
    refine ⟨by omega, ?_⟩
    rw [spine_add]
    exact hkwin
  have hne : {k | n < k ∧ spine lam x k ∈ Window lam}.Nonempty := ⟨n + k, hmem⟩
  have hin := Nat.sInf_mem hne
  exact ⟨hin.1, le_trans (Nat.sInf_le hmem) (by omega), hin.2⟩

lemma visit_props {B : ℕ} (hB1 : 1 ≤ B) (h0 : 1 < lam0) (h0l : lam0 ≤ lam)
    (hl1 : lam ≤ lam1) (hphi1 : lam1 ^ 2 < lam1 + 1)
    (hB : g lam1 < lam0 ^ (B - 1) * eta lam0 lam1)
    {x : ℝ} (hx : x ∈ Window lam) (i : ℕ) :
    spine lam x (visit lam x i) ∈ Window lam ∧ visit lam x i ≤ i * (B + 1) := by
  induction i with
  | zero => simpa [visit] using hx
  | succ i ih =>
      obtain ⟨hwin, hle⟩ := ih
      obtain ⟨h1', h2', h3'⟩ := nextVisit_props hB1 h0 h0l hl1 hphi1 hB hwin
      refine ⟨h3', ?_⟩
      show nextVisit lam x (visit lam x i) ≤ (i + 1) * (B + 1)
      have : (i + 1) * (B + 1) = i * (B + 1) + (B + 1) := by ring
      omega

lemma visit_lt_succ {B : ℕ} (hB1 : 1 ≤ B) (h0 : 1 < lam0) (h0l : lam0 ≤ lam)
    (hl1 : lam ≤ lam1) (hphi1 : lam1 ^ 2 < lam1 + 1)
    (hB : g lam1 < lam0 ^ (B - 1) * eta lam0 lam1)
    {x : ℝ} (hx : x ∈ Window lam) (i : ℕ) : visit lam x i < visit lam x (i + 1) :=
  (nextVisit_props hB1 h0 h0l hl1 hphi1 hB
    (visit_props hB1 h0 h0l hl1 hphi1 hB hx i).1).1

lemma visit_strictMono {B : ℕ} (hB1 : 1 ≤ B) (h0 : 1 < lam0) (h0l : lam0 ≤ lam)
    (hl1 : lam ≤ lam1) (hphi1 : lam1 ^ 2 < lam1 + 1)
    (hB : g lam1 < lam0 ^ (B - 1) * eta lam0 lam1)
    {x : ℝ} (hx : x ∈ Window lam) : StrictMono (visit lam x) :=
  strictMono_nat_of_lt_succ (visit_lt_succ hB1 h0 h0l hl1 hphi1 hB hx)

/-! ### Deviating from the spine at one window visit -/

/-- The orbit that follows the spine except at time `t`, where it takes the other
child. -/
noncomputable def devOrbit (lam : ℝ) (x : ℝ) (t : ℕ) : ℕ → ℝ
  | 0 => x
  | n + 1 =>
      f lam (if n = t then cb lam (devOrbit lam x t n) + 1 else cb lam (devOrbit lam x t n))
        (devOrbit lam x t n)

/-- The itinerary of `devOrbit`. -/
noncomputable def devItin (lam : ℝ) (x : ℝ) (t : ℕ) (n : ℕ) : Fin 2 :=
  if n = t then cb lam (devOrbit lam x t n) + 1 else cb lam (devOrbit lam x t n)

lemma devOrbit_succ (lam x : ℝ) (t n : ℕ) :
    devOrbit lam x t (n + 1) = f lam (devItin lam x t n) (devOrbit lam x t n) := rfl

/-- Before the deviation the orbit is the spine. -/
lemma devOrbit_eq_spine (lam x : ℝ) {t n : ℕ} (hn : n ≤ t) :
    devOrbit lam x t n = spine lam x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hne : n ≠ t := by omega
      rw [devOrbit_succ, devItin, if_neg hne, ih (by omega), spine_succ, cstep]

/-- Before the deviation the itinerary is the spine's. -/
lemma devItin_eq_of_lt (lam x : ℝ) {t n : ℕ} (hn : n < t) :
    devItin lam x t n = cb lam (spine lam x n) := by
  rw [devItin, if_neg (by omega : n ≠ t), devOrbit_eq_spine lam x (by omega : n ≤ t)]

/-- At the deviation the itinerary is the *other* branch. -/
lemma devItin_at (lam x : ℝ) (t : ℕ) :
    devItin lam x t t = cb lam (spine lam x t) + 1 := by
  rw [devItin, if_pos rfl, devOrbit_eq_spine lam x (le_refl t)]

/-- The deviating orbit stays in `(0,1)` and every branch it takes is legal,
provided the deviation happens at a window visit. -/
lemma devOrbit_legal (h1 : 1 < lam) (h2 : lam < 2) {x : ℝ} (hx : x ∈ Set.Ioo (0:ℝ) 1)
    {t : ℕ} (ht : spine lam x t ∈ Window lam) (n : ℕ) :
    devOrbit lam x t n ∈ Set.Ioo (0:ℝ) 1 ∧
      BLegal lam (devItin lam x t n) (devOrbit lam x t n) := by
  induction n with
  | zero =>
      refine ⟨hx, ?_⟩
      by_cases h : (0 : ℕ) = t
      · rw [devItin, if_pos h]
        refine BLegal_of_mem_Window ?_ _
        have hz : devOrbit lam x t 0 = spine lam x t := by rw [← h]; rfl
        rw [hz]
        exact ht
      · rw [devItin, if_neg h]
        exact cb_legal h1 h2 _
  | succ n ih =>
      obtain ⟨hmem, hleg⟩ := ih
      have hmem' : devOrbit lam x t (n + 1) ∈ Set.Ioo (0:ℝ) 1 := by
        rw [devOrbit_succ]
        exact f_mem_Ioo h1 hmem hleg
      refine ⟨hmem', ?_⟩
      by_cases h : n + 1 = t
      · rw [devItin, if_pos h]
        refine BLegal_of_mem_Window ?_ _
        rw [devOrbit_eq_spine lam x (le_of_eq h), h]
        exact ht
      · rw [devItin, if_neg h]
        exact cb_legal h1 h2 _

/-! ### The count -/

/-- A length-`m` branch word, extended by branch `0` past its end. -/
def extendWord {m : ℕ} (w : Fin m → Fin 2) : ℕ → Fin 2 :=
  fun n => if h : n < m then w ⟨n, h⟩ else 0

/-- `1/2` survives the first `m` branches of the itinerary `e`. -/
noncomputable def SurvivesUpTo (lam : ℝ) (x : ℝ) (e : ℕ → Fin 2) (m : ℕ) : Prop :=
  ∀ n < m, BLegal lam (e n) (itinOrbit lam x e n)

/-- **`K lam m`: the number of length-`m` branch words along which `1/2`
survives.** -/
noncomputable def K (lam : ℝ) (m : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin m → Fin 2)).filter
    (fun w => SurvivesUpTo lam (1/2) (extendWord w) m)).card

/-- Survival of `x` along a finite branch word, presented as a list: each branch
in turn must be legal at the point reached so far. -/
noncomputable def bSurvives (lam : ℝ) : ℝ → List (Fin 2) → Prop
  | _, [] => True
  | x, e :: w => BLegal lam e x ∧ bSurvives lam (f lam e x) w

lemma itinOrbit_shift (lam x : ℝ) (e : ℕ → Fin 2) (n : ℕ) :
    itinOrbit lam x e (n + 1) = itinOrbit lam (f lam (e 0) x) (fun i => e (i + 1)) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [itinOrbit_succ, ih, itinOrbit_succ]

/-- The two descriptions of survival along a finite word agree. -/
lemma survivesUpTo_iff_bSurvives (lam : ℝ) :
    ∀ (m : ℕ) (x : ℝ) (e : ℕ → Fin 2),
      SurvivesUpTo lam x e m ↔ bSurvives lam x (List.ofFn (fun i : Fin m => e i)) := by
  intro m
  induction m with
  | zero => intro x e; simp [SurvivesUpTo, bSurvives]
  | succ m ih =>
      intro x e
      rw [List.ofFn_succ]
      show _ ↔ (BLegal lam (e 0) x ∧
        bSurvives lam (f lam (e 0) x) (List.ofFn (fun i : Fin m => e ((i : ℕ) + 1))))
      rw [← ih (f lam (e 0) x) (fun i => e (i + 1))]
      constructor
      · intro h
        refine ⟨by simpa using h 0 (by omega), ?_⟩
        intro n hn
        have := h (n + 1) (by omega)
        rwa [itinOrbit_shift] at this
      · rintro ⟨h0, hrest⟩ n hn
        match n with
        | 0 => simpa using h0
        | (n + 1) =>
            rw [itinOrbit_shift]
            exact hrest n (by omega)

/-- `K` counts exactly the length-`m` branch words along which `1/2` survives. -/
lemma K_eq_card_bSurvives (lam : ℝ) (m : ℕ) :
    K lam m = ((Finset.univ : Finset (Fin m → Fin 2)).filter
      (fun w => bSurvives lam (1/2) (List.ofFn w))).card := by
  rw [K]
  congr 1
  apply Finset.filter_congr
  intro w _
  rw [survivesUpTo_iff_bSurvives lam m (1/2) (extendWord w)]
  have : (fun i : Fin m => extendWord w (i : ℕ)) = w := by
    funext i
    rw [extendWord, dif_pos i.isLt]
  rw [this]

/-- The word of length `m` deviating from the spine at time `t`. -/
noncomputable def devWord (lam : ℝ) (x : ℝ) (m t : ℕ) : Fin m → Fin 2 :=
  fun i => devItin lam x t i

lemma extendWord_devWord (lam x : ℝ) {m t : ℕ} {n : ℕ} (hn : n < m) :
    extendWord (devWord lam x m t) n = devItin lam x t n := by
  rw [extendWord, dif_pos hn, devWord]

lemma itinOrbit_devWord (lam x : ℝ) {m t : ℕ} {n : ℕ} (hn : n ≤ m) :
    itinOrbit lam x (extendWord (devWord lam x m t)) n = devOrbit lam x t n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [itinOrbit_succ, ih (by omega), extendWord_devWord lam x (by omega : n < m),
        devOrbit_succ]

lemma devWord_survives (h1 : 1 < lam) (h2 : lam < 2) {x : ℝ} (hx : x ∈ Set.Ioo (0:ℝ) 1)
    {m t : ℕ} (ht : spine lam x t ∈ Window lam) :
    SurvivesUpTo lam x (extendWord (devWord lam x m t)) m := by
  intro n hn
  rw [extendWord_devWord lam x hn, itinOrbit_devWord lam x (le_of_lt hn)]
  exact (devOrbit_legal h1 h2 hx ht n).2

/-- Deviating at different visits gives different words. -/
lemma devWord_ne (lam x : ℝ) {m t t' : ℕ} (htm : t < m) (hlt : t < t') :
    devWord lam x m t ≠ devWord lam x m t' := by
  intro hcon
  have := congrFun hcon ⟨t, htm⟩
  rw [devWord, devWord] at this
  simp only at this
  rw [devItin_at lam x t, devItin_eq_of_lt lam x hlt] at this
  revert this
  generalize cb lam (spine lam x t) = a
  revert a
  decide

/-- **T12b (linear count).**  On a window `[lam₀, lam₁] ⊆ (1, φ)` with return
bound `B`, the number of length-`m` branch words along which `1/2` survives is at
least `m / (B+1)`. -/
theorem K_ge {B : ℕ} (hB1 : 1 ≤ B) (h0 : 1 < lam0) (h0l : lam0 ≤ lam)
    (hl1 : lam ≤ lam1) (hphi1 : lam1 ^ 2 < lam1 + 1)
    (hB : g lam1 < lam0 ^ (B - 1) * eta lam0 lam1) (m : ℕ) :
    m / (B + 1) ≤ K lam m := by
  have h1 : 1 < lam := lt_of_lt_of_le h0 h0l
  have h1' : 1 < lam1 := lt_of_lt_of_le h1 hl1
  have h2 : lam < 2 := lt_of_le_of_lt hl1 (lt_two_of_sq_lt h1' hphi1)
  have hhalf : (1/2 : ℝ) ∈ Window lam := half_mem_Window h1 h2
  have hhalfIoo : (1/2 : ℝ) ∈ Set.Ioo (0:ℝ) 1 := by norm_num
  set q := m / (B + 1) with hq
  have hqm : q * (B + 1) ≤ m := Nat.div_mul_le_self m (B + 1)
  -- each visit index `i < q` gives a time `< m`
  have hvisit_lt : ∀ i < q, visit lam (1/2) i < m := by
    intro i hi
    have hle := (visit_props hB1 h0 h0l hl1 hphi1 hB hhalf i).2
    have hmul : (i + 1) * (B + 1) ≤ q * (B + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have : i * (B + 1) + (B + 1) = (i + 1) * (B + 1) := by ring
    omega
  rw [K]
  refine le_trans (le_of_eq (Finset.card_range q).symm)
    (Finset.card_le_card_of_injOn (fun i => devWord lam (1/2) m (visit lam (1/2) i)) ?_ ?_)
  · intro i hi
    simp only [Finset.coe_range, Set.mem_Iio] at hi
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and]
    exact devWord_survives h1 h2 hhalfIoo
      (visit_props hB1 h0 h0l hl1 hphi1 hB hhalf i).1
  · intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    by_contra hne
    have hmono := visit_strictMono hB1 h0 h0l hl1 hphi1 hB hhalf
    rcases Nat.lt_or_ge i j with h | h
    · exact devWord_ne lam (1/2) (hvisit_lt i hi) (hmono h) hij
    · have hji : j < i := by omega
      exact devWord_ne lam (1/2) (hvisit_lt j hj) (hmono hji) hij.symm

end Branching
end KnotGame
