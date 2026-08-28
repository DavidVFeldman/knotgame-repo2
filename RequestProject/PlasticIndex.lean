import RequestProject.PlasticOrbit
import RequestProject.Suffix

/-!
# The plastic game as a finite automaton on `153` indices

`PlasticOrbit.lean` certifies that every knot of every reachable configuration
at the plastic number lies on the explicit `153`-point list `orbitList`, whose
entries are integer coordinate triples over `ℤ[ρ]`.  This file turns that list
into a *computable automaton*:

* `survB m t` / `actT m t` — survival and action on triples, decided by the
  certified integer enclosure `Mn`/`En` of `PlasticOrbit.lean`, and proved to
  agree with the real `survives`/`act` at `λ = ρ` (`survives_iff_survB`,
  `act_eq_actT`);
* the transition tables `tabL`, `tabM`, `tabR`, packed as single natural numbers
  with one byte per orbit index (`255` meaning "the knot dies"), checked against
  `survB`/`actT` by the kernel (`chk_tab`);
* `stepIdx`, `runIdx` — the game on *sorted lists of indices*, and the bridge
  `run_eq_cfgSet`, identifying `run ρ w` with the set of points indexed by
  `runIdx w`.

Two orbit points sit exactly on a threshold: `orbitList[58] = r/2` and
`orbitList[94] = 1 - r/2`.  Survival being strict, both die under `M`; the
comparisons are therefore three-valued (`<`, `>`, or an exact equality of
coordinate triples), which is what `decB` records.

This is the analogue at the plastic number of the integer model of
`RunRational.lean` at `λ = 3/2`; `PlasticConfig.lean` uses it to enumerate the
reachable configurations.
-/

namespace KnotGame
namespace Plastic

set_option maxRecDepth 100000

/-! ## Sign tests on triples -/

/-- The difference of two triples. -/
def tsub (t u : Tri) : Tri := (t.1 - u.1, t.2.1 - u.2.1, t.2.2 - u.2.2)

lemma tval_tsub (t u : Tri) : tval (tsub t u) = tval t - tval u := by
  simp only [tval, traw, tsub]
  push_cast
  ring

/-- The certified test `tval t > 0`. -/
def posB (t : Tri) : Bool := decide (0 < Mn t - En t)

/-- The certified test `tval t < 0`. -/
def negB (t : Tri) : Bool := decide (Mn t + En t < 0)

lemma tval_pos_of_posB {t : Tri} (h : posB t = true) : 0 < tval t :=
  tval_pos_of (of_decide_eq_true h)

lemma tval_neg_of_negB {t : Tri} (h : negB t = true) : tval t < 0 := by
  have h' : Mn t + En t < 0 := of_decide_eq_true h
  have h1 := le_Mn_add_En t
  have h2 : ((Mn t + En t : ℤ) : ℝ) < 0 := by exact_mod_cast h'
  have h3 : (1000000000000000000 : ℝ) * traw t < 0 := lt_of_le_of_lt h1 h2
  simp only [tval]
  linarith

/-- The certified test `tval t < tval u`. -/
def ltB (t u : Tri) : Bool := negB (tsub t u)

/-- The certified test `tval u < tval t`. -/
def gtB (t u : Tri) : Bool := posB (tsub t u)

lemma tval_lt_of_ltB {t u : Tri} (h : ltB t u = true) : tval t < tval u := by
  have := tval_neg_of_negB h
  rw [tval_tsub] at this
  linarith

lemma tval_gt_of_gtB {t u : Tri} (h : gtB t u = true) : tval u < tval t := by
  have := tval_pos_of_posB h
  rw [tval_tsub] at this
  linarith

/-- The comparison of `t` against `u` is settled: strictly below, strictly
above, or the same triple. -/
def decB (t u : Tri) : Bool := ltB t u || gtB t u || decide (t = u)

lemma le_of_decB_of_not_gtB {t u : Tri} (hd : decB t u = true) (h : gtB t u = false) :
    tval t ≤ tval u := by
  simp only [decB, Bool.or_eq_true, decide_eq_true_eq] at hd
  rcases hd with (h1 | h1) | h1
  · exact le_of_lt (tval_lt_of_ltB h1)
  · exact absurd h1 (by simp [h])
  · exact le_of_eq (by rw [h1])

lemma ge_of_decB_of_not_ltB {t u : Tri} (hd : decB t u = true) (h : ltB t u = false) :
    tval u ≤ tval t := by
  simp only [decB, Bool.or_eq_true, decide_eq_true_eq] at hd
  rcases hd with (h1 | h1) | h1
  · exact absurd h1 (by simp [h])
  · exact le_of_lt (tval_gt_of_gtB h1)
  · exact le_of_eq (by rw [h1])

/-! ## The thresholds of the three moves, as triples -/

lemma rho_ne_zero : rho ≠ 0 := ne_of_gt (lt_trans zero_lt_one one_lt_rho)

lemma r_rho_eq : r rho = rho ^ 2 - 1 := by
  have hmul : rho * (rho ^ 2 - 1) = 1 := by nlinarith [rho_cube]
  rw [r, inv_eq_of_mul_eq_one_right hmul]

lemma g_rho_eq : g rho = 2 - rho ^ 2 := by
  rw [g, r_rho_eq]; ring

/-- The triple of `g = 1 - r`. -/
def gTri : Tri := (4, 0, -2)

/-- The triple of `r`. -/
def rTri : Tri := (-2, 0, 2)

/-- The triple of `r/2`. -/
def rHalfTri : Tri := (-1, 0, 1)

/-- The triple of `1 - r/2`. -/
def oneSubRHalfTri : Tri := (3, 0, -1)

lemma tval_gTri : tval gTri = g rho := by
  simp only [tval, traw, gTri, g_rho_eq]
  push_cast
  ring

lemma tval_rTri : tval rTri = r rho := by
  simp only [tval, traw, rTri, r_rho_eq]
  push_cast
  ring

lemma tval_rHalfTri : tval rHalfTri = r rho / 2 := by
  simp only [tval, traw, rHalfTri, r_rho_eq]
  push_cast
  ring

lemma tval_oneSubRHalfTri : tval oneSubRHalfTri = 1 - r rho / 2 := by
  simp only [tval, traw, oneSubRHalfTri, r_rho_eq]
  push_cast
  ring

/-! ## Survival and action on triples -/

/-- Survival of a knot at `tval t` under the move `m`, decided on integers. -/
def survB : Move → Tri → Bool
  | Move.L, t => gtB t gTri
  | Move.M, t => ltB t rHalfTri || gtB t oneSubRHalfTri
  | Move.R, t => ltB t rTri

/-- The image of a surviving knot at `tval t` under the move `m`, on triples. -/
def actT : Move → Tri → Tri
  | Move.L, t => tf1 t
  | Move.M, t => if ltB t rHalfTri then tf0 t else tf1 t
  | Move.R, t => tf0 t

/-- All four comparisons needed by the three moves are settled at `t`. -/
def decT (t : Tri) : Bool :=
  decB t gTri && decB t rTri && decB t rHalfTri && decB t oneSubRHalfTri

/-- Every orbit point is comparable with each of the four thresholds. -/
theorem chk_dec : ∀ t ∈ orbitList, decT t = true := by decide

lemma decT_g {t : Tri} (h : decT t = true) : decB t gTri = true := by
  simp only [decT, Bool.and_eq_true] at h; exact h.1.1.1

lemma decT_r {t : Tri} (h : decT t = true) : decB t rTri = true := by
  simp only [decT, Bool.and_eq_true] at h; exact h.1.1.2

lemma decT_rHalf {t : Tri} (h : decT t = true) : decB t rHalfTri = true := by
  simp only [decT, Bool.and_eq_true] at h; exact h.1.2

lemma decT_oneSubRHalf {t : Tri} (h : decT t = true) : decB t oneSubRHalfTri = true := by
  simp only [decT, Bool.and_eq_true] at h; exact h.2

lemma survives_of_survB {m : Move} {t : Tri} (h : survB m t = true) :
    survives rho m (tval t) := by
  cases m
  · have := tval_gt_of_gtB (t := t) (u := gTri) h
    rw [tval_gTri] at this
    exact this
  · rcases Bool.or_eq_true_iff.1 h with h1 | h1
    · exact Or.inl (by have := tval_lt_of_ltB h1; rwa [tval_rHalfTri] at this)
    · exact Or.inr (by have := tval_gt_of_gtB h1; rwa [tval_oneSubRHalfTri] at this)
  · have := tval_lt_of_ltB (t := t) (u := rTri) h
    rwa [tval_rTri] at this

lemma not_survives_of_survB_false {m : Move} {t : Tri} (hd : decT t = true)
    (h : survB m t = false) : ¬ survives rho m (tval t) := by
  cases m
  · have hle := le_of_decB_of_not_gtB (decT_g hd) h
    rw [tval_gTri] at hle
    simpa using not_lt.mpr hle
  · simp only [survB, Bool.or_eq_false_iff] at h
    have h1 := ge_of_decB_of_not_ltB (decT_rHalf hd) h.1
    have h2 := le_of_decB_of_not_gtB (decT_oneSubRHalf hd) h.2
    rw [tval_rHalfTri] at h1
    rw [tval_oneSubRHalfTri] at h2
    simp only [survives_M, not_or, not_lt]
    exact ⟨h1, h2⟩
  · have hge := ge_of_decB_of_not_ltB (decT_r hd) h
    rw [tval_rTri] at hge
    simpa using not_lt.mpr hge

lemma survives_iff_survB {m : Move} {t : Tri} (hd : decT t = true) :
    survives rho m (tval t) ↔ survB m t = true := by
  constructor
  · intro hs
    by_contra hc
    exact not_survives_of_survB_false hd (by simpa using hc) hs
  · exact survives_of_survB

lemma act_eq_actT {m : Move} {t : Tri} (h : survB m t = true) :
    act rho m (tval t) = tval (actT m t) := by
  cases m
  · rw [act_L, actT, tval_tf1]
  · by_cases hlt : ltB t rHalfTri = true
    · have hx : tval t < r rho / 2 := by
        have := tval_lt_of_ltB hlt; rwa [tval_rHalfTri] at this
      rw [act_M_of_lt _ _ hx, actT, if_pos hlt, tval_tf0]
    · have hgt : 1 - r rho / 2 < tval t := by
        have h' : gtB t oneSubRHalfTri = true := by
          rcases Bool.or_eq_true_iff.1 h with h1 | h1
          · exact absurd h1 hlt
          · exact h1
        have := tval_gt_of_gtB h'; rwa [tval_oneSubRHalfTri] at this
      have hr1 : r rho < 1 := r_lt_one rho one_lt_rho
      have hx : ¬ tval t < r rho / 2 := by
        intro hc
        linarith
      rw [act_M_of_gt _ _ hx, actT, if_neg hlt, tval_tf1]
  · rw [act_R, actT, tval_tf0]

/-! ## The packed transition tables -/

/-- The `i`-th orbit point (the junk value `(0,0,0)` outside the range). -/
def oget (i : ℕ) : Tri := orbitList.getD i (0, 0, 0)

/-- The index of `1/2` in `orbitList`. -/
def halfIdx : ℕ := 76

/-- One byte of a packed transition table; `255` means "the knot dies". -/
def tget (T i : ℕ) : ℕ := (T >>> (8 * i)) % 256

/-- The transition table of the move `L`, one byte per orbit index. -/
def tabL : ℕ := 171056735807690813158204043027096063117823792939589782407190498882094804196684560109697704812219969809878965280427119476230116787853925094057711547396344022237304133198271482418090456866214403214303098389081284245680005335449185070084434135948613816110420505742780952882874500925302037696564924024950129259355089229527500094027877515435717160957588186308421626974175231

/-- The transition table of the move `M`. -/
def tabM : ℕ := 171056735807690813158204043027096063117823792939589782407190498882094804196684560109697704812219969809878965280427119476230116787853925094061968791442788097996213042809060419290900012167758304409433320024857898999623341739072374766867490930247231286174404088190874128191572005682919522501675980705118723683600313451217024624203679068632389131358086327993137409535705601

/-- The transition table of the move `R`. -/
def tabR : ℕ := 288878149031346317441449898160257412877284850718137687733941608447907569136952074473685387937855203874463210323106590926941063634499150493722986231349017905573328364153930698346593479896178159433542037095240295292727168663669627640369498979092486053592098226686136996275178217074670687912311030344412589571798672530070215681851737034958949051279163572853132067179004417

/-- The packed table of a move. -/
def tabOf : Move → ℕ
  | Move.L => tabL
  | Move.M => tabM
  | Move.R => tabR

/-- The table entry at `i` is correct: the byte is `255` exactly when the point
dies, and otherwise it indexes the image point. -/
def tabOK (m : Move) (i : ℕ) : Bool :=
  let t := oget i
  let v := tget (tabOf m) i
  if survB m t then decide (v < 153) && decide (oget v = actT m t) else decide (v = 255)

/-- **The tables are correct**, checked by the kernel on all `153` indices. -/
theorem chk_tab : ((List.range 153).all
    (fun i => tabOK Move.L i && tabOK Move.M i && tabOK Move.R i)) = true := by decide

lemma tabOK_of_lt {m : Move} {i : ℕ} (hi : i < 153) : tabOK m i = true := by
  have h := List.all_eq_true.1 chk_tab i (List.mem_range.2 hi)
  simp only [Bool.and_eq_true] at h
  cases m
  · exact h.1.1
  · exact h.1.2
  · exact h.2

lemma oget_mem {i : ℕ} (hi : i < 153) : oget i ∈ orbitList := by
  have hlen : orbitList.length = 153 := orbitList_length
  have hi' : i < orbitList.length := by omega
  rw [oget, List.getD_eq_getElem _ _ hi']
  exact List.getElem_mem hi'

lemma decT_oget {i : ℕ} (hi : i < 153) : decT (oget i) = true :=
  chk_dec _ (oget_mem hi)

lemma tget_eq_255_iff {m : Move} {i : ℕ} (hi : i < 153) :
    tget (tabOf m) i = 255 ↔ ¬ survives rho m (tval (oget i)) := by
  have h := tabOK_of_lt (m := m) hi
  simp only [tabOK] at h
  by_cases hs : survB m (oget i) = true
  · rw [if_pos hs] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    constructor
    · intro hc; omega
    · intro hc; exact absurd (survives_of_survB hs) hc
  · have hs' : survB m (oget i) = false := by simpa using hs
    rw [if_neg hs] at h
    simp only [decide_eq_true_eq] at h
    exact ⟨fun _ => not_survives_of_survB_false (decT_oget hi) hs', fun _ => h⟩

lemma tget_lt {m : Move} {i : ℕ} (hi : i < 153) (h255 : tget (tabOf m) i ≠ 255) :
    tget (tabOf m) i < 153 := by
  have h := tabOK_of_lt (m := m) hi
  simp only [tabOK] at h
  by_cases hs : survB m (oget i) = true
  · rw [if_pos hs] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1
  · rw [if_neg hs] at h
    simp only [decide_eq_true_eq] at h
    exact absurd h h255

lemma oget_tget {m : Move} {i : ℕ} (hi : i < 153) (h255 : tget (tabOf m) i ≠ 255) :
    tval (oget (tget (tabOf m) i)) = act rho m (tval (oget i)) := by
  have h := tabOK_of_lt (m := m) hi
  simp only [tabOK] at h
  by_cases hs : survB m (oget i) = true
  · rw [if_pos hs] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.2, ← act_eq_actT hs]
  · rw [if_neg hs] at h
    simp only [decide_eq_true_eq] at h
    exact absurd h h255

lemma oget_halfIdx : oget halfIdx = (1, 0, 0) := by decide

lemma tval_oget_halfIdx : tval (oget halfIdx) = 1/2 := by
  rw [oget_halfIdx]
  simp [tval, traw]

/-! ## Configurations as sorted lists of indices -/

/-- Insertion into a strictly increasing list of indices. -/
def insNat (x : ℕ) : List ℕ → List ℕ
  | [] => [x]
  | y :: c => if x = y then y :: c else if x < y then x :: y :: c else y :: insNat x c

lemma mem_insNat {x j : ℕ} : ∀ c : List ℕ, j ∈ insNat x c ↔ j = x ∨ j ∈ c
  | [] => by simp [insNat]
  | y :: c => by
      simp only [insNat]
      split
      · next hxy =>
          subst hxy
          constructor
          · intro h; exact Or.inr h
          · rintro (rfl | h)
            · exact List.mem_cons_self ..
            · exact h
      · split
        · simp only [List.mem_cons]
        · rw [List.mem_cons, mem_insNat c, List.mem_cons]
          tauto

lemma pairwise_insNat {x : ℕ} : ∀ {c : List ℕ}, List.Pairwise (· < ·) c →
    List.Pairwise (· < ·) (insNat x c)
  | [], _ => by simp [insNat]
  | y :: c, h => by
      obtain ⟨hy, hc⟩ := List.pairwise_cons.1 h
      simp only [insNat]
      split
      · exact h
      · split
        · next hne hlt =>
            refine List.pairwise_cons.2 ⟨?_, h⟩
            intro b hb
            rcases List.mem_cons.1 hb with rfl | hb'
            · exact hlt
            · exact lt_trans hlt (hy b hb')
        · next hne hnlt =>
            have hyx : y < x := by omega
            refine List.pairwise_cons.2 ⟨?_, pairwise_insNat hc⟩
            intro b hb
            rcases (mem_insNat c).1 hb with rfl | hb'
            · exact hyx
            · exact hy b hb'

/-- One move on a configuration of indices. -/
def stepIdx (m : Move) (c : List ℕ) : List ℕ :=
  let c' := c.foldr (fun i acc =>
      let v := tget (tabOf m) i
      if v = 255 then acc else insNat v acc) []
  if m = Move.M then insNat halfIdx c' else c'

lemma mem_stepAux {m : Move} {j : ℕ} : ∀ c : List ℕ,
    (j ∈ c.foldr (fun i acc =>
        let v := tget (tabOf m) i
        if v = 255 then acc else insNat v acc) []) ↔
      ∃ i ∈ c, tget (tabOf m) i ≠ 255 ∧ j = tget (tabOf m) i
  | [] => by simp
  | i :: c => by
      simp only [List.foldr_cons]
      by_cases h : tget (tabOf m) i = 255
      · simp only [h, if_pos]
        rw [mem_stepAux c]
        constructor
        · rintro ⟨k, hk, h1, h2⟩; exact ⟨k, List.mem_cons_of_mem _ hk, h1, h2⟩
        · rintro ⟨k, hk, h1, h2⟩
          rcases List.mem_cons.1 hk with rfl | hk'
          · exact absurd h h1
          · exact ⟨k, hk', h1, h2⟩
      · simp only [h, if_false]
        rw [mem_insNat, mem_stepAux c]
        constructor
        · rintro (rfl | ⟨k, hk, h1, h2⟩)
          · exact ⟨i, List.mem_cons_self .., h, rfl⟩
          · exact ⟨k, List.mem_cons_of_mem _ hk, h1, h2⟩
        · rintro ⟨k, hk, h1, h2⟩
          rcases List.mem_cons.1 hk with rfl | hk'
          · exact Or.inl h2
          · exact Or.inr ⟨k, hk', h1, h2⟩

lemma pairwise_stepAux {m : Move} : ∀ c : List ℕ,
    List.Pairwise (· < ·) (c.foldr (fun i acc =>
      let v := tget (tabOf m) i
      if v = 255 then acc else insNat v acc) [])
  | [] => by simp
  | i :: c => by
      simp only [List.foldr_cons]
      by_cases h : tget (tabOf m) i = 255
      · simpa [h] using pairwise_stepAux (m := m) c
      · simpa [h] using pairwise_insNat (x := tget (tabOf m) i) (pairwise_stepAux (m := m) c)

lemma mem_stepIdx {m : Move} {c : List ℕ} {j : ℕ} :
    j ∈ stepIdx m c ↔
      (∃ i ∈ c, tget (tabOf m) i ≠ 255 ∧ j = tget (tabOf m) i) ∨
        (m = Move.M ∧ j = halfIdx) := by
  simp only [stepIdx]
  cases m
  · rw [if_neg (by simp)]
    simp only [reduceCtorEq, false_and, or_false]
    exact mem_stepAux (m := Move.L) c
  · rw [if_pos rfl, mem_insNat, mem_stepAux (m := Move.M) c]
    simp only [true_and]
    exact or_comm
  · rw [if_neg (by simp)]
    simp only [reduceCtorEq, false_and, or_false]
    exact mem_stepAux (m := Move.R) c

lemma pairwise_stepIdx {m : Move} (c : List ℕ) : List.Pairwise (· < ·) (stepIdx m c) := by
  simp only [stepIdx]
  cases m
  · rw [if_neg (by simp)]; exact pairwise_stepAux (m := Move.L) c
  · rw [if_pos rfl]; exact pairwise_insNat (x := halfIdx) (pairwise_stepAux (m := Move.M) c)
  · rw [if_neg (by simp)]; exact pairwise_stepAux (m := Move.R) c

lemma stepIdx_lt {m : Move} {c : List ℕ} (hc : ∀ i ∈ c, i < 153) :
    ∀ j ∈ stepIdx m c, j < 153 := by
  intro j hj
  rcases mem_stepIdx.1 hj with ⟨i, hi, h255, rfl⟩ | ⟨-, rfl⟩
  · exact tget_lt (hc i hi) h255
  · norm_num [halfIdx]

/-! ## The bridge to the real game -/

open Classical in
/-- The real configuration indexed by a list of orbit indices. -/
noncomputable def cfgSet (c : List ℕ) : Finset ℝ := (c.map (fun i => tval (oget i))).toFinset

lemma mem_cfgSet {c : List ℕ} {x : ℝ} : x ∈ cfgSet c ↔ ∃ i ∈ c, tval (oget i) = x := by
  classical
  simp [cfgSet, List.mem_toFinset]

/-- **The bridge, one step.** -/
theorem step_cfgSet (m : Move) {c : List ℕ} (hc : ∀ i ∈ c, i < 153) :
    step rho m (cfgSet c) = cfgSet (stepIdx m c) := by
  classical
  ext x
  rw [mem_step, mem_cfgSet]
  constructor
  · rintro (⟨y, hy, hsurv, hact⟩ | ⟨hm, rfl⟩)
    · rw [mem_cfgSet] at hy
      obtain ⟨i, hi, rfl⟩ := hy
      have hi153 := hc i hi
      have h255 : tget (tabOf m) i ≠ 255 := fun hc' =>
        ((tget_eq_255_iff hi153).1 hc') hsurv
      exact ⟨tget (tabOf m) i, mem_stepIdx.2 (Or.inl ⟨i, hi, h255, rfl⟩),
        by rw [oget_tget hi153 h255, hact]⟩
    · exact ⟨halfIdx, mem_stepIdx.2 (Or.inr ⟨hm, rfl⟩), tval_oget_halfIdx⟩
  · rintro ⟨j, hj, rfl⟩
    rcases mem_stepIdx.1 hj with ⟨i, hi, h255, rfl⟩ | ⟨hm, rfl⟩
    · have hi153 := hc i hi
      refine Or.inl ⟨tval (oget i), mem_cfgSet.2 ⟨i, hi, rfl⟩, ?_, (oget_tget hi153 h255).symm⟩
      by_contra hcon
      exact h255 ((tget_eq_255_iff hi153).2 hcon)
    · exact Or.inr ⟨hm, tval_oget_halfIdx⟩

/-- The configuration of indices after a word. -/
def runIdx (w : List Move) : List ℕ := w.foldl (fun c m => stepIdx m c) []

lemma runIdx_spec : ∀ (w : List Move) (c : List ℕ), (∀ i ∈ c, i < 153) →
    List.Pairwise (· < ·) c →
    runFrom rho (cfgSet c) w = cfgSet (w.foldl (fun c m => stepIdx m c) c) ∧
      (∀ i ∈ w.foldl (fun c m => stepIdx m c) c, i < 153) ∧
      List.Pairwise (· < ·) (w.foldl (fun c m => stepIdx m c) c)
  | [], c, hc, hp => ⟨rfl, hc, hp⟩
  | m :: w, c, hc, _ => by
      have h2 := runIdx_spec w (stepIdx m c) (stepIdx_lt hc) (pairwise_stepIdx c)
      refine ⟨?_, h2.2.1, h2.2.2⟩
      rw [runFrom_cons, step_cfgSet m hc, h2.1]
      rfl

/-- **The bridge.**  At the plastic number the configuration after `w` is the
set of orbit points indexed by `runIdx w`. -/
theorem run_eq_cfgSet (w : List Move) : run rho w = cfgSet (runIdx w) := by
  have h := (runIdx_spec w [] (by simp) (by simp)).1
  have hnil : cfgSet [] = (∅ : Finset ℝ) := by
    classical
    simp [cfgSet]
  rw [run, ← hnil, h, runIdx]

lemma runIdx_lt (w : List Move) : ∀ i ∈ runIdx w, i < 153 :=
  (runIdx_spec w [] (by simp) (by simp)).2.1

lemma runIdx_pairwise (w : List Move) : List.Pairwise (· < ·) (runIdx w) :=
  (runIdx_spec w [] (by simp) (by simp)).2.2

/-! ## Counting -/

/-- Distinct orbit indices carry distinct points. -/
lemma tval_oget_inj {i j : ℕ} (hi : i < 153) (hj : j < 153)
    (h : tval (oget i) = tval (oget j)) : i = j := by
  by_contra hne
  have hlen : orbitList.length = 153 := orbitList_length
  have hi' : i < orbitList.length := by omega
  have hj' : j < orbitList.length := by omega
  have hpw := orbitList_pairwise
  rw [List.pairwise_iff_getElem] at hpw
  have hoi : oget i = orbitList[i] := by rw [oget, List.getD_eq_getElem _ _ hi']
  have hoj : oget j = orbitList[j] := by rw [oget, List.getD_eq_getElem _ _ hj']
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hd := hpw i j hi' hj' hlt
    rw [← hoi, ← hoj, h, sub_self, abs_zero] at hd
    linarith [deltaRho_pos]
  · have hd := hpw j i hj' hi' hlt
    rw [← hoi, ← hoj, h, sub_self, abs_zero] at hd
    linarith [deltaRho_pos]

lemma card_cfgSet_eq {c : List ℕ} (hc : ∀ i ∈ c, i < 153)
    (hp : List.Pairwise (· < ·) c) : (cfgSet c).card = c.length := by
  classical
  have hnd : (c.map (fun i => tval (oget i))).Nodup := by
    refine List.Nodup.map_on ?_ (hp.imp (fun {a b} h => ne_of_lt h))
    intro a ha b hb hab
    exact tval_oget_inj (hc a ha) (hc b hb) hab
  rw [cfgSet, List.toFinset_card_of_nodup hnd, List.length_map]

/-- The number of knots after `w` is the length of the index configuration. -/
theorem card_run_eq_length (w : List Move) : (run rho w).card = (runIdx w).length := by
  rw [run_eq_cfgSet, card_cfgSet_eq (runIdx_lt w) (runIdx_pairwise w)]

end Plastic
end KnotGame
