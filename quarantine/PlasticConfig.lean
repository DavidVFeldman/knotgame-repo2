import RequestProject.PlasticCert

/-!
# Proposition 9: the game at the plastic number

`PlasticIndex.lean` identifies the game at the plastic number `ρ` with a game
on sorted lists of indices into the `153`-point orbit, and `PlasticCert.lean`
supplies a tree `V` of such index configurations, each node carrying a depth
tag and a recorded parent.  Here we check by kernel computation that

* the empty configuration lies in `V` with tag `0` (`nil_mem_V`);
* `V` is closed under the three moves, the tags growing by at most one; every
  member of `V` has at most seven indices, and a member with `k` indices has
  tag at least `1, 3, 5, 7, 12, 17, 28` for `k = 1, …, 7`; every member is
  obtained from its recorded parent, which has a smaller tag (`chkV`);
* `V` is correctly keyed and ordered (`okV`) and has `25525` nodes (`sizeV`).

The closure gives the upper bound `N ρ ≤ 7` and the lower bounds on the record
depths; the recorded parents show conversely that every member of `V` is
reachable, so the members of `V` are exactly the reachable configurations and
there are `25525` of them.  Explicit record words give the matching upper
bounds on the depths.  Altogether:

* `sup_N_rho : IsGreatest (Set.range (N ρ)) 7`;
* `d ρ k = 1, 3, 5, 7, 12, 17, 28` for `k = 1, …, 7`
  (`d_rho_one`, …, `d_rho_seven`);
* `card_reachable_configs`: there are exactly `25525` reachable configurations.
-/

namespace KnotGame
namespace Plastic

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! ## The kernel checks -/

/-- `c` occurs in the certificate with a tag at most `n`. -/
def memVd (c : List ℕ) (n : ℕ) : Bool := V.findLe (encCfg c) c n

/-- The move coded by a natural number. -/
def moveOf : ℕ → Move
  | 0 => Move.L
  | 1 => Move.M
  | _ => Move.R

/-- The three successors of `c` occur with tags one larger. -/
def chkStep (c : List ℕ) (d : ℕ) : Bool :=
  memVd (stepIdx Move.L c) (d + 1) && memVd (stepIdx Move.M c) (d + 1) &&
    memVd (stepIdx Move.R c) (d + 1)

/-- `c` has at most seven knots, and its tag is at least the record depth of
its size. -/
def chkSize (c : List ℕ) (d : ℕ) : Bool :=
  decide (c.length ≤ 7) &&
    decide (1 ≤ c.length → 1 ≤ d) && decide (2 ≤ c.length → 3 ≤ d) &&
    decide (3 ≤ c.length → 5 ≤ d) && decide (4 ≤ c.length → 7 ≤ d) &&
    decide (5 ≤ c.length → 12 ≤ d) && decide (6 ≤ c.length → 17 ≤ d) &&
    decide (7 ≤ c.length → 28 ≤ d)

/-- `c` is the empty configuration, or is obtained by the recorded move from
the recorded parent, which occurs with a smaller tag. -/
def chkReach (c : List ℕ) (d pm : ℕ) (pc : List ℕ) : Bool :=
  match d with
  | 0 => decide (c = [])
  | d' + 1 => memVd pc d' && decide (stepIdx (moveOf pm) pc = c)

/-- The property checked at every node of the certificate. -/
def chkBody (c : List ℕ) (d pm : ℕ) (pc : List ℕ) : Bool :=
  chkStep c d && chkSize c d && chkReach c d pm pc

theorem chkV : V.all chkBody = true := by decide +kernel

theorem nil_mem_V : memVd [] 0 = true := by decide +kernel

theorem okV : V.ok none none = true := by decide +kernel

theorem sizeV : V.size = 25525 := by decide +kernel

/-! ## Reading off the checks -/

lemma chkStep_facts {c : List ℕ} {d : ℕ} (h : chkStep c d = true) (m : Move) :
    memVd (stepIdx m c) (d + 1) = true := by
  simp only [chkStep, Bool.and_eq_true] at h
  cases m
  · exact h.1.1
  · exact h.1.2
  · exact h.2

lemma chkSize_facts {c : List ℕ} {d : ℕ} (h : chkSize c d = true) :
    c.length ≤ 7 ∧ (1 ≤ c.length → 1 ≤ d) ∧ (2 ≤ c.length → 3 ≤ d) ∧
      (3 ≤ c.length → 5 ≤ d) ∧ (4 ≤ c.length → 7 ≤ d) ∧ (5 ≤ c.length → 12 ≤ d) ∧
      (6 ≤ c.length → 17 ≤ d) ∧ (7 ≤ c.length → 28 ≤ d) := by
  simp only [chkSize, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩

lemma chkBody_facts {c : List ℕ} {d pm : ℕ} {pc : List ℕ} (h : chkBody c d pm pc = true) :
    chkStep c d = true ∧ chkSize c d = true ∧ chkReach c d pm pc = true := by
  simp only [chkBody, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- What a successful lookup yields. -/
lemma facts_of_memVd {c : List ℕ} {n : ℕ} (h : memVd c n = true) :
    ∃ d ≤ n, ∃ pm pc, chkStep c d = true ∧ chkSize c d = true ∧
      chkReach c d pm pc = true := by
  obtain ⟨d, hd, pm, pc, hp⟩ := Tbl.all_of_findLe V chkV h
  exact ⟨d, hd, pm, pc, chkBody_facts hp⟩

/-! ## Every reachable configuration is certified -/

lemma memVd_step {m : Move} {c : List ℕ} {n : ℕ} (h : memVd c n = true) :
    memVd (stepIdx m c) (n + 1) = true := by
  obtain ⟨d, hd, -, -, hs, -, -⟩ := facts_of_memVd h
  exact Tbl.findLe_mono V (Nat.succ_le_succ hd) (chkStep_facts hs m)

lemma memVd_foldl : ∀ (w : List Move) (c : List ℕ) (n : ℕ), memVd c n = true →
    memVd (w.foldl (fun c m => stepIdx m c) c) (n + w.length) = true
  | [], c, n, h => by simpa using h
  | m :: w, c, n, h => by
      have h1 := memVd_foldl w (stepIdx m c) (n + 1) (memVd_step h)
      have hlen : n + 1 + w.length = n + (m :: w).length := by
        simp only [List.length_cons]; omega
      rwa [hlen] at h1

/-- Every configuration reachable in `|w|` moves is certified with a tag at
most `|w|`. -/
theorem memVd_runIdx (w : List Move) : memVd (runIdx w) w.length = true := by
  have := memVd_foldl w [] 0 nil_mem_V
  simpa [runIdx] using this

/-- The checked facts, transported to an arbitrary run. -/
theorem run_facts (w : List Move) :
    ∃ d ≤ w.length, chkSize (runIdx w) d = true := by
  obtain ⟨d, hd, -, -, -, hs, -⟩ := facts_of_memVd (memVd_runIdx w)
  exact ⟨d, hd, hs⟩

/-! ## The upper bound -/

/-- **Proposition 9, upper bound.**  At the plastic number every run leaves at
most seven knots. -/
theorem card_run_rho_le_seven (w : List Move) : (run rho w).card ≤ 7 := by
  rw [card_run_eq_length]
  obtain ⟨d, -, hs⟩ := run_facts w
  exact (chkSize_facts hs).1

/-- At the plastic number `N ρ n ≤ 7` for every `n`. -/
theorem N_rho_le_seven (n : ℕ) : N rho n ≤ 7 := by
  refine Finset.sup_le ?_
  intro v _
  exact card_run_rho_le_seven _

/-! ## Passing between words and `N` -/

lemma le_N_of_word_rho {k : ℕ} (v : Fin k → Move) : (run rho (List.ofFn v)).card ≤ N rho k :=
  Finset.le_sup (f := fun u : Fin k → Move => (run rho (List.ofFn u)).card)
    (Finset.mem_univ v)

/-- A word realizes its own knot count in `N`. -/
lemma length_runIdx_le_N (w : List Move) : (runIdx w).length ≤ N rho w.length := by
  have h := le_N_of_word_rho (k := w.length) (fun i : Fin w.length => w[(i : ℕ)])
  rwa [List.ofFn_getElem, card_run_eq_length] at h

/-- Conversely, `N ρ n` is realized by some word of length `n`. -/
lemma exists_word_rho (n : ℕ) : ∃ w : List Move, w.length = n ∧ N rho n = (runIdx w).length := by
  obtain ⟨v, -, hv⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin n → Move))
    ⟨fun _ => Move.M, Finset.mem_univ _⟩
    (fun u : Fin n → Move => (run rho (List.ofFn u)).card)
  exact ⟨List.ofFn v, List.length_ofFn, by rw [N, hv, card_run_eq_length]⟩

/-! ## The record depths -/

/-- The record depth is at most the length of any word attaining `k` knots. -/
lemma d_rho_le_of_word {k : ℕ} (w : List Move) (hk : k ≤ (runIdx w).length) :
    d rho k ≤ w.length :=
  Nat.sInf_le (Set.mem_setOf.2 (le_trans hk (length_runIdx_le_N w)))

/-- A lower bound on a record depth, from a lower bound on the length of every
word attaining `k` knots. -/
lemma le_d_rho {k n : ℕ} (hne : ∃ m, k ≤ N rho m)
    (h : ∀ w : List Move, k ≤ (runIdx w).length → n ≤ w.length) : n ≤ d rho k := by
  refine le_csInf hne ?_
  intro m hm
  obtain ⟨w, hlen, hw⟩ := exists_word_rho m
  have hk : k ≤ (runIdx w).length := by rw [← hw]; exact hm
  exact hlen ▸ h w hk

open Move in
/-- The shortest word producing one knot. -/
def rec1 : List Move := [M]

open Move in
/-- The shortest word producing two knots. -/
def rec2 : List Move := [M, L, M]

open Move in
/-- The shortest word producing three knots. -/
def rec3 : List Move := [M, L, M, L, M]

open Move in
/-- The shortest word producing four knots. -/
def rec4 : List Move := [M, L, M, L, M, L, M]

open Move in
/-- The shortest word producing five knots. -/
def rec5 : List Move := [M, L, L, M, R, M, R, R, L, M, L, M]

open Move in
/-- The shortest word producing six knots. -/
def rec6 : List Move := [M, L, M, L, M, R, L, R, R, L, M, L, M, L, M, L, M]

open Move in
/-- The shortest word producing seven knots. -/
def rec7 : List Move :=
  [M, L, M, R, L, R, L, L, R, L, R, M, L, M, R, M, L, R, L, R, L, M, R, M, R, M, R, M]

lemma runIdx_rec1 : (runIdx rec1).length = 1 := by decide +kernel
lemma runIdx_rec2 : (runIdx rec2).length = 2 := by decide +kernel
lemma runIdx_rec3 : (runIdx rec3).length = 3 := by decide +kernel
lemma runIdx_rec4 : (runIdx rec4).length = 4 := by decide +kernel
lemma runIdx_rec5 : (runIdx rec5).length = 5 := by decide +kernel
lemma runIdx_rec6 : (runIdx rec6).length = 6 := by decide +kernel
lemma runIdx_rec7 : (runIdx rec7).length = 7 := by decide +kernel

lemma exists_N_ge (k : ℕ) (w : List Move) (hk : k ≤ (runIdx w).length) : ∃ m, k ≤ N rho m :=
  ⟨w.length, le_trans hk (length_runIdx_le_N w)⟩

/-- `d ρ 1 = 1`. -/
theorem d_rho_one : d rho 1 = 1 := by
  refine le_antisymm ?_ (le_d_rho (exists_N_ge 1 rec1 (by rw [runIdx_rec1])) ?_)
  · simpa [rec1] using d_rho_le_of_word rec1 (by rw [runIdx_rec1])
  · intro w hw
    obtain ⟨dd, hd, hs⟩ := run_facts w
    exact le_trans ((chkSize_facts hs).2.1 hw) hd

/-- `d ρ 2 = 3`. -/
theorem d_rho_two : d rho 2 = 3 := by
  refine le_antisymm ?_ (le_d_rho (exists_N_ge 2 rec2 (by rw [runIdx_rec2])) ?_)
  · simpa [rec2] using d_rho_le_of_word rec2 (by rw [runIdx_rec2])
  · intro w hw
    obtain ⟨dd, hd, hs⟩ := run_facts w
    exact le_trans ((chkSize_facts hs).2.2.1 hw) hd

/-- `d ρ 3 = 5`. -/
theorem d_rho_three : d rho 3 = 5 := by
  refine le_antisymm ?_ (le_d_rho (exists_N_ge 3 rec3 (by rw [runIdx_rec3])) ?_)
  · simpa [rec3] using d_rho_le_of_word rec3 (by rw [runIdx_rec3])
  · intro w hw
    obtain ⟨dd, hd, hs⟩ := run_facts w
    exact le_trans ((chkSize_facts hs).2.2.2.1 hw) hd

/-- `d ρ 4 = 7`. -/
theorem d_rho_four : d rho 4 = 7 := by
  refine le_antisymm ?_ (le_d_rho (exists_N_ge 4 rec4 (by rw [runIdx_rec4])) ?_)
  · simpa [rec4] using d_rho_le_of_word rec4 (by rw [runIdx_rec4])
  · intro w hw
    obtain ⟨dd, hd, hs⟩ := run_facts w
    exact le_trans ((chkSize_facts hs).2.2.2.2.1 hw) hd

/-- `d ρ 5 = 12`. -/
theorem d_rho_five : d rho 5 = 12 := by
  refine le_antisymm ?_ (le_d_rho (exists_N_ge 5 rec5 (by rw [runIdx_rec5])) ?_)
  · simpa [rec5] using d_rho_le_of_word rec5 (by rw [runIdx_rec5])
  · intro w hw
    obtain ⟨dd, hd, hs⟩ := run_facts w
    exact le_trans ((chkSize_facts hs).2.2.2.2.2.1 hw) hd

/-- `d ρ 6 = 17`. -/
theorem d_rho_six : d rho 6 = 17 := by
  refine le_antisymm ?_ (le_d_rho (exists_N_ge 6 rec6 (by rw [runIdx_rec6])) ?_)
  · simpa [rec6] using d_rho_le_of_word rec6 (by rw [runIdx_rec6])
  · intro w hw
    obtain ⟨dd, hd, hs⟩ := run_facts w
    exact le_trans ((chkSize_facts hs).2.2.2.2.2.2.1 hw) hd

/-- `d ρ 7 = 28`. -/
theorem d_rho_seven : d rho 7 = 28 := by
  refine le_antisymm ?_ (le_d_rho (exists_N_ge 7 rec7 (by rw [runIdx_rec7])) ?_)
  · simpa [rec7] using d_rho_le_of_word rec7 (by rw [runIdx_rec7])
  · intro w hw
    obtain ⟨dd, hd, hs⟩ := run_facts w
    exact le_trans ((chkSize_facts hs).2.2.2.2.2.2.2 hw) hd

/-! ## The maximum -/

theorem seven_le_N_rho_twentyeight : 7 ≤ N rho 28 := by
  have h := length_runIdx_le_N rec7
  rw [runIdx_rec7] at h
  simpa [rec7] using h

/-- **Proposition 9.**  At the plastic number the largest number of
simultaneous knots is exactly `7`. -/
theorem sup_N_rho : IsGreatest (Set.range (N rho)) 7 := by
  constructor
  · exact ⟨28, le_antisymm (N_rho_le_seven 28) seven_le_N_rho_twentyeight⟩
  · rintro y ⟨n, rfl⟩
    exact N_rho_le_seven n

/-! ## Counting the reachable configurations -/

lemma runIdx_append (w : List Move) (m : Move) :
    runIdx (w ++ [m]) = stepIdx m (runIdx w) := by
  simp [runIdx, List.foldl_append]

/-- Every certified configuration is reachable: the recorded parents chain
back to the empty configuration. -/
theorem reachable_of_memVd : ∀ (n : ℕ) (c : List ℕ), memVd c n = true →
    ∃ w : List Move, runIdx w = c := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro c hc
      obtain ⟨dd, hd, pm, pc, -, -, hr⟩ := facts_of_memVd hc
      match dd, hr with
      | 0, hr =>
          refine ⟨[], ?_⟩
          simp only [chkReach, decide_eq_true_eq] at hr
          rw [hr]
          rfl
      | d' + 1, hr =>
          simp only [chkReach, Bool.and_eq_true, decide_eq_true_eq] at hr
          obtain ⟨w, hw⟩ := ih d' (by omega) pc hr.1
          exact ⟨w ++ [moveOf pm], by rw [runIdx_append, hw]; exact hr.2⟩

/-- The configurations stored in the certificate are exactly the reachable
ones. -/
theorem mem_toList_iff (c : List ℕ) : c ∈ V.toList ↔ ∃ w : List Move, runIdx w = c := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Tbl.findLe_of_mem_toList V none none okV h
    exact reachable_of_memVd n c hn
  · rintro ⟨w, rfl⟩
    exact Tbl.mem_toList_of_findLe V (memVd_runIdx w)

lemma nodup_V_toList : V.toList.Nodup := by
  have h := (Tbl.pairwise_of_ok V none none okV).1
  exact List.Nodup.of_map encCfg (h.imp (fun {a b} hab => ne_of_lt hab))

/-- **Proposition 9, the count, in the index model.**  Exactly `25525`
configurations of orbit indices are reachable. -/
theorem card_reachable_idx : (Set.range runIdx).ncard = 25525 := by
  classical
  have hset : Set.range runIdx = (V.toList.toFinset : Set (List ℕ)) := by
    ext c
    simp only [Set.mem_range, Finset.mem_coe, List.mem_toFinset]
    exact (mem_toList_iff c).symm
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup nodup_V_toList,
    Tbl.length_toList, sizeV]

/-! ### The count for the real configurations -/

/-- Distinct index configurations carry distinct sets of knots. -/
lemma cfgSet_inj {c c' : List ℕ} (hc : ∀ i ∈ c, i < 153) (hc' : ∀ i ∈ c', i < 153)
    (hp : List.Pairwise (· < ·) c) (hp' : List.Pairwise (· < ·) c')
    (h : cfgSet c = cfgSet c') : c = c' := by
  have hmem : ∀ i, i ∈ c ↔ i ∈ c' := by
    intro i
    constructor
    · intro hi
      have : tval (oget i) ∈ cfgSet c' := by
        rw [← h]; exact mem_cfgSet.2 ⟨i, hi, rfl⟩
      obtain ⟨j, hj, hij⟩ := mem_cfgSet.1 this
      rwa [tval_oget_inj (hc' j hj) (hc i hi) hij] at hj
    · intro hi
      have : tval (oget i) ∈ cfgSet c := by
        rw [h]; exact mem_cfgSet.2 ⟨i, hi, rfl⟩
      obtain ⟨j, hj, hij⟩ := mem_cfgSet.1 this
      rwa [tval_oget_inj (hc j hj) (hc' i hi) hij] at hj
  have hnd : c.Nodup := hp.imp (fun {a b} hab => ne_of_lt hab)
  have hnd' : c'.Nodup := hp'.imp (fun {a b} hab => ne_of_lt hab)
  exact List.Perm.eq_of_pairwise (le := (· < ·))
    (fun a b _ _ h1 h2 => absurd h1 (asymm h2)) hp hp'
    ((List.perm_ext_iff_of_nodup hnd hnd').2 hmem)

/-- **Proposition 9, the count.**  At the plastic number exactly `25525`
configurations of knots are reachable. -/
theorem card_reachable_configs :
    {S : Finset ℝ | ∃ w : List Move, run rho w = S}.ncard = 25525 := by
  classical
  have himg : {S : Finset ℝ | ∃ w : List Move, run rho w = S} = cfgSet '' Set.range runIdx := by
    ext S
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨runIdx w, ⟨w, rfl⟩, (run_eq_cfgSet w).symm⟩
    · rintro ⟨c, ⟨w, rfl⟩, rfl⟩
      exact ⟨w, run_eq_cfgSet w⟩
  have hinj : Set.InjOn cfgSet (Set.range runIdx) := by
    rintro c ⟨w, rfl⟩ c' ⟨w', rfl⟩ h
    exact cfgSet_inj (runIdx_lt w) (runIdx_lt w') (runIdx_pairwise w) (runIdx_pairwise w') h
  rw [himg, Set.InjOn.ncard_image hinj, card_reachable_idx]

end Plastic
end KnotGame
