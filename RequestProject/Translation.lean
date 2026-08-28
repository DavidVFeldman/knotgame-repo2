import RequestProject.Ternary
import RequestProject.Permanence

/-!
# T22d — the knot-free equivalent at `λ = 3/2` (paper `prop:translation`)

The ternary rules of `RequestProject.Ternary` say that at `λ = 3/2`, in the
coordinate `w = 2x`, a move is the choice of a forbidden digit `c ∈ {0,1,2}`
and the dynamics is

  `w ↦ (3/2) w − [⌊(3/2) w⌋ > c]`,   the knot dying when `⌊(3/2) w⌋ = c`.

This file removes the knots from the statement of unboundedness altogether.
`MahlerCriterion` is the paper's condition: for every `k` there are a length
`N`, a control `c ∈ {0,1,2}^N` and birth indices `t_1 < … < t_k` with
`c_{t_i} = 1`, such that the `k` trajectories started at `w = 1` immediately
after those births avoid the control to time `N`.  `unbounded_iff_mahler` is
the equivalence

  `(∀ K, ∃ n, K ≤ N_{3/2}(n))  ↔  MahlerCriterion`.

The proof has two halves.  `translate_core` is the dictionary: for a knot at a
dyadic point of `(0,1)`, surviving a word of moves is *the same statement* as
the `w`-trajectory avoiding the corresponding control, and the image is the
trajectory's endpoint.  `card_birthSet` is the bookkeeping: the number of
knots of a run is the number of its `M`s whose suffix keeps `1/2` alive
(`births`), which is the number of admissible birth indices.

## Conventions (SCRUPLES)

* Control letters are indexed from `0`: `c j` is applied between time `j` and
  time `j+1`, so a birth at letter `b` (that is `c b = 1`) produces a knot at
  time `b+1` with `w = 1`, and its trajectory is then driven by
  `c (b+1), c (b+2), …`.  The paper indexes from `1`, where the birth letter
  and the birth time carry the same number; the two conventions describe the
  same object.
* `c` is a function `ℕ → ℤ` whose values are always in `{0,1,2}`; only
  `c 0, …, c (N-1)` are used.
* The paper's "all stay in `(0,2)`" is not a separate condition: a knot that
  avoids the control stays in `(0,1)` automatically (`act_mem_Ioo`), and
  conversely `MahlerAlive` is exactly the avoidance condition.
* `N_{3/2}` unbounded is written `∀ K, ∃ n, K ≤ N (3/2) n`, as everywhere else
  in the development.
-/

namespace KnotGame
namespace Ternary

open Finset

/-! ### The knot-free dynamics -/

/-- One step of the `w`-recursion under the forbidden digit `cj`. -/
noncomputable def wstep (cj : ℤ) (w : ℝ) : ℝ :=
  (3 / 2 : ℝ) * w - (if cj < ⌊(3 / 2 : ℝ) * w⌋ then 1 else 0)

/-- The trajectory of `w` under the control `c` read from index `b` on. -/
noncomputable def witer (c : ℕ → ℤ) (b : ℕ) (w : ℝ) : ℕ → ℝ
  | 0 => w
  | i + 1 => wstep (c (b + i)) (witer c b w i)

@[simp] lemma witer_zero (c : ℕ → ℤ) (b : ℕ) (w : ℝ) : witer c b w 0 = w := rfl

lemma witer_succ (c : ℕ → ℤ) (b : ℕ) (w : ℝ) (i : ℕ) :
    witer c b w (i + 1) = wstep (c (b + i)) (witer c b w i) := rfl

/-- Peeling the first step off a trajectory. -/
lemma witer_shift (c : ℕ → ℤ) (b : ℕ) (w : ℝ) :
    ∀ i, witer c b w (i + 1) = witer c (b + 1) (wstep (c b) w) i
  | 0 => by simp [witer_succ]
  | i + 1 => by
      rw [witer_succ, witer_shift c b w i, witer_succ c (b + 1)]
      congr 2
      omega

/-- A knot alive at `x` with digit rule: the `w`-step is the game's step. -/
lemma two_mul_act (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (m : Move)
    (hs : survives (3 / 2 : ℝ) m x) :
    2 * act (3 / 2 : ℝ) m x = wstep (code m) (2 * x) := by
  have hfl : ⌊(3 / 2 : ℝ) * (2 * x)⌋ = D x := by rw [D]; congr 1; ring
  rw [act_eq_ternary hx0 hx1 m hs, wstep, hfl]
  by_cases hc : code m < D x <;> simp [hc] <;> ring

/-! ### The dictionary -/

/-- **The translation.**  For a knot at a dyadic point of `(0,1)`, surviving the
word `u` is exactly the condition that the `w`-trajectory avoids the control,
and the image of the knot is the endpoint of the trajectory. -/
lemma translate_core : ∀ (u : List Move) (x : ℝ) (j : ℕ) (c : ℕ → ℤ) (b : ℕ),
    0 < x → x < 1 → Dyadic j x → (∀ i, i < u.length → c (b + i) = code (u.getD i Move.L)) →
    ((survivesWord (3 / 2 : ℝ) x u ↔
        ∀ i, i < u.length → ⌊(3 / 2 : ℝ) * witer c b (2 * x) i⌋ ≠ c (b + i)) ∧
      (survivesWord (3 / 2 : ℝ) x u →
        2 * posAfter (3 / 2 : ℝ) x u = witer c b (2 * x) u.length))
  | [], x, j, c, b => by
      intro _ _ _ _
      exact ⟨by simp, by simp⟩
  | m :: u, x, j, c, b => by
      intro hx0 hx1 hd hc
      have hcb : c (b + 0) = code m := hc 0 (by simp)
      have hcb' : c b = code m := by simpa using hcb
      have hfl : ⌊(3 / 2 : ℝ) * (2 * x)⌋ = D x := by rw [D]; congr 1; ring
      have hfirst : (⌊(3 / 2 : ℝ) * witer c b (2 * x) 0⌋ ≠ c (b + 0))
          ↔ survives (3 / 2 : ℝ) m x := by
        rw [witer_zero, hfl, hcb,
          survives_iff_digit_ne hx0 hx1 (three_mul_ne_one hd) (three_mul_ne_two hd) m]
      constructor
      · constructor
        · rintro ⟨hs, hrest⟩ i hi
          rcases Nat.eq_zero_or_pos i with rfl | hipos
          · exact hfirst.mpr hs
          · obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
            have hact := two_mul_act x hx0 hx1 m hs
            obtain ⟨hx0', hx1'⟩ := act_mem_Ioo one_lt_lam32 ⟨hx0, hx1⟩ hs
            have hIH := (translate_core u (act (3 / 2 : ℝ) m x) (j + 1) c (b + 1)
              hx0' hx1' (dyadic_act hd m) (fun i' hi' => by
                have := hc (i' + 1) (by simpa using Nat.succ_lt_succ hi')
                simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this)).1
            have hstep : witer c b (2 * x) (i + 1)
                = witer c (b + 1) (2 * act (3 / 2 : ℝ) m x) i := by
              rw [witer_shift, hact, hcb']
            rw [hstep]
            have := hIH.mp hrest i (by simpa using Nat.lt_of_succ_lt_succ hi)
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
        · intro H
          have hs : survives (3 / 2 : ℝ) m x := hfirst.mp (H 0 (by simp))
          refine ⟨hs, ?_⟩
          have hact := two_mul_act x hx0 hx1 m hs
          obtain ⟨hx0', hx1'⟩ := act_mem_Ioo one_lt_lam32 ⟨hx0, hx1⟩ hs
          have hIH := (translate_core u (act (3 / 2 : ℝ) m x) (j + 1) c (b + 1)
            hx0' hx1' (dyadic_act hd m) (fun i' hi' => by
              have := hc (i' + 1) (by simpa using Nat.succ_lt_succ hi')
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this)).1
          refine hIH.mpr (fun i hi => ?_)
          have hstep : witer c b (2 * x) (i + 1)
              = witer c (b + 1) (2 * act (3 / 2 : ℝ) m x) i := by
            rw [witer_shift, hact, hcb']
          have := H (i + 1) (by simpa using Nat.succ_lt_succ hi)
          rw [hstep] at this
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
      · rintro ⟨hs, hrest⟩
        have hact := two_mul_act x hx0 hx1 m hs
        obtain ⟨hx0', hx1'⟩ := act_mem_Ioo one_lt_lam32 ⟨hx0, hx1⟩ hs
        have hIH := (translate_core u (act (3 / 2 : ℝ) m x) (j + 1) c (b + 1)
          hx0' hx1' (dyadic_act hd m) (fun i' hi' => by
            have := hc (i' + 1) (by simpa using Nat.succ_lt_succ hi')
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this)).2 hrest
        have hstep : witer c b (2 * x) (u.length + 1)
            = witer c (b + 1) (2 * act (3 / 2 : ℝ) m x) u.length := by
          rw [witer_shift, hact, hcb']
        rw [posAfter_cons, List.length_cons, hstep]
        exact hIH

/-! ### Births -/

/-- The birth indices of a run: the positions carrying an `M` whose subsequent
suffix keeps `1/2` alive. -/
noncomputable def birthSet (lam : ℝ) (W : List Move) : Finset ℕ :=
  (range W.length).filter
    (fun b => W.getD b Move.L = Move.M ∧ survivesWord lam (1/2) (W.drop (b + 1)))

lemma mem_birthSet {lam : ℝ} {W : List Move} {b : ℕ} :
    b ∈ birthSet lam W ↔
      b < W.length ∧ W.getD b Move.L = Move.M ∧ survivesWord lam (1/2) (W.drop (b + 1)) := by
  simp [birthSet]

/-- Membership in the birth set of a one-letter extension. -/
lemma mem_birthSet_cons {lam : ℝ} {m : Move} {w : List Move} (b : ℕ) :
    b ∈ birthSet lam (m :: w) ↔
      ((b = 0 ∧ m = Move.M ∧ survivesWord lam (1/2) w) ∨ ∃ a ∈ birthSet lam w, a + 1 = b) := by
  rw [mem_birthSet]
  cases b with
  | zero =>
      have hlen : 0 < (m :: w).length := by simp
      have hg : (m :: w).getD 0 Move.L = m := by simp
      have hd : (m :: w).drop (0 + 1) = w := by simp
      rw [hg, hd]
      constructor
      · rintro ⟨-, h1, h2⟩
        exact Or.inl ⟨rfl, h1, h2⟩
      · rintro (⟨-, h1, h2⟩ | ⟨a, -, ha⟩)
        · exact ⟨hlen, h1, h2⟩
        · omega
  | succ b =>
      have hg : (m :: w).getD (b + 1) Move.L = w.getD b Move.L := by simp
      have hd : (m :: w).drop (b + 1 + 1) = w.drop (b + 1) := by simp
      have hl : (b + 1 < (m :: w).length) ↔ (b < w.length) := by simp
      rw [hg, hd]
      constructor
      · rintro ⟨hlen, h1, h2⟩
        exact Or.inr ⟨b, mem_birthSet.mpr ⟨hl.mp hlen, h1, h2⟩, rfl⟩
      · rintro (⟨hb, -, -⟩ | ⟨a, ha, hab⟩)
        · omega
        · obtain ⟨hlen, h1, h2⟩ := mem_birthSet.mp ha
          have : a = b := by omega
          subst this
          exact ⟨hl.mpr hlen, h1, h2⟩

/-- The number of birth indices is the number of knots. -/
lemma card_birthSet (lam : ℝ) : ∀ W : List Move, (birthSet lam W).card = births lam W
  | [] => by simp [birthSet]
  | m :: w => by
      classical
      have hinj : Function.Injective (fun a : ℕ => a + 1) := add_left_injective 1
      by_cases hcond : m = Move.M ∧ survivesWord lam (1/2) w
      · have hsplit : birthSet lam (m :: w) = insert 0 ((birthSet lam w).image (· + 1)) := by
          ext b
          rw [mem_birthSet_cons b, Finset.mem_insert, Finset.mem_image]
          constructor
          · rintro (⟨rfl, -, -⟩ | h)
            · exact Or.inl rfl
            · exact Or.inr h
          · rintro (rfl | h)
            · exact Or.inl ⟨rfl, hcond.1, hcond.2⟩
            · exact Or.inr h
        have hnot : (0 : ℕ) ∉ (birthSet lam w).image (· + 1) := by
          simp only [Finset.mem_image, not_exists]
          rintro a ⟨-, ha⟩
          omega
        rw [hsplit, births_cons, if_pos hcond, Finset.card_insert_of_notMem hnot,
          Finset.card_image_of_injective _ hinj, card_birthSet lam w]
      · have hsplit : birthSet lam (m :: w) = (birthSet lam w).image (· + 1) := by
          ext b
          rw [mem_birthSet_cons b, Finset.mem_image]
          constructor
          · rintro (⟨-, h1, h2⟩ | h)
            · exact absurd ⟨h1, h2⟩ hcond
            · exact h
          · intro h
            exact Or.inr h
        rw [hsplit, births_cons, if_neg hcond, Finset.card_image_of_injective _ hinj,
          card_birthSet lam w]
        omega

/-! ### The criterion -/

/-- The knot born by the letter `b` of the control `c` avoids the control up to
time `N`. -/
def MahlerAlive (c : ℕ → ℤ) (b N : ℕ) : Prop :=
  ∀ i, b + 1 + i < N → ⌊(3 / 2 : ℝ) * witer c (b + 1) 1 i⌋ ≠ c (b + 1 + i)

/-- **The knot-free criterion** (paper `prop:translation`).  For every `k` there
are a horizon `N`, a control `c` with values in `{0,1,2}` and birth indices
`t 0 < … < t (k−1)` below `N`, each carrying the digit `1`, whose trajectories
avoid the control to time `N`. -/
def MahlerCriterion : Prop :=
  ∀ k : ℕ, ∃ (N : ℕ) (c : ℕ → ℤ) (t : ℕ → ℕ),
    (∀ j, c j = 0 ∨ c j = 1 ∨ c j = 2) ∧
    (∀ i i', i < i' → i' < k → t i < t i') ∧
    (∀ i, i < k → t i < N ∧ c (t i) = 1 ∧ MahlerAlive c (t i) N)

/-- The move carrying a given ternary digit. -/
def moveOf (z : ℤ) : Move := if z = 0 then Move.L else if z = 1 then Move.M else Move.R

@[simp] lemma moveOf_one : moveOf 1 = Move.M := by simp [moveOf]

lemma code_moveOf {z : ℤ} (hz : z = 0 ∨ z = 1 ∨ z = 2) : code (moveOf z) = z := by
  rcases hz with h | h | h <;> subst h <;> decide

/-- The control read off a word of moves. -/
def ctrl (W : List Move) (j : ℕ) : ℤ := code (W.getD j Move.L)

lemma ctrl_mem (W : List Move) (j : ℕ) : ctrl W j = 0 ∨ ctrl W j = 1 ∨ ctrl W j = 2 := by
  unfold ctrl
  cases W.getD j Move.L <;> simp [code]

/-- Along a run, the survival of the knot born at `b` is the avoidance
condition of the criterion. -/
lemma mahlerAlive_iff (W : List Move) (b : ℕ) (hb : b < W.length) :
    MahlerAlive (ctrl W) b W.length ↔ survivesWord (3 / 2 : ℝ) (1/2 : ℝ) (W.drop (b + 1)) := by
  have hlen : (W.drop (b + 1)).length = W.length - (b + 1) := by simp
  have hctrl : ∀ i, i < (W.drop (b + 1)).length →
      ctrl W (b + 1 + i) = code ((W.drop (b + 1)).getD i Move.L) := by
    intro i hi
    unfold ctrl
    congr 1
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
  have hcore := (translate_core (W.drop (b + 1)) (1/2 : ℝ) 0 (ctrl W) (b + 1)
    (by norm_num) (by norm_num) dyadic_half hctrl).1
  rw [show (2 : ℝ) * (1/2 : ℝ) = 1 by norm_num] at hcore
  rw [hcore]
  constructor
  · intro H i hi
    exact H i (by omega)
  · intro H i hi
    exact H i (by omega)

/-- **T22d** (paper `prop:translation`).  `N_{3/2}` is unbounded if and only if
the knot-free criterion holds. -/
theorem unbounded_iff_mahler :
    (∀ K : ℕ, ∃ n : ℕ, K ≤ N (3 / 2 : ℝ) n) ↔ MahlerCriterion := by
  classical
  constructor
  · intro H k
    obtain ⟨n, hn⟩ := H k
    -- a word of length `n` with at least `k` knots
    obtain ⟨v, -, hv⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin n → Move))
      ⟨fun _ => Move.L, Finset.mem_univ _⟩ (fun v => (run (3 / 2 : ℝ) (List.ofFn v)).card)
    set W : List Move := List.ofFn v with hW
    have hlen : W.length = n := by simp [hW]
    have hcard : k ≤ (run (3 / 2 : ℝ) W).card := by
      rw [hW, ← hv]; exact hn
    have hbirth : k ≤ (birthSet (3 / 2 : ℝ) W).card := by
      rw [card_birthSet, ← card_run one_lt_lam32 W]
      exact hcard
    obtain ⟨S, hS, hScard⟩ := Finset.exists_subset_card_eq hbirth
    set e := S.orderIsoOfFin hScard with he
    refine ⟨W.length, ctrl W, fun i => if h : i < k then (e ⟨i, h⟩ : ℕ) else 0,
      ctrl_mem W, ?_, ?_⟩
    · intro i i' hii hi'
      have hi : i < k := lt_trans hii hi'
      dsimp only
      rw [dif_pos hi, dif_pos hi']
      exact_mod_cast (S.orderIsoOfFin hScard).strictMono (show (⟨i, hi⟩ : Fin k) < ⟨i', hi'⟩ from hii)
    · intro i hi
      dsimp only
      rw [dif_pos hi]
      obtain ⟨hb, hM, hsurv⟩ := mem_birthSet.mp (hS (e ⟨i, hi⟩).2)
      refine ⟨hb, ?_, (mahlerAlive_iff W _ hb).mpr hsurv⟩
      unfold ctrl
      rw [hM]
      rfl
  · intro H K
    obtain ⟨N₀, c, t, hc, hmono, hspec⟩ := H K
    set W : List Move := (List.range N₀).map (fun j => moveOf (c j)) with hW
    have hlen : W.length = N₀ := by simp [hW]
    have hget : ∀ j, j < N₀ → W.getD j Move.L = moveOf (c j) := by
      intro j hj
      rw [hW, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
      rfl
    have hctrl : ∀ j, j < N₀ → ctrl W j = c j := by
      intro j hj
      unfold ctrl
      rw [hget j hj, code_moveOf (hc j)]
    -- the `K` birth indices belong to the birth set
    have hsub : (range K).image t ⊆ birthSet (3 / 2 : ℝ) W := by
      intro b hb
      rw [Finset.mem_image] at hb
      obtain ⟨i, hi, rfl⟩ := hb
      rw [Finset.mem_range] at hi
      obtain ⟨hlt, hone, halive⟩ := hspec i hi
      have hbW : t i < W.length := by rw [hlen]; exact hlt
      refine mem_birthSet.mpr ⟨hbW, ?_, ?_⟩
      · rw [hget _ hlt, hone, moveOf_one]
      · refine (mahlerAlive_iff W (t i) hbW).mp ?_
        intro j hj
        rw [hlen] at hj
        have hjN : t i + 1 + j < N₀ := hj
        have hiter : ∀ s, s ≤ j → witer (ctrl W) (t i + 1) 1 s = witer c (t i + 1) 1 s := by
          intro s
          induction s with
          | zero => intro _; rfl
          | succ s ih =>
              intro hs
              rw [witer_succ, witer_succ, ih (by omega), hctrl _ (by omega)]
        rw [hiter j (le_refl j), hctrl _ (by omega)]
        exact halive j hjN
    have hcard : K ≤ (birthSet (3 / 2 : ℝ) W).card := by
      refine le_trans ?_ (Finset.card_le_card hsub)
      rw [Finset.card_image_of_injOn, Finset.card_range]
      intro a ha b hb hab
      rw [Finset.mem_coe, Finset.mem_range] at ha hb
      by_contra hne
      rcases Nat.lt_or_ge a b with h | h
      · exact absurd hab (ne_of_lt (hmono a b h hb))
      · have hba : b < a := by omega
        exact absurd hab.symm (ne_of_lt (hmono b a hba ha))
    refine ⟨W.length, ?_⟩
    calc K ≤ (birthSet (3 / 2 : ℝ) W).card := hcard
      _ = births (3 / 2 : ℝ) W := card_birthSet _ W
      _ ≤ N (3 / 2 : ℝ) W.length := births_le_N one_lt_lam32 W

end Ternary
end KnotGame
