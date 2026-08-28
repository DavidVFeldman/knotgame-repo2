import RequestProject.Ternary
import RequestProject.Golden

/-!
# T24 — cylinder counts for the kind sets (paper `prop:kinddim`), split

The *survival tree of `1/2`* has as its nodes at depth `n` the words of `n`
moves that `1/2` survives — the level-`n` cylinders of the kind set `K_λ` of
the paper, coded in base three by `L, M, R ↦ 0, 1, 2`.  This file counts them.

* `kindWords lam x n` — the words of length `n` survived by a knot at `x`,
  and `card_kindWords_succ`, the one-step recursion that drives everything:
  the count at `x` is the sum, over the moves `x` survives, of the counts at
  the images of `x`.

* **T24a** (`card_kindWords_three_halves`).  At `λ = 3/2` there are exactly
  `2 ^ n` nodes at depth `n`.  The three deleted intervals tile `[0,1]`, so
  exactly one move is fatal at each node — never none, never two
  (`Ternary.exists_unique_fatal`); the dyadic invariant of
  `RequestProject.Ternary` is what rules out a node sitting on a cell
  boundary.  The proof is an induction on `n`; no Hausdorff dimension is
  involved.

* **T24b** (`card_kindWords_phi_add_three`).  At `λ = φ` the counts satisfy
  `N_{n+3} = 4 N_n`.  This is read off the certified five-point orbit of
  `RequestProject.Golden`: from `1/2 = p₂` the surviving moves lead to `p₀`
  and `p₄`, each of which has two surviving moves, both landing on `p₁`
  resp. `p₃`, and each of those has a single surviving move, back to `p₂`.

**T24c is not attempted.**  Neither the Hausdorff nor the box dimension of the
kind sets is claimed anywhere in this file: the cylinder count alone does not
give them (it bounds the box dimension from above only after a separation
statement about the cylinders, which is not proved here).  See
`SCRUPLES-round8.md`.

## Conventions (SCRUPLES)

* A node of the survival tree is a *word*, not a point: two different words are
  two different nodes even if they carry `1/2` to the same place.
* `N_n` of the paper is `(kindWords lam (1/2) n).card` here, so `N_0 = 1`
  (the empty word).
-/

namespace KnotGame
namespace KindTree

open scoped Classical

variable {lam x : ℝ}

/-! ### Words of a given length -/

/-- All words of moves of a given length. -/
def words : ℕ → Finset (List Move)
  | 0 => {[]}
  | n + 1 => (Finset.univ : Finset Move).biUnion (fun m => (words n).image (List.cons m))

lemma mem_words : ∀ {n : ℕ} {w : List Move}, w ∈ words n ↔ w.length = n
  | 0, w => by
      constructor
      · intro h; simp [words] at h; simp [h]
      · intro h; simp [words, List.length_eq_zero_iff.mp h]
  | n + 1, w => by
      simp only [words, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨m, v, hv, rfl⟩
        simp [mem_words.mp hv]
      · intro h
        match w with
        | [] => simp at h
        | m :: v => exact ⟨m, v, mem_words.mpr (by simpa using h), rfl⟩

/-! ### The survival tree -/

/-- The nodes of the survival tree of a knot at `x` at depth `n`: the words of
`n` moves that a knot at `x` survives. -/
noncomputable def kindWords (lam x : ℝ) (n : ℕ) : Finset (List Move) :=
  (words n).filter (fun w => survivesWord lam x w)

lemma mem_kindWords {n : ℕ} {w : List Move} :
    w ∈ kindWords lam x n ↔ w.length = n ∧ survivesWord lam x w := by
  simp [kindWords, mem_words]

@[simp] lemma card_kindWords_zero (lam x : ℝ) : (kindWords lam x 0).card = 1 := by
  have : kindWords lam x 0 = {[]} := by
    ext w
    simp [mem_kindWords, List.length_eq_zero_iff]
    rintro rfl
    trivial
  rw [this, Finset.card_singleton]

/-- The survival tree of `x` at depth `n+1` splits according to the first
move. -/
lemma kindWords_succ (lam x : ℝ) (n : ℕ) :
    kindWords lam x (n + 1)
      = (Finset.univ.filter (fun m : Move => survives lam m x)).biUnion
          (fun m => (kindWords lam (act lam m x) n).image (List.cons m)) := by
  ext w
  simp only [mem_kindWords, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_image]
  constructor
  · rintro ⟨hlen, hsurv⟩
    match w with
    | [] => simp at hlen
    | m :: v =>
        rw [survivesWord_cons] at hsurv
        exact ⟨m, hsurv.1, v, ⟨by simpa using hlen, hsurv.2⟩, rfl⟩
  · rintro ⟨m, hm, v, ⟨hlen, hsurv⟩, rfl⟩
    exact ⟨by simp [hlen], by rw [survivesWord_cons]; exact ⟨hm, hsurv⟩⟩

/-- **The counting recursion.**  The number of nodes at depth `n+1` is the sum,
over the moves that `x` survives, of the numbers of nodes at depth `n` of the
images. -/
lemma card_kindWords_succ (lam x : ℝ) (n : ℕ) :
    (kindWords lam x (n + 1)).card
      = ∑ m ∈ Finset.univ.filter (fun m : Move => survives lam m x),
          (kindWords lam (act lam m x) n).card := by
  rw [kindWords_succ, Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun m _ =>
      Finset.card_image_of_injective _ (List.cons_injective)
  · intro a _ b _ hab
    simp only [Finset.disjoint_left, Finset.mem_image]
    rintro w ⟨u, -, rfl⟩ ⟨v, -, hv⟩
    obtain ⟨h1, -⟩ := List.cons_eq_cons.mp hv
    exact hab h1.symm

/-! ### T24a: the count at `λ = 3/2` -/

open Ternary in
/-- The count at a dyadic point of `(0,1)` doubles at every level. -/
lemma card_kindWords_dyadic :
    ∀ (n j : ℕ) (y : ℝ), 0 < y → y < 1 → Dyadic j y →
      (kindWords (3 / 2 : ℝ) y n).card = 2 ^ n := by
  intro n
  induction n with
  | zero => intro j y _ _ _; simp
  | succ n ih =>
      intro j y hy0 hy1 hyd
      have h1 := three_mul_ne_one hyd
      have h2 := three_mul_ne_two hyd
      obtain ⟨m₀, hm₀, hun⟩ := exists_unique_fatal hy0 hy1 h1 h2
      have hfatal : Finset.univ.filter (fun m : Move => ¬ survives (3 / 2 : ℝ) m y) = {m₀} := by
        ext m
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨fun hm => hun m hm, fun hm => hm ▸ hm₀⟩
      have hcard : (Finset.univ.filter (fun m : Move => survives (3 / 2 : ℝ) m y)).card = 2 := by
        have hsum := Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset Move)) (p := fun m => survives (3 / 2 : ℝ) m y)
        rw [hfatal, Finset.card_singleton] at hsum
        have h3 : (Finset.univ : Finset Move).card = 3 := by decide
        omega
      rw [card_kindWords_succ]
      have hterm : ∀ m ∈ Finset.univ.filter (fun m : Move => survives (3 / 2 : ℝ) m y),
          (kindWords (3 / 2 : ℝ) (act (3 / 2 : ℝ) m y) n).card = 2 ^ n := by
        intro m hm
        rw [Finset.mem_filter] at hm
        obtain ⟨ha0, ha1⟩ := act_mem_Ioo one_lt_lam32 ⟨hy0, hy1⟩ hm.2
        exact ih (j + 1) _ ha0 ha1 (dyadic_act hyd m)
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, hcard]
      ring

/-- **T24a** (paper `prop:kinddim`, the count at `3/2`).  At `λ = 3/2` the
survival tree of `1/2` has exactly `2 ^ n` nodes at depth `n`. -/
theorem card_kindWords_three_halves (n : ℕ) :
    (kindWords (3 / 2 : ℝ) (1 / 2 : ℝ) n).card = 2 ^ n :=
  card_kindWords_dyadic n 0 (1 / 2 : ℝ) (by norm_num) (by norm_num) Ternary.dyadic_half

/-! ### T24b: the count at `λ = φ` -/

open Golden in
/-- The one-step recursion at the five orbit points of the golden ratio. -/
lemma card_kindWords_p_succ (i : Fin 5) (n : ℕ) :
    (kindWords phi (p i) (n + 1)).card
      = ∑ m ∈ Finset.univ.filter (fun m : Move => absSurv m i),
          (kindWords phi (p (absAct m i)) n).card := by
  rw [card_kindWords_succ]
  have hfil : Finset.univ.filter (fun m : Move => survives phi m (p i))
      = Finset.univ.filter (fun m : Move => absSurv m i) := by
    apply Finset.filter_congr
    intro m _
    simpa using survives_p m i
  rw [hfil]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_filter] at hm
  rw [act_p m i (by simpa using hm.2)]

open Golden in
lemma card_p2_succ (n : ℕ) :
    (kindWords phi (p 2) (n + 1)).card
      = (kindWords phi (p 0) n).card + (kindWords phi (p 4) n).card := by
  rw [card_kindWords_p_succ]
  rw [show Finset.univ.filter (fun m : Move => absSurv m 2) = ({Move.L, Move.R} : Finset Move)
    from by decide]
  simp [absAct]

open Golden in
lemma card_p0_succ (n : ℕ) :
    (kindWords phi (p 0) (n + 1)).card = 2 * (kindWords phi (p 1) n).card := by
  rw [card_kindWords_p_succ]
  rw [show Finset.univ.filter (fun m : Move => absSurv m 0) = ({Move.M, Move.R} : Finset Move)
    from by decide]
  simp [absAct]
  ring

open Golden in
lemma card_p4_succ (n : ℕ) :
    (kindWords phi (p 4) (n + 1)).card = 2 * (kindWords phi (p 3) n).card := by
  rw [card_kindWords_p_succ]
  rw [show Finset.univ.filter (fun m : Move => absSurv m 4) = ({Move.L, Move.M} : Finset Move)
    from by decide]
  simp [absAct]
  ring

open Golden in
lemma card_p1_succ (n : ℕ) :
    (kindWords phi (p 1) (n + 1)).card = (kindWords phi (p 2) n).card := by
  rw [card_kindWords_p_succ]
  rw [show Finset.univ.filter (fun m : Move => absSurv m 1) = ({Move.R} : Finset Move)
    from by decide]
  simp [absAct]

open Golden in
lemma card_p3_succ (n : ℕ) :
    (kindWords phi (p 3) (n + 1)).card = (kindWords phi (p 2) n).card := by
  rw [card_kindWords_p_succ]
  rw [show Finset.univ.filter (fun m : Move => absSurv m 3) = ({Move.L} : Finset Move)
    from by decide]
  simp [absAct]

open Golden in
/-- **T24b** (paper `prop:kinddim`, the count at `φ`).  At `λ = φ` the number of
nodes at depth `n+3` of the survival tree of `1/2` is four times the number at
depth `n`. -/
theorem card_kindWords_phi_add_three (n : ℕ) :
    (kindWords phi (1 / 2 : ℝ) (n + 3)).card = 4 * (kindWords phi (1 / 2 : ℝ) n).card := by
  have hp2 : (1 / 2 : ℝ) = p 2 := (p2).symm
  rw [hp2]
  have h1 : (kindWords phi (p 2) (n + 3)).card
      = (kindWords phi (p 0) (n + 2)).card + (kindWords phi (p 4) (n + 2)).card :=
    card_p2_succ (n + 2)
  rw [h1, card_p0_succ (n + 1), card_p4_succ (n + 1), card_p1_succ n, card_p3_succ n]
  ring

end KindTree
end KnotGame
