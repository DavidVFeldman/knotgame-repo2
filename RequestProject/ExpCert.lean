import RequestProject.ExpCount

/-!
# Interval-arithmetic certificates for the doubling property (round 7)

`ExpCount.Doubling lam a b T` asks that every `x ∈ [a,b]` have two distinct
branch words of length `T` whose images stay in `[a,b]`.  This file reduces that
to a *finite rational computation*, uniformly over a parameter interval
`lam ∈ [l0, l1]`.

Since both branch maps are increasing in `x` and monotone in `lam`, the image of
a rational box `[lo,hi] × [l0,l1]` is enclosed by

  branch `0`: `[l0 * lo, l1 * hi]`,
  branch `1`: `[l1 * lo - l1 + 1, l0 * hi - l0 + 1]`,

valid as long as `0 ≤ lo` and `hi ≤ 1`, which the checker `iok` verifies at every
step.  A *certificate* is a list of cells `(p, q, u, v)` tiling `[a,b]`, each
carrying two distinct words of length `T` whose enclosures over the cell lie in
`[a,b]`; `doubling_of_cert` turns such a list into `Doubling lam a b T` for every
`lam` in the parameter interval.

## Conventions (SCRUPLES)

* Cells are closed and consecutive (`chained`), and the last one reaches `b` (or
  past it); no point of `[a,b]` is missed.
* The enclosure is one-sided in each endpoint — the lower end of the image
  depends only on `lo`, the upper end only on `hi` — which is what makes the
  check a single pass over the word.
-/

namespace KnotGame
namespace ExpCert

open KnotGame.Branching KnotGame.ExpCount

/-! ### Interval arithmetic -/

/-- Lower endpoint of the enclosure of one branch step. -/
def ilo (l0 l1 : ℚ) (e : Fin 2) (lo : ℚ) : ℚ := if e = 0 then l0 * lo else l1 * lo - l1 + 1

/-- Upper endpoint of the enclosure of one branch step. -/
def ihi (l0 l1 : ℚ) (e : Fin 2) (hi : ℚ) : ℚ := if e = 0 then l1 * hi else l0 * hi - l0 + 1

/-- The checker: run the enclosure along the word, verifying the invariant
`0 ≤ lo ≤ hi ≤ 1` at every step, and require the final enclosure inside `[a,b]`. -/
def iok (l0 l1 a b : ℚ) : List (Fin 2) → ℚ → ℚ → Bool
  | [], lo, hi => decide (a ≤ lo) && decide (hi ≤ b)
  | e :: w, lo, hi =>
      decide (0 ≤ lo) && decide (lo ≤ hi) && decide (hi ≤ 1) &&
        iok l0 l1 a b w (ilo l0 l1 e lo) (ihi l0 l1 e hi)

/-- Soundness of the checker. -/
lemma rapp_mem_of_iok {l0 l1 a b : ℚ} {lam : ℝ} (hlam0 : ((l0 : ℚ) : ℝ) ≤ lam)
    (hlam1 : lam ≤ ((l1 : ℚ) : ℝ)) (hl0 : (0 : ℝ) < (l0 : ℚ)) :
    ∀ (w : List (Fin 2)) (lo hi : ℚ) (x : ℝ), ((lo : ℚ) : ℝ) ≤ x → x ≤ ((hi : ℚ) : ℝ) →
      iok l0 l1 a b w lo hi = true →
      ((a : ℚ) : ℝ) ≤ rapp lam x w ∧ rapp lam x w ≤ ((b : ℚ) : ℝ) := by
  intro w
  induction w with
  | nil =>
      intro lo hi x hx hx' h
      simp only [iok, Bool.and_eq_true, decide_eq_true_eq] at h
      constructor
      · exact le_trans (by exact_mod_cast h.1) hx
      · exact le_trans hx' (by exact_mod_cast h.2)
  | cons e w ih =>
      intro lo hi x hx hx' h
      simp only [iok, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨hlo, -⟩, hhi⟩, hrest⟩ := h
      have hlo' : (0:ℝ) ≤ ((lo : ℚ) : ℝ) := by exact_mod_cast hlo
      have hhi' : ((hi : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hhi
      refine ih _ _ (f lam e x) ?_ ?_ hrest
      · rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl
        · simp only [ilo, f_zero]
          push_cast
          nlinarith
        · simp only [ilo, if_neg (by decide : ¬(1 : Fin 2) = 0), f_one]
          push_cast
          nlinarith
      · rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl
        · simp only [ihi, f_zero]
          push_cast
          nlinarith
        · simp only [ihi, if_neg (by decide : ¬(1 : Fin 2) = 0), f_one]
          push_cast
          nlinarith

/-! ### Certificates -/

/-- A cell of a certificate: an interval `[p,q]` and two branch words. -/
abbrev Cell := ℚ × ℚ × List (Fin 2) × List (Fin 2)

/-- The cells are consecutive and cover up to `b`.  Stated for any payload type,
so that it applies both to the cells of a certificate and to the parameter cells
of `RequestProject.ExpWindow`. -/
def chained {β : Type} (a : ℚ) : List (ℚ × ℚ × β) → ℚ → Bool
  | [], b => decide (b ≤ a)
  | c :: rest, b => (c.1 == a) && chained c.2.1 rest b

/-- A cell is valid: two distinct words of length `T` whose enclosures over the
cell, for every parameter in `[l0,l1]`, lie inside `[a,b]`. -/
def cellOK (l0 l1 a b : ℚ) (T : ℕ) (c : Cell) : Bool :=
  decide (c.2.2.1 ≠ c.2.2.2) && decide (c.2.2.1.length = T) && decide (c.2.2.2.length = T) &&
    iok l0 l1 a b c.2.2.1 c.1 c.2.1 && iok l0 l1 a b c.2.2.2 c.1 c.2.1

/-- Every point strictly above the left end lies in one of a chained list of
cells. -/
lemma exists_cell_lt {β : Type} {a b : ℚ} {cs : List (ℚ × ℚ × β)} (h : chained a cs b = true)
    {x : ℝ} (hxa : ((a : ℚ) : ℝ) < x) (hxb : x ≤ ((b : ℚ) : ℝ)) :
    ∃ c ∈ cs, ((c.1 : ℚ) : ℝ) ≤ x ∧ x ≤ ((c.2.1 : ℚ) : ℝ) := by
  induction cs generalizing a with
  | nil =>
      simp only [chained, decide_eq_true_eq] at h
      have : ((b : ℚ) : ℝ) ≤ ((a : ℚ) : ℝ) := by exact_mod_cast h
      linarith
  | cons c rest ih =>
      simp only [chained, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨hc, hrest⟩ := h
      subst hc
      by_cases hx : x ≤ ((c.2.1 : ℚ) : ℝ)
      · exact ⟨c, List.mem_cons_self, le_of_lt hxa, hx⟩
      · push_neg at hx
        obtain ⟨c', hc', h1, h2⟩ := ih hrest hx
        exact ⟨c', List.mem_cons_of_mem _ hc', h1, h2⟩

/-- Every point of `[a,b]` lies in one of a nonempty chained list of cells. -/
lemma exists_cell {β : Type} {a b : ℚ} {cs : List (ℚ × ℚ × β)} (h : chained a cs b = true)
    (hne : cs ≠ []) {x : ℝ} (hxa : ((a : ℚ) : ℝ) ≤ x) (hxb : x ≤ ((b : ℚ) : ℝ)) :
    ∃ c ∈ cs, ((c.1 : ℚ) : ℝ) ≤ x ∧ x ≤ ((c.2.1 : ℚ) : ℝ) := by
  match cs, hne with
  | c :: rest, _ =>
      simp only [chained, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨hc, hrest⟩ := h
      subst hc
      by_cases hx : x ≤ ((c.2.1 : ℚ) : ℝ)
      · exact ⟨c, List.mem_cons_self, hxa, hx⟩
      · push_neg at hx
        obtain ⟨c', hc', h1, h2⟩ := exists_cell_lt hrest hx hxb
        exact ⟨c', List.mem_cons_of_mem _ hc', h1, h2⟩

/-- **A certificate yields the doubling property**, for every parameter in the
certified interval. -/
theorem doubling_of_cert {l0 l1 a b : ℚ} {T : ℕ} {cs : List Cell} {lam : ℝ}
    (hl0 : (0:ℚ) < l0) (hlam0 : ((l0 : ℚ) : ℝ) ≤ lam) (hlam1 : lam ≤ ((l1 : ℚ) : ℝ))
    (hch : chained a cs b = true) (hne : cs ≠ []) (hall : cs.all (cellOK l0 l1 a b T) = true) :
    Doubling lam ((a : ℚ) : ℝ) ((b : ℚ) : ℝ) T := by
  intro x hxa hxb
  obtain ⟨c, hc, hp, hq⟩ := exists_cell hch hne hxa hxb
  have hok : cellOK l0 l1 a b T c = true := (List.all_eq_true.1 hall) c hc
  simp only [cellOK, Bool.and_eq_true, decide_eq_true_eq, ne_eq] at hok
  obtain ⟨⟨⟨⟨hne, hlu⟩, hlv⟩, hu⟩, hv⟩ := hok
  have hl0' : (0:ℝ) < ((l0 : ℚ) : ℝ) := by exact_mod_cast hl0
  obtain ⟨hu1, hu2⟩ := rapp_mem_of_iok hlam0 hlam1 hl0' c.2.2.1 c.1 c.2.1 x hp hq hu
  obtain ⟨hv1, hv2⟩ := rapp_mem_of_iok hlam0 hlam1 hl0' c.2.2.2 c.1 c.2.1 x hp hq hv
  exact ⟨c.2.2.1, c.2.2.2, hne, hlu, hlv, hu1, hu2, hv1, hv2⟩

end ExpCert
end KnotGame
