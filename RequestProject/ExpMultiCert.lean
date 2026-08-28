import RequestProject.ExpCert
import RequestProject.ExpMulti

/-!
# Certificates at higher multiplicity (round 7)

The same interval-arithmetic certificates as in `RequestProject.ExpCert`, but
each cell now carries a list of `k` words instead of exactly two, and the
conclusion is `MDoubling lam a b T k` rather than `Doubling lam a b T`.  The
checker `iok` and the covering lemmas `chained`, `exists_cell` are reused
unchanged.

## Conventions (SCRUPLES)

* Distinctness of the `k` words is checked as `List.Nodup` of the cell's word
  list, and the number of words as `length = k`; the `Finset` of `MDoubling` is
  the list's `toFinset`, whose cardinality is then `k`.
-/

namespace KnotGame
namespace ExpMultiCert

open KnotGame.Branching KnotGame.ExpCount KnotGame.ExpCert KnotGame.ExpMulti

/-- A cell of a multiplicity certificate: an interval `[p,q]` and a list of
branch words. -/
abbrev MCell := ℚ × ℚ × List (List (Fin 2))

/-- A cell is valid: `k` distinct words of length `T` whose enclosures over the
cell, for every parameter in `[l0,l1]`, lie inside `[a,b]`. -/
def mcellOK (l0 l1 a b : ℚ) (T k : ℕ) (c : MCell) : Bool :=
  decide (c.2.2.length = k) && decide (c.2.2.Nodup) &&
    c.2.2.all (fun w => decide (w.length = T) && iok l0 l1 a b w c.1 c.2.1)

/-- **A multiplicity certificate yields `MDoubling`**, for every parameter in the
certified interval. -/
theorem mdoubling_of_cert {l0 l1 a b : ℚ} {T k : ℕ} {cs : List MCell} {lam : ℝ}
    (hl0 : (0:ℚ) < l0) (hlam0 : ((l0 : ℚ) : ℝ) ≤ lam) (hlam1 : lam ≤ ((l1 : ℚ) : ℝ))
    (hch : chained a cs b = true) (hne : cs ≠ []) (hall : cs.all (mcellOK l0 l1 a b T k) = true) :
    MDoubling lam ((a : ℚ) : ℝ) ((b : ℚ) : ℝ) T k := by
  intro x hxa hxb
  obtain ⟨c, hc, hp, hq⟩ := exists_cell hch hne hxa hxb
  have hok : mcellOK l0 l1 a b T k c = true := (List.all_eq_true.1 hall) c hc
  simp only [mcellOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hlen, hnd⟩, hwords⟩ := hok
  have hl0' : (0:ℝ) < ((l0 : ℚ) : ℝ) := by exact_mod_cast hl0
  refine ⟨c.2.2.toFinset, ?_, ?_⟩
  · rw [List.toFinset_card_of_nodup hnd, hlen]
  · intro w hw
    rw [List.mem_toFinset] at hw
    have hwok := (List.all_eq_true.1 hwords) w hw
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hwok
    obtain ⟨hwlen, hiok⟩ := hwok
    obtain ⟨h1, h2⟩ := rapp_mem_of_iok hlam0 hlam1 hl0' w c.1 c.2.1 x hp hq hiok
    exact ⟨hwlen, h1, h2⟩

end ExpMultiCert
end KnotGame
