import RequestProject.TransversalityChecker

/-!
# The 27-cell certificate for the window `[1/2, 667/1000]` (round 3, Target T9)

Each lemma below is the statement that the branch-and-bound search of
`RequestProject.TransversalityChecker` empties for one cell, and is discharged
by kernel reduction (`decide +kernel`); no `native_decide` is used.  The cells
were found by `scripts/bnb_lean.py`, an exact integer replica of the checker;
that script is only a search aid, the certificate itself being re-checked here
by the kernel.  Together the cells tile `[512000000/Qn, 683008000/Qn]`, that is
`[1/2, 667/1000]`; the search visits 164823 nodes in total.
-/

namespace KnotGame
namespace Transversality

set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000

lemma cell_01 : cellOK 512000000 597504000 = true := by decide +kernel

lemma cell_02 : cellOK 597504000 618880000 = true := by decide +kernel

lemma cell_03 : cellOK 618880000 640256000 = true := by decide +kernel

lemma cell_04 : cellOK 640256000 650944000 = true := by decide +kernel

lemma cell_05 : cellOK 650944000 656288000 = true := by decide +kernel

lemma cell_06 : cellOK 656288000 661632000 = true := by decide +kernel

lemma cell_07 : cellOK 661632000 664304000 = true := by decide +kernel

lemma cell_08 : cellOK 664304000 666976000 = true := by decide +kernel

lemma cell_09 : cellOK 666976000 669648000 = true := by decide +kernel

lemma cell_10 : cellOK 669648000 672320000 = true := by decide +kernel

lemma cell_11 : cellOK 672320000 674992000 = true := by decide +kernel

lemma cell_12 : cellOK 674992000 676328000 = true := by decide +kernel

lemma cell_13 : cellOK 676328000 677664000 = true := by decide +kernel

lemma cell_14 : cellOK 677664000 679000000 = true := by decide +kernel

lemma cell_15 : cellOK 679000000 679664000 = true := by decide +kernel

lemma cell_16 : cellOK 679664000 680336000 = true := by decide +kernel

lemma cell_17 : cellOK 680336000 681000000 = true := by decide +kernel

lemma cell_18 : cellOK 681000000 681336000 = true := by decide +kernel

lemma cell_19 : cellOK 681336000 681672000 = true := by decide +kernel

lemma cell_20 : cellOK 681672000 682000000 = true := by decide +kernel

lemma cell_21 : cellOK 682000000 682168000 = true := by decide +kernel

lemma cell_22 : cellOK 682168000 682336000 = true := by decide +kernel

lemma cell_23 : cellOK 682336000 682504000 = true := by decide +kernel

lemma cell_24 : cellOK 682504000 682672000 = true := by decide +kernel

lemma cell_25 : cellOK 682672000 682840000 = true := by decide +kernel

lemma cell_26 : cellOK 682840000 682920000 = true := by decide +kernel

lemma cell_27 : cellOK 682920000 683008000 = true := by decide +kernel

/-- The cells of the certified decomposition of `[1/2, 667/1000]`. -/
def cells : List (ℕ × ℕ) :=
  [(512000000, 597504000),
   (597504000, 618880000),
   (618880000, 640256000),
   (640256000, 650944000),
   (650944000, 656288000),
   (656288000, 661632000),
   (661632000, 664304000),
   (664304000, 666976000),
   (666976000, 669648000),
   (669648000, 672320000),
   (672320000, 674992000),
   (674992000, 676328000),
   (676328000, 677664000),
   (677664000, 679000000),
   (679000000, 679664000),
   (679664000, 680336000),
   (680336000, 681000000),
   (681000000, 681336000),
   (681336000, 681672000),
   (681672000, 682000000),
   (682000000, 682168000),
   (682168000, 682336000),
   (682336000, 682504000),
   (682504000, 682672000),
   (682672000, 682840000),
   (682840000, 682920000),
   (682920000, 683008000)]

/-- Every cell of the decomposition carries a certificate. -/
lemma cells_ok : ∀ p ∈ cells, cellOK p.1 p.2 = true := by
  intro p hp
  fin_cases hp
  exacts [cell_01, cell_02, cell_03, cell_04, cell_05, cell_06, cell_07, cell_08, cell_09, cell_10, cell_11, cell_12, cell_13, cell_14, cell_15, cell_16, cell_17, cell_18, cell_19, cell_20, cell_21, cell_22, cell_23, cell_24, cell_25, cell_26, cell_27]

/-- Every cell is a nondegenerate subinterval of the window with an even
endpoint sum, so that its midpoint is exact. -/
lemma cells_wf : ∀ p ∈ cells, p.1 ≤ p.2 ∧ 4 * p.2 ≤ 3 * Qn ∧ (p.1 + p.2) % 2 = 0 := by
  decide +kernel

end Transversality
end KnotGame
