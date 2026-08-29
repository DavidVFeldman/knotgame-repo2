import RequestProject.ExpSharpestData

/-!
# Kernel checks at length 16, part 0 (round 10, T31)

Every check below is a kernel reduction over exact rationals
(`decide +kernel`).  The certificate is checked group by group — 41 groups of
at most 50 cells — spread over 9 files, since the kernel's working set
for all of them in one file does not fit in memory.  This file checks groups
0–4; the conclusions are in `RequestProject.ExpSharpest`.
-/

namespace KnotGame
namespace ExpSharpest

open KnotGame.ExpCert KnotGame.ExpMultiCert

set_option maxHeartbeats 4000000

/-- The check of one group of cells: `49` distinct words of length `16` per
cell, each with its enclosure inside `J = [1/6, 5/6]`.  The kernel runs one
group at a time. -/
abbrev P : MCell → Bool := mcellOK (3/2) (3/2) (1/6) (5/6) 16 49

lemma cellsG0_ok : cellsG0.all P = true := by decide +kernel
lemma cellsG1_ok : cellsG1.all P = true := by decide +kernel
lemma cellsG2_ok : cellsG2.all P = true := by decide +kernel
lemma cellsG3_ok : cellsG3.all P = true := by decide +kernel
lemma cellsG4_ok : cellsG4.all P = true := by decide +kernel

end ExpSharpest
end KnotGame
