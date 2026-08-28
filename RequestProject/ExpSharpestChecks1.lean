import RequestProject.ExpSharpestChecks0

/-!
# Kernel checks at length 16, part 1 (round 10, T31)

Every check below is a kernel reduction over exact rationals
(`decide +kernel`).  The certificate is checked group by group — 41 groups of
at most 50 cells — spread over 9 files, since the kernel's working set
for all of them in one file does not fit in memory.  This file checks groups
5–9; the conclusions are in `RequestProject.ExpSharpest`.
-/

namespace KnotGame
namespace ExpSharpest

open KnotGame.ExpCert KnotGame.ExpMultiCert

set_option maxHeartbeats 4000000

lemma cellsG5_ok : cellsG5.all P = true := by decide +kernel
lemma cellsG6_ok : cellsG6.all P = true := by decide +kernel
lemma cellsG7_ok : cellsG7.all P = true := by decide +kernel
lemma cellsG8_ok : cellsG8.all P = true := by decide +kernel
lemma cellsG9_ok : cellsG9.all P = true := by decide +kernel

end ExpSharpest
end KnotGame
