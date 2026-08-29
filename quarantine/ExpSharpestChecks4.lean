import RequestProject.ExpSharpestChecks0

/-!
# Kernel checks at length 16, part 4 (round 10, T31)

Every check below is a kernel reduction over exact rationals
(`decide +kernel`).  The certificate is checked group by group — 41 groups of
at most 50 cells — spread over 9 files, since the kernel's working set
for all of them in one file does not fit in memory.  This file checks groups
20–24; the conclusions are in `RequestProject.ExpSharpest`.
-/

namespace KnotGame
namespace ExpSharpest

open KnotGame.ExpCert KnotGame.ExpMultiCert

set_option maxHeartbeats 4000000

lemma cellsG20_ok : cellsG20.all P = true := by decide +kernel
lemma cellsG21_ok : cellsG21.all P = true := by decide +kernel
lemma cellsG22_ok : cellsG22.all P = true := by decide +kernel
lemma cellsG23_ok : cellsG23.all P = true := by decide +kernel
lemma cellsG24_ok : cellsG24.all P = true := by decide +kernel

end ExpSharpest
end KnotGame
