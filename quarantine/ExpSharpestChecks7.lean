import RequestProject.ExpSharpestChecks0

/-!
# Kernel checks at length 16, part 7 (round 10, T31)

Every check below is a kernel reduction over exact rationals
(`decide +kernel`).  The certificate is checked group by group — 41 groups of
at most 50 cells — spread over 9 files, since the kernel's working set
for all of them in one file does not fit in memory.  This file checks groups
35–39; the conclusions are in `RequestProject.ExpSharpest`.
-/

namespace KnotGame
namespace ExpSharpest

open KnotGame.ExpCert KnotGame.ExpMultiCert

set_option maxHeartbeats 4000000

lemma cellsG35_ok : cellsG35.all P = true := by decide +kernel
lemma cellsG36_ok : cellsG36.all P = true := by decide +kernel
lemma cellsG37_ok : cellsG37.all P = true := by decide +kernel
lemma cellsG38_ok : cellsG38.all P = true := by decide +kernel
lemma cellsG39_ok : cellsG39.all P = true := by decide +kernel

end ExpSharpest
end KnotGame
