import RequestProject.ExpSharpestChecks0

/-!
# Kernel checks at length 16, part 2 (round 10, T31)

Every check below is a kernel reduction over exact rationals
(`decide +kernel`).  The certificate is checked group by group — 41 groups of
at most 50 cells — spread over 9 files, since the kernel's working set
for all of them in one file does not fit in memory.  This file checks groups
10–14; the conclusions are in `RequestProject.ExpSharpest`.
-/

namespace KnotGame
namespace ExpSharpest

open KnotGame.ExpCert KnotGame.ExpMultiCert

set_option maxHeartbeats 4000000

lemma cellsG10_ok : cellsG10.all P = true := by decide +kernel
lemma cellsG11_ok : cellsG11.all P = true := by decide +kernel
lemma cellsG12_ok : cellsG12.all P = true := by decide +kernel
lemma cellsG13_ok : cellsG13.all P = true := by decide +kernel
lemma cellsG14_ok : cellsG14.all P = true := by decide +kernel

end ExpSharpest
end KnotGame
