import RequestProject.ExpSharpestChecks0

/-!
# Kernel checks at length 16, part 6 (round 10, T31)

Every check below is a kernel reduction over exact rationals
(`decide +kernel`).  The certificate is checked group by group — 41 groups of
at most 50 cells — spread over 9 files, since the kernel's working set
for all of them in one file does not fit in memory.  This file checks groups
30–34; the conclusions are in `RequestProject.ExpSharpest`.
-/

namespace KnotGame
namespace ExpSharpest

open KnotGame.ExpCert KnotGame.ExpMultiCert

set_option maxHeartbeats 4000000

lemma cellsG30_ok : cellsG30.all P = true := by decide +kernel
lemma cellsG31_ok : cellsG31.all P = true := by decide +kernel
lemma cellsG32_ok : cellsG32.all P = true := by decide +kernel
lemma cellsG33_ok : cellsG33.all P = true := by decide +kernel
lemma cellsG34_ok : cellsG34.all P = true := by decide +kernel

end ExpSharpest
end KnotGame
