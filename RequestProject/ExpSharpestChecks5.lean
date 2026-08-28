import RequestProject.ExpSharpestChecks0

/-!
# Kernel checks at length 16, part 5 (round 10, T31)

Every check below is a kernel reduction over exact rationals
(`decide +kernel`).  The certificate is checked group by group — 41 groups of
at most 50 cells — spread over 9 files, since the kernel's working set
for all of them in one file does not fit in memory.  This file checks groups
25–29; the conclusions are in `RequestProject.ExpSharpest`.
-/

namespace KnotGame
namespace ExpSharpest

open KnotGame.ExpCert KnotGame.ExpMultiCert

set_option maxHeartbeats 4000000

lemma cellsG25_ok : cellsG25.all P = true := by decide +kernel
lemma cellsG26_ok : cellsG26.all P = true := by decide +kernel
lemma cellsG27_ok : cellsG27.all P = true := by decide +kernel
lemma cellsG28_ok : cellsG28.all P = true := by decide +kernel
lemma cellsG29_ok : cellsG29.all P = true := by decide +kernel

end ExpSharpest
end KnotGame
