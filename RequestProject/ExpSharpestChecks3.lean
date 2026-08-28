import RequestProject.ExpSharpestChecks0

/-!
# Kernel checks at length 16, part 3 (round 10, T31)

Every check below is a kernel reduction over exact rationals
(`decide +kernel`).  The certificate is checked group by group — 41 groups of
at most 50 cells — spread over 9 files, since the kernel's working set
for all of them in one file does not fit in memory.  This file checks groups
15–19; the conclusions are in `RequestProject.ExpSharpest`.
-/

namespace KnotGame
namespace ExpSharpest

open KnotGame.ExpCert KnotGame.ExpMultiCert

set_option maxHeartbeats 4000000

lemma cellsG15_ok : cellsG15.all P = true := by decide +kernel
lemma cellsG16_ok : cellsG16.all P = true := by decide +kernel
lemma cellsG17_ok : cellsG17.all P = true := by decide +kernel
lemma cellsG18_ok : cellsG18.all P = true := by decide +kernel
lemma cellsG19_ok : cellsG19.all P = true := by decide +kernel

end ExpSharpest
end KnotGame
