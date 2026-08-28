import RequestProject.PlasticOrbit

/-! Prototype (not part of the library): the index model of the plastic game and
a kernel BFS over its configurations.  Used only to measure feasibility. -/

namespace KnotGame
namespace Plastic
namespace Proto

def tabL : ℕ := 171056735807690813158204043027096063117823792939589782407190498882094804196684560109697704812219969809878965280427119476230116787853925094057711547396344022237304133198271482418090456866214403214303098389081284245680005335449185070084434135948613816110420505742780952882874500925302037696564924024950129259355089229527500094027877515435717160957588186308421626974175231

def tabM : ℕ := 171056735807690813158204043027096063117823792939589782407190498882094804196684560109697704812219969809878965280427119476230116787853925094061968791442788097996213042809060419290900012167758304409433320024857898999623341739072374766867490930247231286174404088190874128191572005682919522501675980705118723683600313451217024624203679068632389131358086327993137409535705601

def tabR : ℕ := 288878149031346317441449898160257412877284850718137687733941608447907569136952074473685387937855203874463210323106590926941063634499150493722986231349017905573328364153930698346593479896178159433542037095240295292727168663669627640369498979092486053592098226686136996275178217074670687912311030344412589571798672530070215681851737034958949051279163572853132067179004417

def tabOf : Move → ℕ
  | Move.L => tabL
  | Move.M => tabM
  | Move.R => tabR

def tget (T i : ℕ) : ℕ := (T >>> (8 * i)) % 256

def halfIdx : ℕ := 76

def insNat (x : ℕ) : List ℕ → List ℕ
  | [] => [x]
  | y :: c => if x = y then y :: c else if x < y then x :: y :: c else y :: insNat x c

def stepIdx (m : Move) (c : List ℕ) : List ℕ :=
  let c' := c.foldr (fun i acc =>
      let v := tget (tabOf m) i
      if v = 255 then acc else insNat v acc) []
  if m = Move.M then insNat halfIdx c' else c'

inductive Tbl where
  | leaf : Tbl
  | node : List ℕ → Tbl → Tbl → Tbl

def cfgLt : List ℕ → List ℕ → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: x, b :: y => if a < b then true else if b < a then false else cfgLt x y

def Tbl.find (c : List ℕ) : Tbl → Bool
  | .leaf => false
  | .node d l r => if c = d then true else if cfgLt c d then l.find c else r.find c

def Tbl.ins (c : List ℕ) : Tbl → Tbl
  | .leaf => .node c .leaf .leaf
  | .node d l r => if c = d then .node d l r
      else if cfgLt c d then .node d (l.ins c) r else .node d l (r.ins c)

def Tbl.toListAux : Tbl → List (List ℕ) → List (List ℕ)
  | .leaf, acc => acc
  | .node c l r, acc => l.toListAux (c :: r.toListAux acc)

def Tbl.toList (t : Tbl) : List (List ℕ) := t.toListAux []

def Tbl.sizeAux : Tbl → ℕ → ℕ
  | .leaf, n => n
  | .node _ l r, n => l.sizeAux (r.sizeAux (n + 1))

def Tbl.size (t : Tbl) : ℕ := t.sizeAux 0

def expand (m : Move) (c : List ℕ) (st : Tbl × List (List ℕ)) : Tbl × List (List ℕ) :=
  let d := stepIdx m c
  if st.1.find d then st else (st.1.ins d, d :: st.2)

def bfsRound (st : Tbl × List (List ℕ)) : Tbl × List (List ℕ) :=
  st.2.foldl (fun acc c => expand Move.R c (expand Move.M c (expand Move.L c acc)))
    (st.1, [])

def bfs : ℕ → Tbl × List (List ℕ)
  | 0 => (Tbl.leaf.ins [], [[]])
  | n + 1 => bfsRound (bfs n)

def visited (n : ℕ) : Tbl := (bfs n).1

def maxLen (l : List (List ℕ)) : ℕ := l.foldl (fun n c => max n c.length) 0

/-- The layers: configurations reachable in exactly `n` moves. -/
def layerTbl : ℕ → Tbl
  | 0 => Tbl.leaf.ins []
  | n + 1 => (layerTbl n).toList.foldl
      (fun t c => ((t.ins (stepIdx Move.L c)).ins (stepIdx Move.M c)).ins (stepIdx Move.R c))
      Tbl.leaf

#eval (visited 5).size
#eval (visited 12).size
#eval (bfs 30).2.length          -- frontier should be empty once closed
#eval (visited 30).size          -- expect 25525
#eval maxLen (visited 30).toList -- expect 7
#eval (List.range 8).map (fun n => maxLen (layerTbl n).toList)

end Proto
end Plastic
end KnotGame
