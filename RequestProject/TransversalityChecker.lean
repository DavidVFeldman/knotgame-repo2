import RequestProject.TransversalityBounds

/-!
# The verified branch-and-bound checker (round 3, Target T9)

A *cell* is a rational interval `[an/Q, bn/Q]`.  For a cell the checker runs a
breadth-first branch and bound over the coefficient prefixes `c 1, …, c Dep`,
each state carrying the value of the truncation and of its derivative at the
midpoint of the cell, and prunes a state as soon as the centered-form bounds of
`TransversalityBounds` show that no completion of the prefix can violate
transversality anywhere in the cell.  If the search runs out of states the cell
is certified.

All the arithmetic is on natural numbers:

* `x`-values have denominator `Qn`;
* bound quantities have denominator `Scn`, always rounded **up** (`cdiv`);
* the powers `XGS`, `XPS` of the midpoint have denominator `Scn`, rounded
  **down**, the resulting error being absorbed by the slacks `SLA`, `SLB`;
* the two node coordinates are shifted by `OFF` so that they stay natural.

`cellOK an bn = true` is a decidable statement about naturals; `cell_sound`
turns it into the transversality statement on `[an/Qn, bn/Qn]`.
-/

namespace KnotGame
namespace Transversality

open Finset

/-! ### The arithmetic of the checker -/

/-- Truncation depth. -/
def Dep : ℕ := 48
/-- Common denominator of the cell endpoints. -/
def Qn : ℕ := 1024000000
/-- Scale of all bound quantities. -/
def Scn : ℕ := 10 ^ 18
/-- `δ = 1/1000` at scale `Scn`. -/
def deltaS : ℕ := 10 ^ 15
/-- Shift keeping the node coordinates natural. -/
def OFF : ℕ := 10 ^ 25
/-- Cap on the thresholds, verified by the certificate; it keeps the shifted
node coordinates away from `0`. -/
def TCAP : ℕ := 10 ^ 23
/-- Slack absorbing the rounding of the powers in the value coordinate. -/
def SLA : ℕ := 4 * (Dep + 1)
/-- Slack absorbing the rounding of the powers in the derivative coordinate. -/
def SLB : ℕ := 4 * (Dep + 1) * (Dep + 1)

/-- Ceiling division on naturals. -/
def cdiv (x d : ℕ) : ℕ := (x + d - 1) / d

/-- Upper bound for `b ^ i` at scale `Scn`, where `b = bn / Qn`. -/
def BP (bn : ℕ) : ℕ → ℕ
  | 0 => Scn
  | i + 1 => cdiv (BP bn i * bn) Qn

/-- Upper bound for `∑_{j ≤ i} j b^{j-1}` at scale `Scn`. -/
def DS (bn : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => DS bn i + (i + 1) * BP bn i

/-- Upper bound for `∑_{j ≤ i} j (j-1) b^{j-2}` at scale `Scn`. -/
def DD (bn : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => DD bn i + (i + 1) * i * BP bn (i - 1)

/-- Threshold for the value coordinate at depth `i`: `δ` plus the variation of
the truncation over the cell plus the tail beyond depth `i`. -/
def TAn (an bn : ℕ) (i : ℕ) : ℕ :=
  deltaS + cdiv (DS bn i * (bn - an)) (2 * Qn) + cdiv (BP bn (i + 1) * Qn) (Qn - bn) + SLA

/-- Threshold for the derivative coordinate at depth `i`. -/
def TBn (an bn : ℕ) (i : ℕ) : ℕ :=
  deltaS + cdiv (DD bn i * (bn - an)) (2 * Qn)
    + cdiv ((i + 1) * BP bn i * Qn * Qn) ((Qn - bn) * (Qn - bn)) + SLB

/-- `m ^ i` at scale `Scn`, rounded down. -/
def XGS (mn : ℕ) : ℕ → ℕ
  | 0 => Scn
  | i + 1 => XGS mn i * mn / Qn

/-- `i * m ^ (i-1)` at scale `Scn`, rounded down. -/
def XPS (mn : ℕ) (i : ℕ) : ℕ := i * XGS mn (i - 1)

/-- The pruning test at a node. -/
def keep (loa hia lob : ℕ) (s : ℕ × ℕ) : Bool :=
  loa ≤ s.1 && s.1 ≤ hia && lob ≤ s.2

def push (loa hia lob : ℕ) (s : ℕ × ℕ) (acc : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  if keep loa hia lob s then s :: acc else acc

/-- The three children of every state of a layer, pruned. -/
def expand (xg xp loa hia lob : ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | s :: rest =>
      push loa hia lob (s.1 - xg, s.2 - xp)
        (push loa hia lob s
          (push loa hia lob (s.1 + xg, s.2 + xp) (expand xg xp loa hia lob rest)))

/-- The surviving states after choosing the coefficients `c 1, …, c i`. -/
def layer (an bn mn : ℕ) : ℕ → List (ℕ × ℕ)
  | 0 => push (OFF - TAn an bn 0) (OFF + TAn an bn 0) (OFF - TBn an bn 0) (OFF + Scn, OFF) []
  | i + 1 =>
      expand (XGS mn (i + 1)) (XPS mn (i + 1))
        (OFF - TAn an bn (i+1)) (OFF + TAn an bn (i+1)) (OFF - TBn an bn (i+1))
        (layer an bn mn i)

/-- The thresholds stay below `TCAP` up to depth `i`. -/
def capOK (an bn : ℕ) : ℕ → Bool
  | 0 => (TAn an bn 0 ≤ TCAP) && (TBn an bn 0 ≤ TCAP)
  | i + 1 => capOK an bn i && (TAn an bn (i+1) ≤ TCAP) && (TBn an bn (i+1) ≤ TCAP)

/-- The certificate for one cell. -/
def cellOK (an bn : ℕ) : Bool :=
  capOK an bn Dep && (layer an bn ((an + bn) / 2) Dep).isEmpty

end Transversality
end KnotGame
