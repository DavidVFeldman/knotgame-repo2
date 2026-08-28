"""Generate `RequestProject/Supergolden.lean` from the exact orbit computation.

The data (43 orbit points over Z[lam] with denominator 2, the three transition
tables, the 412 reachable configurations with their exact first-attainment
depths) come from `scripts/supergolden.py`, which works with a rational
bracket for lam and never with floating point.  The generated Lean file
re-derives everything from scratch inside Lean: the orbit points are named,
their transitions are proved, and the configuration data are re-checked by the
kernel.
"""
import re
import ast
import subprocess
from collections import deque

out = subprocess.run(['python3', 'scripts/supergolden.py'],
                     capture_output=True, text=True).stdout
TL = ast.literal_eval(re.search(r"^TL (\[.*\])$", out, re.M).group(1))
TR = ast.literal_eval(re.search(r"^TR (\[.*\])$", out, re.M).group(1))
TM = ast.literal_eval(re.search(r"^TM (\[.*\])$", out, re.M).group(1))
pts = []
for line in out.splitlines():
    m = re.match(r"^(\d+) \((-?\d+), (-?\d+), (-?\d+)\) ", line)
    if m:
        pts.append((int(m.group(2)), int(m.group(3)), int(m.group(4))))
n = len(pts)
assert n == 43
HALF = 21
assert pts[HALF] == (1, 0, 0)

# breadth-first search over configurations, as bitmasks, recording depths
def stepmask(mask, tab, add):
    m = 0
    for i in range(n):
        if mask >> i & 1 and tab[i] >= 0:
            m |= 1 << tab[i]
    return m | add

depth = {0: 0}
q = deque([0])
while q:
    s = q.popleft()
    for t in (stepmask(s, TL, 0), stepmask(s, TR, 0),
              stepmask(s, TM, 1 << HALF)):
        if t not in depth:
            depth[t] = depth[s] + 1
            q.append(t)
cfgs = sorted(depth, key=lambda s: (depth[s], s))
MAXD = max(depth.values())
card = lambda s: bin(s).count('1')
assert max(card(s) for s in cfgs) == 4
for k, dk in ((1, 1), (2, 3), (3, 5), (4, 11)):
    assert min(depth[s] for s in cfgs if card(s) >= k) == dk


def bits(s):
    return [i for i in range(n) if s >> i & 1]


def vecB(t):
    return "![" + ", ".join("true" if v >= 0 else "false" for v in t) + "]"


def vecA(t):
    return "![" + ", ".join(str(v if v >= 0 else 0) for v in t) + "]"


def point(t):
    A, B, C = t
    parts = []
    for co, s in ((A, ""), (B, "lam"), (C, "lam^2")):
        if co == 0:
            continue
        if abs(co) == 1 and s:
            mono = s
        elif s:
            mono = str(abs(co)) + "*" + s
        else:
            mono = str(abs(co))
        if not parts:
            parts.append(("-" if co < 0 else "") + mono)
        else:
            parts.append((" - " if co < 0 else " + ") + mono)
    body = "".join(parts) if parts else "0"
    return "(" + body + ")/2"


def fset(s):
    b = bits(s)
    if not b:
        return "(∅, %d)" % depth[s]
    return "({" + ",".join(str(i) for i in b) + "}, %d)" % depth[s]


reachD = ",\n   ".join(fset(s) for s in cfgs)
pvec = ",\n    ".join(point(t) for t in pts)

# the words realising the four depths
words = {1: "M", 2: "MLM", 3: "MLMLM", 4: "MLMLRRRLMRM"}
def word(w):
    return "![" + ", ".join("Move." + ch for ch in w) + "]"

src = f'''import RequestProject.Golden

/-!
# The supergolden parameter (round 3, Target T8)

The supergolden ratio `lam` is the real root of `x³ = x² + 1`
(`lam ≈ 1.4655712319`).  It is a Pisot number, so Theorem 3.1 already gives
that the orbit of `1/2` is finite; this file computes that orbit exactly and
runs the round-1 golden-ratio argument at the new parameter:

* the orbit of `1/2` has **{n}** points, listed in increasing order in `p`;
* the transition tables `absSurv`, `absAct` describe the game on those points;
* exactly **{len(cfgs)}** configurations are reachable, all of card `≤ 4`;
* the maximum is attained: `sup N = 4`;
* the first attainment depths are `d 1 = 1`, `d 2 = 3`, `d 3 = 5`, `d 4 = 11`.

Points are written over `ℤ[lam]` with denominator `2`, exactly as in
`Tribonacci` and `PlasticOrbit`.  The orbit here is far larger, so the
configuration data are handled differently: the {len(cfgs)} reachable
configurations are stored **with their exact first-attainment depth** in
`reachD`, and a single boolean check `checkOK`, discharged by kernel reduction,
verifies at once that

* the list is closed under the three moves (the depth of a successor is at most
  one more than the depth of its predecessor, and in particular is finite),
* every configuration has at most four knots, and
* a configuration with `k` knots has depth at least `d k` (`1, 3, 5, 11`).

Everything about the game then follows from that one check.  Storing the
depths, rather than iterating a layer construction inside Lean, is what keeps
the kernel computation to a single pass over the list.
-/

namespace KnotGame
namespace Supergolden

set_option maxRecDepth 10000000
set_option maxHeartbeats 4000000

open Finset

/-! ### The supergolden number -/

private lemma exists_root : ∃ x : ℝ, x ∈ Set.Ioo (1:ℝ) 2 ∧ x ^ 3 - x ^ 2 - 1 = 0 := by
  have hcont : ContinuousOn (fun x : ℝ => x ^ 3 - x ^ 2 - 1) (Set.Icc 1 2) :=
    (Continuous.continuousOn (by continuity))
  have h0 : (0:ℝ) ∈ Set.Ioo ((1:ℝ) ^ 3 - 1 ^ 2 - 1) ((2:ℝ) ^ 3 - 2 ^ 2 - 1) := by
    constructor <;> norm_num
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Ioo (by norm_num : (1:ℝ) ≤ 2) hcont h0
  exact ⟨x, hx, hfx⟩

/-- The **supergolden ratio**: the real root of `x³ = x² + 1`. -/
noncomputable def lam : ℝ := Classical.choose exists_root

lemma lam_mem : lam ∈ Set.Ioo (1:ℝ) 2 := (Classical.choose_spec exists_root).1

lemma lam_cubic : lam ^ 3 - lam ^ 2 - 1 = 0 := (Classical.choose_spec exists_root).2

lemma one_lt_lam : 1 < lam := lam_mem.1

lemma lam_lt_two : lam < 2 := lam_mem.2

lemma lam_cube : lam ^ 3 = lam ^ 2 + 1 := by linarith [lam_cubic]

lemma lam_gt : (1.4655712 : ℝ) < lam := by
  nlinarith [lam_cubic, lam_mem.1, lam_mem.2, sq_nonneg (lam - 1.4655712),
    sq_nonneg (lam + 1.4655712)]

lemma lam_lt : lam < 1.4655713 := by
  nlinarith [lam_cubic, lam_mem.1, lam_mem.2, sq_nonneg (lam - 1.4655713),
    sq_nonneg (lam + 1.4655713)]

lemma lam_sq_gt : (2.1478989 : ℝ) < lam ^ 2 := by nlinarith [lam_gt, lam_mem.1]

lemma lam_sq_lt : lam ^ 2 < 2.1478994 := by nlinarith [lam_lt, lam_mem.1]

lemma r_sg : r lam = lam ^ 2 - lam := by
  have h : lam * (lam ^ 2 - lam) = 1 := by linear_combination lam_cubic
  simpa [r] using inv_eq_of_mul_eq_one_right h

lemma g_sg : g lam = 1 + lam - lam ^ 2 := by
  rw [g, r_sg]; ring

/-! ### The {n} orbit points -/

/-- The {n} points of the orbit of `1/2`, in increasing order, as elements
`(A + B·lam + C·lam²)/2` of `ℤ[lam]` with denominator `2`. -/
noncomputable def p : Fin {n} → ℝ :=
  ![{pvec}]

lemma p_strictMono : StrictMono p := by
  have h1 := lam_gt
  have h2 := lam_lt
  have h3 := lam_sq_gt
  have h4 := lam_sq_lt
  refine Fin.strictMono_iff_lt_succ.mpr ?_
  intro i
  fin_cases i <;> simp [p] <;> linarith

lemma p_injective : Function.Injective p := p_strictMono.injective

/-- Which of the orbit points survive which move. -/
def absSurv : Move → Fin {n} → Bool
  | .L => {vecB(TL)}
  | .M => {vecB(TM)}
  | .R => {vecB(TR)}

/-- Where the surviving points go.  The value at a non-surviving point is
irrelevant. -/
def absAct : Move → Fin {n} → Fin {n}
  | .L => {vecA(TL)}
  | .M => {vecA(TM)}
  | .R => {vecA(TR)}

lemma survives_p (m : Move) (i : Fin {n}) : survives lam m (p i) ↔ absSurv m i := by
  have h1 := lam_gt
  have h2 := lam_lt
  have h3 := lam_sq_gt
  have h4 := lam_sq_lt
  fin_cases m <;> fin_cases i <;> simp [absSurv, p, r_sg, g_sg] <;>
    first
      | linarith
      | (left; linarith)
      | (right; linarith)
      | (constructor <;> linarith)

lemma act_p (m : Move) (i : Fin {n}) (hi : absSurv m i) :
    act lam m (p i) = p (absAct m i) := by
  have h1 := lam_gt
  have h2 := lam_lt
  have h3 := lam_sq_gt
  have h4 := lam_sq_lt
  have hc := lam_cube
  fin_cases m <;> fin_cases i <;>
    simp [absSurv, absAct, p, act_L, act_R] at hi ⊢ <;>
    first
      | ring1
      | linear_combination hc/2
      | linear_combination -hc/2
      | linear_combination hc
      | linear_combination -hc
      | linear_combination 3*hc/2
      | linear_combination -3*hc/2
      | linear_combination 2*hc
      | linear_combination -2*hc
      | (rw [act_M_of_lt lam _ (by rw [r_sg]; linarith)];
         first
           | ring1
           | linear_combination hc/2
           | linear_combination -hc/2
           | linear_combination hc
           | linear_combination -hc
           | linear_combination 3*hc/2
           | linear_combination -3*hc/2)
      | (rw [act_M_of_gt lam _ (by rw [r_sg]; push_neg; linarith)];
         first
           | ring1
           | linear_combination hc/2
           | linear_combination -hc/2
           | linear_combination hc
           | linear_combination -hc
           | linear_combination 3*hc/2)

/-! ### The automaton on subsets of the orbit -/

/-- The automaton on subsets of the orbit. -/
def absStep (m : Move) (T : Finset (Fin {n})) : Finset (Fin {n}) :=
  (T.filter (fun i => absSurv m i)).image (absAct m) ∪ (if m = Move.M then {{{HALF}}} else ∅)

/-- One move of the game is the image under `p` of one move of the automaton. -/
lemma step_image (m : Move) (T : Finset (Fin {n})) :
    step lam m (T.image p) = (absStep m T).image p := by
  ext y
  simp only [mem_step, absStep, Finset.mem_image, Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro (⟨x, ⟨i, hi, rfl⟩, hs, rfl⟩ | ⟨hm, rfl⟩)
    · refine ⟨absAct m i, Or.inl ⟨i, ⟨hi, (survives_p m i).mp hs⟩, rfl⟩, ?_⟩
      exact (act_p m i ((survives_p m i).mp hs)).symm
    · refine ⟨{HALF}, Or.inr ?_, rfl⟩
      simp [hm]
  · rintro ⟨j, (⟨i, ⟨hi, hs⟩, rfl⟩ | hj), rfl⟩
    · exact Or.inl ⟨p i, ⟨i, hi, rfl⟩, (survives_p m i).mpr hs, (act_p m i hs)⟩
    · by_cases hm : m = Move.M
      · rw [if_pos hm, Finset.mem_singleton] at hj
        subst hj
        exact Or.inr ⟨hm, rfl⟩
      · rw [if_neg hm] at hj
        exact absurd hj (Finset.notMem_empty _)

noncomputable def absRunFrom (T : Finset (Fin {n})) (w : List Move) : Finset (Fin {n}) :=
  w.foldl (fun T m => absStep m T) T

noncomputable def absRun (w : List Move) : Finset (Fin {n}) := absRunFrom ∅ w

lemma runFrom_eq (T : Finset (Fin {n})) (w : List Move) :
    runFrom lam (T.image p) w = (absRunFrom T w).image p := by
  induction w generalizing T with
  | nil => rfl
  | cons m w ih =>
      rw [runFrom_cons, step_image, ih]
      rfl

lemma run_eq (w : List Move) : run lam w = (absRun w).image p := by
  have : ((∅ : Finset (Fin {n})).image p) = ∅ := by simp
  rw [run, ← this, runFrom_eq, absRun]

lemma card_run_eq (w : List Move) : (run lam w).card = (absRun w).card := by
  rw [run_eq, Finset.card_image_of_injective _ p_injective]

/-! ### The {len(cfgs)} reachable configurations, with their depths -/

/-- The reachable configurations, each tagged with the exact number of moves
after which it first occurs. -/
def reachD : List (Finset (Fin {n}) × ℕ) :=
  [{reachD}]

/-- Lookup in the tagged list; `99` means "absent". -/
def lookupD : List (Finset (Fin {n}) × ℕ) → Finset (Fin {n}) → ℕ
  | [], _ => 99
  | (S, d) :: rest, T => if S = T then d else lookupD rest T

/-- The single boolean check that carries the whole analysis. -/
def checkOK : Bool :=
  reachD.all (fun q =>
    (q.1.card ≤ 4)
    && (lookupD reachD (absStep Move.L q.1) ≤ q.2 + 1)
    && (lookupD reachD (absStep Move.M q.1) ≤ q.2 + 1)
    && (lookupD reachD (absStep Move.R q.1) ≤ q.2 + 1)
    && (lookupD reachD (absStep Move.L q.1) ≤ {MAXD})
    && (lookupD reachD (absStep Move.M q.1) ≤ {MAXD})
    && (lookupD reachD (absStep Move.R q.1) ≤ {MAXD})
    && ((q.1.card ≤ 0) || (1 ≤ q.2))
    && ((q.1.card ≤ 1) || (3 ≤ q.2))
    && ((q.1.card ≤ 2) || (5 ≤ q.2))
    && ((q.1.card ≤ 3) || (11 ≤ q.2)))

theorem checkOK_true : checkOK = true := by decide +kernel

lemma lookupD_empty : lookupD reachD ∅ = 0 := by decide +kernel

/-! ### Consequences of the check -/

lemma lookupD_mem : ∀ (L : List (Finset (Fin {n}) × ℕ)) (T : Finset (Fin {n})),
    lookupD L T ≠ 99 → (T, lookupD L T) ∈ L := by
  intro L
  induction L with
  | nil => intro T h; exact absurd rfl h
  | cons q rest ih =>
      intro T h
      obtain ⟨S, d⟩ := q
      by_cases hs : S = T
      · subst hs
        simp only [lookupD] at h ⊢
        exact List.mem_cons_self ..
      · simp only [lookupD, if_neg hs] at h ⊢
        exact List.mem_cons_of_mem _ (ih T h)

/-- The conjuncts of `checkOK`, for one entry of the list. -/
lemma check_entry {{T : Finset (Fin {n})}} {{d : ℕ}} (h : (T, d) ∈ reachD) :
    T.card ≤ 4 ∧ (∀ m : Move, lookupD reachD (absStep m T) ≤ d + 1)
      ∧ (∀ m : Move, lookupD reachD (absStep m T) ≤ {MAXD})
      ∧ (T.card ≤ 0 ∨ 1 ≤ d) ∧ (T.card ≤ 1 ∨ 3 ≤ d)
      ∧ (T.card ≤ 2 ∨ 5 ≤ d) ∧ (T.card ≤ 3 ∨ 11 ≤ d) := by
  have hall := List.all_eq_true.mp checkOK_true (T, d) h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hall
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := hall
  refine ⟨h1, ?_, ?_, h8, h9, h10, h11⟩
  · intro m; cases m
    · exact h2
    · exact h3
    · exact h4
  · intro m; cases m
    · exact h5
    · exact h6
    · exact h7

/-- The invariant carried along a run: the state is in the list, and its depth
tag is at most the number of moves made. -/
lemma absRunFrom_le (w : List Move) :
    ∀ (T : Finset (Fin {n})) (k : ℕ), lookupD reachD T ≤ k → k ≤ {MAXD} →
      lookupD reachD (absRunFrom T w) ≤ k + w.length ∧
        lookupD reachD (absRunFrom T w) ≤ {MAXD} := by
  induction w with
  | nil => intro T k h hk; exact ⟨by simpa using h, le_trans h hk⟩
  | cons m w ih =>
      intro T k h hk
      have hne : lookupD reachD T ≠ 99 := by omega
      have hmem := lookupD_mem reachD T hne
      obtain ⟨-, hstep, hcap, -⟩ := check_entry hmem
      have h1 : lookupD reachD (absStep m T) ≤ k + 1 :=
        le_trans (hstep m) (by omega)
      have h2 : lookupD reachD (absStep m T) ≤ {MAXD} := hcap m
      have := ih (absStep m T) (min (k+1) {MAXD}) (le_min h1 h2) (min_le_right _ _)
      have hfold : absRunFrom T (m :: w) = absRunFrom (absStep m T) w := rfl
      rw [hfold]
      constructor
      · refine le_trans this.1 ?_
        simp only [List.length_cons]
        omega
      · exact this.2

lemma absRun_le (w : List Move) :
    lookupD reachD (absRun w) ≤ w.length ∧ lookupD reachD (absRun w) ≤ {MAXD} := by
  have := absRunFrom_le w ∅ 0 (by rw [lookupD_empty]) (by omega)
  simpa [absRun] using this

lemma absRun_entry (w : List Move) :
    (absRun w, lookupD reachD (absRun w)) ∈ reachD := by
  have h := (absRun_le w).2
  exact lookupD_mem reachD _ (by omega)

/-! ### The maximum and the depths -/

theorem card_run_le_four (w : List Move) : (run lam w).card ≤ 4 := by
  rw [card_run_eq]
  exact (check_entry (absRun_entry w)).1

theorem N_le_four (k : ℕ) : N lam k ≤ 4 := by
  apply Finset.sup_le
  intro v _
  exact card_run_le_four _

/-- If a run is short, its configuration is small. -/
lemma card_run_le_of_length (w : List Move) (c b : ℕ)
    (hsel : ∀ (T : Finset (Fin {n})) (d : ℕ), (T, d) ∈ reachD → T.card ≤ c ∨ b ≤ d)
    (hw : w.length < b) : (run lam w).card ≤ c := by
  rw [card_run_eq]
  rcases hsel _ _ (absRun_entry w) with h | h
  · exact h
  · exact absurd (le_trans h (absRun_le w).1) (by omega)

theorem N_le_of_lt (c b : ℕ)
    (hsel : ∀ (T : Finset (Fin {n})) (d : ℕ), (T, d) ∈ reachD → T.card ≤ c ∨ b ≤ d)
    (k : ℕ) (hk : k < b) : N lam k ≤ c := by
  apply Finset.sup_le
  intro v _
  refine card_run_le_of_length _ c b hsel ?_
  simpa using hk

theorem N_zero_le_zero : N lam 0 ≤ 0 :=
  N_le_of_lt 0 1 (fun _ _ h => (check_entry h).2.2.2.1) _ (by omega)

theorem N_two_le_one : N lam 2 ≤ 1 :=
  N_le_of_lt 1 3 (fun _ _ h => (check_entry h).2.2.2.2.1) _ (by omega)

theorem N_four_le_two : N lam 4 ≤ 2 :=
  N_le_of_lt 2 5 (fun _ _ h => (check_entry h).2.2.2.2.2.1) _ (by omega)

theorem N_ten_le_three : N lam 10 ≤ 3 :=
  N_le_of_lt 3 11 (fun _ _ h => (check_entry h).2.2.2.2.2.2) _ (by omega)

/-! ### Lower bounds from explicit runs -/

lemma le_N_of_word {{k : ℕ}} (v : Fin k → Move) : (absRun (List.ofFn v)).card ≤ N lam k := by
  have h : (run lam (List.ofFn v)).card = (absRun (List.ofFn v)).card := card_run_eq _
  rw [← h]
  exact Finset.le_sup (f := fun u : Fin k → Move => (run lam (List.ofFn u)).card)
    (Finset.mem_univ v)

/-- The run `{words[1]}` gives one knot. -/
theorem one_le_N_one : 1 ≤ N lam {len(words[1])} := by
  have h := le_N_of_word (k := {len(words[1])}) {word(words[1])}
  have hc : (absRun (List.ofFn {word(words[1])})).card = 1 := by decide +kernel
  omega

/-- The run `{words[2]}` gives two knots. -/
theorem two_le_N_three : 2 ≤ N lam {len(words[2])} := by
  have h := le_N_of_word (k := {len(words[2])}) {word(words[2])}
  have hc : (absRun (List.ofFn {word(words[2])})).card = 2 := by decide +kernel
  omega

/-- The run `{words[3]}` gives three knots. -/
theorem three_le_N_five : 3 ≤ N lam {len(words[3])} := by
  have h := le_N_of_word (k := {len(words[3])}) {word(words[3])}
  have hc : (absRun (List.ofFn {word(words[3])})).card = 3 := by decide +kernel
  omega

/-- The run `{words[4]}` gives four knots. -/
theorem four_le_N_eleven : 4 ≤ N lam {len(words[4])} := by
  have h := le_N_of_word (k := {len(words[4])}) {word(words[4])}
  have hc : (absRun (List.ofFn {word(words[4])})).card = 4 := by decide +kernel
  omega

/-- **T8 (supergolden, exact maximum).**  The largest number of simultaneous
knots at the supergolden parameter is `4`. -/
theorem sup_N_lam : IsGreatest (Set.range (N lam)) 4 := by
  constructor
  · exact ⟨11, le_antisymm (N_le_four 11) four_le_N_eleven⟩
  · rintro y ⟨k, rfl⟩
    exact N_le_four k

lemma N_mono' {{a b : ℕ}} (hab : a ≤ b) : N lam a ≤ N lam b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih => exact le_trans ih (N_mono one_lt_lam k)

/-- `d 1 = 1`. -/
theorem d_one : d lam 1 = 1 := by
  have hmem : (1:ℕ) ∈ {{k | 1 ≤ N lam k}} := one_le_N_one
  refine le_antisymm (Nat.sInf_le hmem) ?_
  refine le_csInf ⟨1, hmem⟩ ?_
  intro k hk
  by_contra hlt
  push_neg at hlt
  interval_cases k
  · have := N_zero_le_zero
    simp only [Set.mem_setOf_eq] at hk
    omega

/-- `d 2 = 3`. -/
theorem d_two : d lam 2 = 3 := by
  have hmem : (3:ℕ) ∈ {{k | 2 ≤ N lam k}} := two_le_N_three
  refine le_antisymm (Nat.sInf_le hmem) ?_
  refine le_csInf ⟨3, hmem⟩ ?_
  intro k hk
  by_contra hlt
  push_neg at hlt
  have hmono : N lam k ≤ N lam 2 := N_mono' (by omega)
  have := N_two_le_one
  simp only [Set.mem_setOf_eq] at hk
  omega

/-- `d 3 = 5`. -/
theorem d_three : d lam 3 = 5 := by
  have hmem : (5:ℕ) ∈ {{k | 3 ≤ N lam k}} := three_le_N_five
  refine le_antisymm (Nat.sInf_le hmem) ?_
  refine le_csInf ⟨5, hmem⟩ ?_
  intro k hk
  by_contra hlt
  push_neg at hlt
  have hmono : N lam k ≤ N lam 4 := N_mono' (by omega)
  have := N_four_le_two
  simp only [Set.mem_setOf_eq] at hk
  omega

/-- `d 4 = 11`. -/
theorem d_four : d lam 4 = 11 := by
  have hmem : (11:ℕ) ∈ {{k | 4 ≤ N lam k}} := four_le_N_eleven
  refine le_antisymm (Nat.sInf_le hmem) ?_
  refine le_csInf ⟨11, hmem⟩ ?_
  intro k hk
  by_contra hlt
  push_neg at hlt
  have hmono : N lam k ≤ N lam 10 := N_mono' (by omega)
  have := N_ten_le_three
  simp only [Set.mem_setOf_eq] at hk
  omega

end Supergolden
end KnotGame
'''

open('RequestProject/Supergolden.lean', 'w').write(src)
print("orbit", n, "configs", len(cfgs), "maxdepth", MAXD)
