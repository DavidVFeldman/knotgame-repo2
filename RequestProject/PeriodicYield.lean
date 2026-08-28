import RequestProject.Compactness

/-!
# T23 — a periodic kind word yields unboundedness (paper `prop:kindyield`)

A finite word `v` is **kind** when `1/2` survives every power `v ^ n`
(`KindWord`).  If moreover the last letter of `v` is an `M`, then the run
`v ^ n` carries a knot born at each of the `n` occurrences of that letter, and
kindness is exactly the statement that each of those knots is still alive at
the end.  Their ages are `0, |v|, 2|v|, …`, which is a bound independent of
`n`, so condition (iii) of the certified compactness criterion
(`BoundedAgeWitnesses`) holds; the criterion then supplies a single
left-infinite run carrying infinitely many simultaneous knots — condition (i),
`InfinitelyManyKnots` — and hence `N_λ = ∞`.

## How this differs from `no_return_to_half`

`RequestProject.Littlewood` certifies (paper `cor:noperiodic`) that under a
periodic run the orbit of a knot born at an `M` never *returns to its birth
point* `1/2` at a time divisible by the period.  That excludes the algebraic
route to unboundedness — one cannot produce a periodic kind word by solving
for a parameter at which `1/2` is a periodic point, because there is none.

It does **not** exclude the route certified here, in which the knot merely
*stays alive*: nothing in `KindWord` asks the orbit of `1/2` to return
anywhere.  The paper's remark after `cor:noperiodic` says exactly this, and
this file adds no evidence either way about whether a kind periodic word
exists at any particular parameter — `KindWord lam v` is a hypothesis
throughout, certified for no `λ` and no `v` here.

## Relation to `Littlewood.N_unbounded_of_kind`

The round-1 file already derives unboundedness of `N_λ` from an *infinite*
kind sequence that is periodic with an `M` at the end of the period.  What is
new here is the finite-word formulation of the paper, and the conclusion in
the form of condition (i) of `thm:compactness`, i.e. a single left-infinite
run carrying infinitely many knots at once; `N_unbounded_of_kindWord` then
recovers the unboundedness statement through the compactness file.

## Conventions (SCRUPLES)

* The paper indexes the period as `v_1 … v_p` and asks `v_p = M`; here the
  hypothesis is `v = u ++ [Move.M]`, which is the same and makes the
  decomposition of `v ^ n` immediate.
* "`v` is kind" is `∀ n, survivesWord lam (1/2) (v ^ n)`.  Since survival is
  prefix-closed, this is equivalent to `1/2` surviving the left-infinite
  periodic run, which is the paper's phrasing.
-/

namespace KnotGame

variable {lam : ℝ}

/-- The `k`-fold concatenation `v ^ k`. -/
def rep (v : List Move) : ℕ → List Move
  | 0 => []
  | k + 1 => v ++ rep v k

@[simp] lemma rep_zero (v : List Move) : rep v 0 = [] := rfl

@[simp] lemma rep_succ (v : List Move) (k : ℕ) : rep v (k + 1) = v ++ rep v k := rfl

lemma rep_add (v : List Move) (a b : ℕ) : rep v (a + b) = rep v a ++ rep v b := by
  induction a with
  | zero => simp
  | succ a ih => rw [show a + 1 + b = (a + b) + 1 by ring, rep_succ, rep_succ, ih,
      List.append_assoc]

@[simp] lemma length_rep (v : List Move) (k : ℕ) : (rep v k).length = k * v.length := by
  induction k with
  | zero => simp
  | succ k ih => simp [ih]; ring

/-- A finite word is **kind** for `lam` when `1/2` survives all of its
powers. -/
def KindWord (lam : ℝ) (v : List Move) : Prop := ∀ k, survivesWord lam (1/2) (rep v k)

/-- Splitting `v ^ (a+1+i)` at the final `M` of the `(a+1)`-st period. -/
lemma rep_split {v u : List Move} (hv : v = u ++ [Move.M]) (a i : ℕ) :
    rep v (a + 1 + i) = (rep v a ++ u) ++ Move.M :: rep v i := by
  rw [rep_add, rep_add]
  simp only [rep_succ, rep_zero, List.append_nil]
  rw [hv]
  simp [List.append_assoc]

/-- Each occurrence of the final `M` of a period is the birth of a knot of the
run `v ^ k`, of age a multiple of `|v|`. -/
lemma hasKnotAge_rep {v u : List Move} (hv : v = u ++ [Move.M]) (hk : KindWord lam v)
    {i k : ℕ} (hik : i < k) : HasKnotAge lam (rep v k) (i * v.length) := by
  obtain ⟨a, rfl⟩ : ∃ a, k = a + 1 + i := ⟨k - 1 - i, by omega⟩
  exact ⟨posAfter lam (1/2) (rep v i), rep v a ++ u, rep v i, rep_split hv a i,
    by simp, hk i, rfl⟩

/-- **T23** (paper `prop:kindyield`), in the form of condition (i) of the
certified compactness criterion: a kind word whose last letter is an `M`
produces a single left-infinite run carrying infinitely many simultaneous
knots. -/
theorem infinitelyManyKnots_of_kindWord {v u : List Move} (hv : v = u ++ [Move.M])
    (hk : KindWord lam v) : InfinitelyManyKnots lam := by
  have hpos : 0 < v.length := by rw [hv]; simp
  refine infinitelyManyKnots_of_boundedAgeWitnesses
    ⟨fun i => i * v.length, fun k => rep v k, fun _ i => i * v.length, fun k => ⟨?_, ?_, ?_⟩⟩
  · intro i hi
    exact hasKnotAge_rep hv hk hi
  · intro i j hij _
    exact Nat.mul_lt_mul_of_lt_of_le hij (le_refl _) hpos
  · intro i _
    exact le_refl _

/-- **T23, the unboundedness conclusion.**  A kind word whose last letter is an
`M` forces `N_λ` to be unbounded. -/
theorem N_unbounded_of_kindWord (h : 1 < lam) {v u : List Move} (hv : v = u ++ [Move.M])
    (hk : KindWord lam v) : ∀ K : ℕ, ∃ n : ℕ, K ≤ N lam n :=
  N_unbounded_of_infinitelyManyKnots h (infinitelyManyKnots_of_kindWord hv hk)

end KnotGame
