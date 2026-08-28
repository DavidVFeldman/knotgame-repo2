# SCRUPLES — round 4

Every place where the Lean statement is not a literal transcription of the
commission, and every convention that had to be fixed.

## 1. Open/closed conventions at `g` and `r`

The window is **open at both ends**:

```lean
def Window (lam : ℝ) : Set ℝ := Set.Ioo (g lam) (r lam)
```

and legality is strict on both sides:

```lean
noncomputable def BLegal (lam : ℝ) (e : Fin 2) (x : ℝ) : Prop :=
  if e = 0 then x < r lam else g lam < x
```

This is the commission's own wording ("branch 0 is legal iff `x < r`; branch 1
is legal iff `x > g`"), and it agrees with the round-1 convention of `Basic.lean`,
where survival is strict because the deleted interval is closed.  Consequences
worth stating explicitly, because they are what the proofs use:

* "outside the window" means `x ≤ g` **or** `r ≤ x` — the endpoints themselves
  are outside;
* at `x = g` exactly branch `0` is legal (`g < r` for `λ < 2`), and at `x = r`
  exactly branch `1` is legal.  So the forced dynamics is defined at the
  endpoints, and T11a is stated with the non-strict hypotheses `x ≤ g` and
  `r ≤ x`, exactly as the commission writes them;
* T11a's conclusions are strict (`λx < r`, `λx − (λ−1) > g`), which is what
  "never crosses" means with an open window: a forced image that leaves its own
  side is **inside** the window, not on its far edge.

## 2. The boundary `x = (g+r)/2` in T11c

`g + r = 1` identically (`g_add_r`), so the midpoint of the window is `1/2` for
every `λ` (`mid_eq_half`).  The statements keep the commission's expression
`(g+r)/2` rather than `1/2`.

The boundary case is assigned to the **lower** branch: `good_child_low` has
hypothesis `x ≤ (g+r)/2` and `good_child_high` has `(g+r)/2 < x`, and the
canonical selector is

```lean
noncomputable def cb (lam : ℝ) (x : ℝ) : Fin 2 := if x ≤ (g lam + r lam) / 2 then 0 else 1
```

This matches the commission ("if `x ≤ (g+r)/2` then `λx ∈ …`; else …").  It also
makes `cb` agree with the forced branch outside the window without a case split
(`cb_of_le_g`, `cb_of_r_le`), because `g ≤ (g+r)/2 < r` there.

## 3. T11c: the interval statements and the distance statement are separate

The commission's T11c makes two assertions: the child lies in an explicit
interval, and it has distance `≥ η` from `{0,1}`.  Both are formalised, as
`good_child_low` / `good_child_high` (the intervals, plus `2 − λ < r`) and
`good_child` (the distance, for the selected child `f λ (cb λ x) x`).  The
distance statement is the one the later targets consume.

## 4. T11d: the shape of the hypothesis on `B`

The commission writes: "`B` is any natural with `λ₀^(B−1)·η > g(λ₁)`".  This is
transcribed literally, with `B − 1` in natural-number subtraction and the side
condition `1 ≤ B`:

```lean
theorem bounded_return_low {B : ℕ} (hB1 : 1 ≤ B) … (hB : g lam1 < lam0 ^ (B - 1) * eta lam0 lam1)
```

The conclusion is `∃ k ≤ B, …`, again as written.  (The proof in fact produces
`k ≤ B − 1`; we do not state the sharper form, since `k ≤ B` is what T12 uses.)
For the anchor window `[1000/667, 8/5]` the commission's data `η = 1/5`,
`g(λ₁) = 3/8`, `B = 3` are certified in `CommonWindow` as `eta_anchor`,
`g_lamHi` and `return_bound_anchor`.

The "symmetrically from `[r, 1−η]` under branch 1" half is proved, not asserted:
`bounded_return_high` is derived from `bounded_return_low` through the exact
conjugacy `x ↦ 1 − x`, which swaps the two branch maps and preserves the window
(`one_sub_mem_Window`).

## 5. T11d: "all earlier iterates staying in `(0, g]`"

Formalised as `∀ j < k, (f λ 0)^[j] x ∈ Set.Ioc 0 (g λ)` — half-open at `0`,
closed at `g`, matching the commission's `(0, g]`.  The symmetric statement is
`∀ j < k, (f λ 1)^[j] x ∈ Set.Ico (r λ) 1`.

## 6. T12a is proved on a larger set of parameters than commissioned

The commission asks for T12a "for `λ ∈ [λ₀,λ₁]` as above".  The proof needs only

* `1 < λ < 2` and `λ² < λ + 1`, and
* the **finiteness** — not the boundedness — of the forced return time, which is
  `exists_window_ge` and follows from T11a plus `λ^i → ∞`.

So `continuum_of_survival_itineraries` is stated for every `λ ∈ (1,2)` with
`λ² < λ+1`, i.e. for all `λ < φ`; it applies in particular on `[λ₀,λ₁]`, and
`common_window` instantiates it there.  This is a strengthening, not a
deviation; it is recorded here because the hypotheses differ from the
commission's.

The construction is the commission's: at a window visit the **chosen bit's**
child is followed (not the good child), and elsewhere the forced branch.  The
bounded return `B` of T11d plays no role in T12a — it is needed only for the
count T12b.

## 7. What "the survival itineraries of `1/2`" means

An itinerary is a function `ℕ → Fin 2`; it survives from `x` when every branch
it prescribes is legal at the point reached so far:

```lean
def Surviving (lam x : ℝ) (e : ℕ → Fin 2) : Prop :=
  ∀ n, BLegal lam (e n) (itinOrbit lam x e n)
```

The deliverable `continuum_of_survival_itineraries` is an
`∃ Θ, Function.Injective Θ ∧ ∀ b, Surviving lam (1/2) (Θ b)`, i.e. literally an
injection of `ℕ → Bool` into that set.  `Θ` is the explicit map `theta`, not a
choice-produced one.

## 8. T12b: what `K_m` counts, and why only `m/(B+1)` words are exhibited

`K λ m` is the number of `w : Fin m → Fin 2` such that each of the `m` branches
is legal at the point reached so far (`SurvivesUpTo`).  `K_eq_card_bSurvives`
proves this is the same count as the list-recursive predicate `bSurvives`, so
nothing turns on the choice of encoding.  The extension of `w` past index `m`
(`extendWord`, by branch `0`) is irrelevant: `SurvivesUpTo … m` only inspects
indices `< m`.

The bound is proved exactly as the note describes: along the spine (always the
good child) the window is visited at times `visit 0 = 0 < visit 1 < ⋯` with
gaps at most `B+1`, so `visit i ≤ i·(B+1)`, and at least `m/(B+1)` of these
times are `< m`.  Deviating from the spine at exactly one visit gives a
surviving word, and two such words differ at the earlier of the two visits.
This produces `m/(B+1)` distinct words; the spine's own word is *not* counted,
so the inequality `m/(B+1) ≤ K λ m` has no off-by-one risk.  `m/(B+1)` is
natural-number division, as the commission allows.

The exponential bound is **not** claimed: only one deviation per word is used,
because the discarded child's return time is unbounded — which is precisely the
open tail estimate the commission excludes.

## 9. T13 is one theorem

`CommonWindow.common_window` is a single conjunction; its (a) half both records
the inclusion `1/λ ∈ [5/8, 667/1000] ⊆ [1/2, 667/1000]` and *instantiates* the
round-3 theorem at `1/λ`, so that citing it does not require re-checking the
inclusion by hand.  `lamLo` and `lamHi` are `noncomputable` only because real
division is.

## 10. Standing constraints

No `sorry`, no `admit`, no new `axiom`, no `@[implemented_by]`, no
`native_decide`.  Round 4 adds no finite computation at all: everything is
algebra over an ordered field plus induction on `ℕ`.  The rational arithmetic of
the anchor window (`3/8 < (1000/667)²/5`, `1000/667 ≤ 3/2 ≤ 8/5`) is discharged
by `norm_num`.
