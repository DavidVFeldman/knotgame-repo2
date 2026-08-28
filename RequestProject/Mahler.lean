import RequestProject.Ternary
import RequestProject.Littlewood

/-!
# T22b, T22c — base `3/2` and Mahler's recursion (paper `prop:base32`, `prop:mahler`)

## T22b — the itinerary as a `{0,1}`-representation of `1` in base `3/2`

`itinerary_tsum` is the paper's `prop:itinerary` for a general `λ ∈ (1,∞)`: if
the orbit `x_0, x_1, …` of `x` along the branch itinerary `ε` stays in `[0,1]`,
then

  `x = (1 − r) ∑_{k≥0} ε_{k+1} r ^ k`,   `r = 1/λ`.

At `λ = 3/2` and `x = 1/2` this is `∑_{j≥1} ε_j (2/3) ^ j = 1`
(`base32_tsum`): the itinerary of a knot is a `{0,1}`-representation of `1` in
base `3/2`.  The second half of `prop:base32`, `D(x_n) = ε_{n+1} + [2x_{n+1} >
1]`, is `digit_eq_eps_add` — see the conventions below for the boundary case.

## T22c — Mahler's recursion

With `w = 2x ∈ (0,2)`, `p = ⌊w⌋ ∈ {0,1}` and `y = {w}`, the five identities of
`prop:mahler` are `mahler_recursion`:

  `D = ⌊(3/2)w⌋`,  `w' = (3/2)w − ε`,  `y' = {(3/2)y + p/2}`,
  `D = p + [y ≥ (2−p)/3]`,  `p' = D − ε`.

`mahler_of_survives` feeds the game into this: for a knot that survives a move,
`ε` is the ternary bracket `[D x > code m]` of `RequestProject.Ternary` and
`x'` is its image, so the game *is* this recursion.  Nothing here claims
anything about Mahler's problem itself; what is certified is that the
identification of the two recursions is exact.

## Conventions (SCRUPLES)

* Itineraries are indexed from `0` in Lean (`eps k` is the paper's
  `ε_{k+1}`), and `orbit lam eps x` is the paper's `x_n`.
* The paper writes the second half of `prop:base32` with a strict bracket,
  `[2x_{n+1} > 1]`.  The identity that is true without further hypotheses uses
  the non-strict bracket `[2x_{n+1} ≥ 1]` (`digit_eq_eps_add`); the two agree
  unless `x_{n+1} = 1/2` exactly, and `digit_eq_eps_add_strict` records the
  paper's form under that hypothesis.  Along the game this is no restriction:
  `RequestProject.Ternary.dyadic_posAfter` shows a position after `n ≥ 1` moves
  is an odd multiple of `2 ^ -(n+1)`, hence never `1/2`.
* `Int.fract` is Lean's `{·}`.
-/

namespace KnotGame
namespace Ternary

open Filter Topology

variable {lam x : ℝ}

/-! ### T22b: the itinerary identity -/

/-- One step of the inverted recursion, summed: `x = (1−r) ∑_{k<N} ε_k r^k +
r^N x_N`. -/
lemma orbit_partial (h : 1 < lam) (eps : ℕ → Fin 2) (x : ℝ) (N : ℕ) :
    x = (1 - r lam) * (∑ k ∈ Finset.range N, ((eps k : ℕ) : ℝ) * (r lam) ^ k)
      + (r lam) ^ N * orbit lam eps x N := by
  have hlam : (0:ℝ) < lam := lt_trans zero_lt_one h
  have hr : r lam = lam⁻¹ := rfl
  have hrl : lam * r lam = 1 := by rw [hr]; field_simp
  induction N with
  | zero => simp [orbit]
  | succ N ih =>
      have hrn : (r lam) ^ (N + 1) * lam = (r lam) ^ N := by
        rw [pow_succ, mul_assoc, mul_comm (r lam) lam, hrl, mul_one]
      rw [Finset.sum_range_succ, orbit, f_eq_sub]
      linear_combination ih + (((eps N : ℕ) : ℝ) - orbit lam eps x N) * hrn

lemma summable_itinerary (h : 1 < lam) (eps : ℕ → Fin 2) :
    Summable (fun k : ℕ => ((eps k : ℕ) : ℝ) * (r lam) ^ k) := by
  have hr0 : 0 < r lam := r_pos lam h
  have hr1 : r lam < 1 := r_lt_one lam h
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (summable_geometric_of_lt_one (le_of_lt hr0) hr1)
  have : ((eps k : ℕ) : ℝ) ≤ 1 := by
    have : (eps k : ℕ) ≤ 1 := Nat.lt_succ_iff.mp (eps k).isLt
    exact_mod_cast this
  nlinarith [pow_pos hr0 k]

/-- **T22b, first half** (paper `prop:itinerary`).  A point whose orbit along
the branch itinerary `eps` stays in `[0,1]` is the value of the corresponding
`{0,1}`-series. -/
theorem itinerary_tsum (h : 1 < lam) (eps : ℕ → Fin 2) (x : ℝ)
    (hb : ∀ n, orbit lam eps x n ∈ Set.Icc (0:ℝ) 1) :
    x = (1 - r lam) * ∑' k : ℕ, ((eps k : ℕ) : ℝ) * (r lam) ^ k := by
  have hr0 : 0 < r lam := r_pos lam h
  have hr1 : r lam < 1 := r_lt_one lam h
  have hsum := summable_itinerary h eps
  set T := ∑' k : ℕ, ((eps k : ℕ) : ℝ) * (r lam) ^ k with hT
  have hP : Tendsto (fun N => ∑ k ∈ Finset.range N, ((eps k : ℕ) : ℝ) * (r lam) ^ k)
      atTop (𝓝 T) := hsum.hasSum.tendsto_sum_nat
  have htail : Tendsto (fun N => (r lam) ^ N * orbit lam eps x N) atTop (𝓝 0) := by
    have hgeo : Tendsto (fun N : ℕ => (r lam) ^ N) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt hr0) hr1
    refine squeeze_zero_norm (fun N => ?_) hgeo
    have h1 : |orbit lam eps x N| ≤ 1 := by
      rcases hb N with ⟨h1, h2⟩
      rw [abs_le]; exact ⟨by linarith, h2⟩
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (le_of_lt (pow_pos hr0 N))]
    nlinarith [pow_pos hr0 N, abs_nonneg (orbit lam eps x N)]
  have hconst : Tendsto (fun _ : ℕ => x) atTop (𝓝 ((1 - r lam) * T + 0)) := by
    have := ((hP.const_mul (1 - r lam)).add htail)
    simpa [← orbit_partial h eps x] using this
  have := tendsto_nhds_unique tendsto_const_nhds hconst
  simpa using this

/-- **T22b, first half at `λ = 3/2`** (paper `prop:base32`).  The itinerary of a
knot is a `{0,1}`-representation of `1` in base `3/2`. -/
theorem base32_tsum (eps : ℕ → Fin 2)
    (hb : ∀ n, orbit (3/2 : ℝ) eps (1/2 : ℝ) n ∈ Set.Icc (0:ℝ) 1) :
    ∑' j : ℕ, ((eps j : ℕ) : ℝ) * (2/3 : ℝ) ^ (j + 1) = 1 := by
  have h := itinerary_tsum one_lt_lam32 eps (1/2 : ℝ) hb
  rw [r32] at h
  have hsum : Summable (fun k : ℕ => ((eps k : ℕ) : ℝ) * (2/3 : ℝ) ^ k) := by
    have := summable_itinerary one_lt_lam32 eps
    rwa [r32] at this
  have hshift : ∑' j : ℕ, ((eps j : ℕ) : ℝ) * (2/3 : ℝ) ^ (j + 1)
      = (2/3 : ℝ) * ∑' k : ℕ, ((eps k : ℕ) : ℝ) * (2/3 : ℝ) ^ k := by
    rw [← hsum.tsum_mul_left]
    exact tsum_congr fun j => by ring
  rw [hshift]
  have : (1 : ℝ) / 2 = (1 - 2/3) * ∑' k : ℕ, ((eps k : ℕ) : ℝ) * (2/3 : ℝ) ^ k := h
  linarith

/-! ### T22b, second half: the digit and the itinerary -/

/-- **T22b, second half.**  With `3x = ε + 2x'` and `x' ∈ [0,1)`, the ternary
digit of `x` is `ε` plus the bracket `[2x' ≥ 1]`. -/
theorem digit_eq_eps_add {x' : ℝ} {e : ℕ} (hx'0 : 0 ≤ x') (hx'1 : x' < 1)
    (hstep : 3 * x = (e : ℝ) + 2 * x') :
    D x = (e : ℤ) + (if 1 ≤ 2 * x' then 1 else 0) := by
  rw [D, hstep]
  by_cases hc : 1 ≤ 2 * x'
  · rw [if_pos hc, Int.floor_eq_iff]
    constructor
    · push_cast; linarith
    · push_cast; linarith
  · push_neg at hc
    rw [if_neg (not_le.mpr hc), add_zero, Int.floor_eq_iff]
    constructor
    · push_cast; linarith
    · push_cast; linarith

/-- The paper's strict form of the previous identity, valid away from the
boundary case `x' = 1/2`. -/
theorem digit_eq_eps_add_strict {x' : ℝ} {e : ℕ} (hx'0 : 0 ≤ x') (hx'1 : x' < 1)
    (hne : 2 * x' ≠ 1) (hstep : 3 * x = (e : ℝ) + 2 * x') :
    D x = (e : ℤ) + (if 1 < 2 * x' then 1 else 0) := by
  rw [digit_eq_eps_add hx'0 hx'1 hstep]
  by_cases hc : 1 < 2 * x'
  · rw [if_pos hc, if_pos (le_of_lt hc)]
  · push_neg at hc
    rw [if_neg (not_lt.mpr hc), if_neg (by
      intro hle
      exact hne (le_antisymm hc hle))]

/-! ### T22c: Mahler's recursion -/

/-- For `w ∈ (0,2)` the carry `p = ⌊w⌋` is `0` or `1`. -/
lemma floor_mem (w : ℝ) (hw0 : 0 < w) (hw2 : w < 2) : ⌊w⌋ = 0 ∨ ⌊w⌋ = 1 := by
  have h1 : (0:ℤ) ≤ ⌊w⌋ := Int.le_floor.mpr (by push_cast; linarith)
  have h2 : ⌊w⌋ < 2 := Int.floor_lt.mpr (by push_cast; linarith)
  omega

/-- **T22c** (paper `prop:mahler`).  Writing `w = 2x`, `p = ⌊w⌋`, `y = {w}` and
`w' = 2x'` for the image `x' = (3x − ε)/2` of `x` under the branch `ε`, the
five identities of the proposition hold. -/
theorem mahler_recursion (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (e : ℕ)
    (x' : ℝ) (hx' : x' = (3 * x - (e : ℝ)) / 2) :
    D x = ⌊(3/2 : ℝ) * (2 * x)⌋ ∧
    2 * x' = (3/2 : ℝ) * (2 * x) - (e : ℝ) ∧
    Int.fract (2 * x') = Int.fract ((3/2 : ℝ) * Int.fract (2 * x) + (⌊2 * x⌋ : ℝ) / 2) ∧
    D x = ⌊2 * x⌋ + (if (2 - (⌊2 * x⌋ : ℝ)) / 3 ≤ Int.fract (2 * x) then 1 else 0) ∧
    ⌊2 * x'⌋ = D x - (e : ℤ) := by
  have hw0 : 0 < 2 * x := by linarith
  have hw2 : 2 * x < 2 := by linarith
  set w : ℝ := 2 * x with hw
  set p : ℤ := ⌊w⌋ with hp
  set y : ℝ := Int.fract w with hy
  have hyw : w = (p : ℝ) + y := by rw [hp, hy, Int.floor_add_fract]
  have hy0 : 0 ≤ y := Int.fract_nonneg w
  have hy1 : y < 1 := Int.fract_lt_one w
  have hDw : D x = ⌊(3/2 : ℝ) * w⌋ := by rw [D, hw]; congr 1; ring
  -- (b)
  have hb : 2 * x' = (3/2 : ℝ) * w - (e : ℝ) := by rw [hx', hw]; ring
  -- (c)
  have hc : Int.fract (2 * x') = Int.fract ((3/2 : ℝ) * y + (p : ℝ) / 2) := by
    rw [hb]
    have hrw : (3/2 : ℝ) * w - (e : ℝ) = ((3/2 : ℝ) * y + (p : ℝ) / 2) + ((p : ℤ) - (e : ℤ) : ℤ) := by
      rw [hyw]; push_cast; ring
    rw [hrw, Int.fract_add_intCast]
  -- (d)
  have hfl : ⌊(3/2 : ℝ) * w⌋ = p + ⌊(3/2 : ℝ) * y + (p : ℝ) / 2⌋ := by
    have hrw : (3/2 : ℝ) * w = ((3/2 : ℝ) * y + (p : ℝ) / 2) + (p : ℝ) := by
      rw [hyw]; ring
    rw [hrw, Int.floor_add_intCast, add_comm]
  have hbracket : ⌊(3/2 : ℝ) * y + (p : ℝ) / 2⌋
      = (if (2 - (p : ℝ)) / 3 ≤ y then 1 else 0) := by
    have hp01 : p = 0 ∨ p = 1 := floor_mem w hw0 hw2
    by_cases hcond : (2 - (p : ℝ)) / 3 ≤ y
    · rw [if_pos hcond, Int.floor_eq_iff]
      constructor
      · push_cast
        rcases hp01 with h | h <;> rw [h] at hcond ⊢ <;> push_cast at hcond ⊢ <;> linarith
      · push_cast
        rcases hp01 with h | h <;> rw [h] <;> push_cast <;> linarith
    · push_neg at hcond
      rw [if_neg (not_le.mpr hcond), Int.floor_eq_iff]
      constructor
      · push_cast
        rcases hp01 with h | h <;> rw [h] <;> push_cast <;> linarith
      · push_cast
        rcases hp01 with h | h <;> rw [h] at hcond ⊢ <;> push_cast at hcond ⊢ <;> linarith
  -- (e)
  have he : ⌊2 * x'⌋ = D x - (e : ℤ) := by
    rw [hb, hDw]
    have : (3/2 : ℝ) * w - (e : ℝ) = (3/2 : ℝ) * w + (-(e : ℤ) : ℤ) := by push_cast; ring
    rw [this, Int.floor_add_intCast]
    ring
  exact ⟨hDw, hb, hc, by rw [hDw, hfl, hbracket], he⟩

/-- **T22c, fed by the game.**  For a knot at `x` surviving the move `m` at
`λ = 3/2`, the branch digit `ε = [D x > code m]` and the image
`x' = act x` satisfy Mahler's recursion. -/
theorem mahler_of_survives (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (m : Move)
    (hs : survives (3/2 : ℝ) m x) :
    act (3/2 : ℝ) m x = (3 * x - ((if code m < D x then 1 else 0 : ℕ) : ℝ)) / 2 ∧
      2 * act (3/2 : ℝ) m x
        = (3/2 : ℝ) * (2 * x) - ((if code m < D x then 1 else 0 : ℕ) : ℝ) := by
  have hact := act_eq_ternary hx0 hx1 m hs
  constructor
  · rw [hact]
    by_cases hc : code m < D x <;> simp [hc]
  · rw [hact]
    by_cases hc : code m < D x <;> · simp [hc]; ring

end Ternary
end KnotGame
