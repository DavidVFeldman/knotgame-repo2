import RequestProject.Mahler
import RequestProject.Sqrt2

/-!
# The binary square at `lam = √2` (paper `prop:square`, `prop:squaresurv`)

Because `λ² = 2`, the `{0,1}`-representation of `prop:itinerary` splits by
parity into two ordinary binary expansions.  Writing (paper indexing)

  `α_n = Σ_{i≥1} ε_{n+2i} 2^{-i}`,   `β_n = Σ_{i≥1} ε_{n+2i-1} 2^{-i}`,

the paper's `prop:square` asserts

  `x_n = (√2 − 1)(α_n + √2 β_n)`,
  `(α_{n+1}, β_{n+1}) = ({2β_n}, α_n)`,
  `ε_{n+1} = ⌊2β_n⌋`,

so that the state of a knot is a point of the unit square on which one move
shifts and swaps the coordinates.  `prop:squaresurv` then reads the survival
table off the five regions of `(0,1)`: a knot admits a move that both spares it
and induces its required branch unless `s_n = α_n + √2 β_n < 1/√2` while
`β_n ≥ 1/2`, or `s_n > (2+√2)/2` while `β_n < 1/2`.

Both are proved here: `pos_eq`, `beta_succ`, `alpha_succ`, `eps_eq_floor`,
`square_normal_form`, and `spares_zero_iff`, `spares_one_iff`,
`squaresurv_general`, `squaresurv`, together with the five region tables
`spares_region₁ … spares_region₅`.

## Conventions (SCRUPLES)

* Itineraries are indexed from `0` in Lean, as everywhere else in this
  development: `eps k` is the paper's `ε_{k+1}`, and `orbit lam eps x n` is the
  paper's `x_n`.  With that convention

    `alpha eps n = Σ_{i≥0} eps (n+2i+1) 2^{-(i+1)}`,
    `beta  eps n = Σ_{i≥0} eps (n+2i)   2^{-(i+1)}`,

  which are the paper's `α_n`, `β_n`.
* `x_n = (√2−1)(α_n + √2 β_n)` is proved for any itinerary whose orbit stays in
  `[0,1]` — exactly the hypothesis of `prop:itinerary` — via the round-8 lemma
  `KnotGame.Ternary.itinerary_tsum`.
* The identity that holds with **no** hypothesis is `two_mul_beta`:
  `2 β_n = ε_{n+1} + α_{n+1}` (`eps n` in Lean indexing).  The paper's
  `α_{n+1} = {2β_n}` and `ε_{n+1} = ⌊2β_n⌋` follow from it exactly when
  `α_{n+1} < 1`, i.e. unless the digits `ε` are `1` at *every* index of that
  parity class from `n+2` on (`alpha_eq_one_iff`).  In the degenerate case
  `α_{n+1} = 1` the fractional part is `0 ≠ α_{n+1}`, so the hypothesis is
  necessary and not an artefact; `alpha_lt_one` gives it from a single vanishing
  digit.  The same hypothesis is what turns `β_n ≥ 1/2` into `ε = 1` in
  `squaresurv`.
* The survival statement is proved in two layers.  `spares_zero_iff` and
  `spares_one_iff` are for a general `λ > 1`: a knot at `x` admits a move
  sparing it and inducing branch `0` iff `x < r`, and one inducing branch `1`
  iff `g < x`.  The five region tables (which of `L, M, R` do the sparing) need
  `g < r/2`, i.e. `λ < 3/2`, and are stated with the relevant inequalities as
  hypotheses; at `λ = √2` they hold.  `squaresurv` is then the paper's phrasing
  in the coordinates `s_n`, `β_n`.
-/

namespace KnotGame
namespace Square

open Real

/-! ### Binary sums of a digit sequence -/

/-- The value `Σ_{i≥0} c_i 2^{-(i+1)} ∈ [0,1]` of a binary digit sequence. -/
noncomputable def bsum (c : ℕ → Fin 2) : ℝ := ∑' i : ℕ, ((c i : ℕ) : ℝ) * (1/2 : ℝ) ^ (i + 1)

lemma summable_half : Summable (fun i : ℕ => (1/2 : ℝ) ^ (i + 1)) := by
  have h := (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ) < 1)).mul_left (1/2)
  refine h.congr (fun i => ?_)
  rw [pow_succ]; ring

lemma tsum_half : ∑' i : ℕ, (1/2 : ℝ) ^ (i + 1) = 1 := by
  have h2 : ∑' i : ℕ, (1/2:ℝ)^(i+1) = (1/2) * ∑' i : ℕ, (1/2:ℝ)^i := by
    rw [← tsum_mul_left]; congr 1; ext i; rw [pow_succ]; ring
  rw [h2, tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)]
  norm_num

lemma digit_le_one (c : ℕ → Fin 2) (i : ℕ) : ((c i : ℕ) : ℝ) ≤ 1 := by
  have : (c i : ℕ) ≤ 1 := Nat.lt_succ_iff.mp (c i).isLt
  exact_mod_cast this

lemma digit_nonneg (c : ℕ → Fin 2) (i : ℕ) : (0:ℝ) ≤ ((c i : ℕ) : ℝ) := by positivity

lemma summable_bsum (c : ℕ → Fin 2) :
    Summable (fun i : ℕ => ((c i : ℕ) : ℝ) * (1/2 : ℝ) ^ (i + 1)) := by
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) summable_half
  nlinarith [digit_le_one c i, pow_pos (by norm_num : (0:ℝ) < 1/2) (i+1)]

lemma bsum_nonneg (c : ℕ → Fin 2) : 0 ≤ bsum c :=
  tsum_nonneg (fun i => by positivity)

lemma bsum_le_one (c : ℕ → Fin 2) : bsum c ≤ 1 := by
  have h := Summable.tsum_le_tsum (f := fun i : ℕ => ((c i : ℕ) : ℝ) * (1/2 : ℝ) ^ (i+1))
    (g := fun i : ℕ => (1/2:ℝ)^(i+1))
    (fun i => by nlinarith [digit_le_one c i, pow_pos (by norm_num : (0:ℝ) < 1/2) (i+1)])
    (summable_bsum c) summable_half
  rwa [tsum_half] at h

/-- A single vanishing digit makes the value strictly smaller than `1`. -/
lemma bsum_lt_one (c : ℕ → Fin 2) (j : ℕ) (hj : c j = 0) : bsum c < 1 := by
  have hlt : ((c j : ℕ) : ℝ) * (1/2:ℝ)^(j+1) < (1/2:ℝ)^(j+1) := by
    rw [hj]; simp
  have h := Summable.tsum_lt_tsum (i := j)
    (f := fun i : ℕ => ((c i : ℕ) : ℝ) * (1/2 : ℝ) ^ (i+1))
    (g := fun i : ℕ => (1/2:ℝ)^(i+1))
    (fun i => by nlinarith [digit_le_one c i, pow_pos (by norm_num : (0:ℝ) < 1/2) (i+1)])
    hlt (summable_bsum c) summable_half
  rwa [tsum_half] at h

/-- Conversely, the value is `1` only for the all-ones sequence. -/
lemma bsum_eq_one_iff (c : ℕ → Fin 2) : bsum c = 1 ↔ ∀ j, c j = 1 := by
  constructor
  · intro h j
    by_contra hj
    have hj0 : c j = 0 := by omega
    exact absurd h (ne_of_lt (bsum_lt_one c j hj0))
  · intro h
    have : bsum c = ∑' i : ℕ, (1/2:ℝ)^(i+1) := by
      rw [bsum]; exact tsum_congr (fun i => by rw [h i]; norm_num)
    rw [this, tsum_half]

lemma bsum_two (c : ℕ → Fin 2) : ∑' i : ℕ, ((c i : ℕ) : ℝ) * (1/2:ℝ)^i = 2 * bsum c := by
  rw [bsum, ← tsum_mul_left]
  congr 1; ext i; rw [pow_succ]; ring

/-- Peeling off the leading digit. -/
lemma bsum_head (c : ℕ → Fin 2) : 2 * bsum c = ((c 0 : ℕ) : ℝ) + bsum (fun i => c (i+1)) := by
  rw [bsum, (summable_bsum c).tsum_eq_zero_add]
  have h : ∑' i : ℕ, ((c (i+1) : ℕ) : ℝ) * (1/2:ℝ)^(i+1+1)
      = (1/2) * bsum (fun i => c (i+1)) := by
    rw [bsum, ← tsum_mul_left]; congr 1; ext i; ring
  rw [h]; ring

/-! ### The coordinates of the square -/

/-- The paper's `α_n = Σ_{i≥1} ε_{n+2i} 2^{-i}`, in `0`-based indexing. -/
noncomputable def alpha (eps : ℕ → Fin 2) (n : ℕ) : ℝ := bsum (fun i => eps (n + 2*i + 1))

/-- The paper's `β_n = Σ_{i≥1} ε_{n+2i-1} 2^{-i}`, in `0`-based indexing. -/
noncomputable def beta (eps : ℕ → Fin 2) (n : ℕ) : ℝ := bsum (fun i => eps (n + 2*i))

/-- The paper's `s_n = α_n + √2 β_n ∈ [0, 1+√2]`. -/
noncomputable def sval (eps : ℕ → Fin 2) (n : ℕ) : ℝ := alpha eps n + Real.sqrt 2 * beta eps n

lemma alpha_nonneg (eps : ℕ → Fin 2) (n : ℕ) : 0 ≤ alpha eps n := bsum_nonneg _
lemma alpha_le_one (eps : ℕ → Fin 2) (n : ℕ) : alpha eps n ≤ 1 := bsum_le_one _
lemma beta_nonneg (eps : ℕ → Fin 2) (n : ℕ) : 0 ≤ beta eps n := bsum_nonneg _
lemma beta_le_one (eps : ℕ → Fin 2) (n : ℕ) : beta eps n ≤ 1 := bsum_le_one _

lemma sval_nonneg (eps : ℕ → Fin 2) (n : ℕ) : 0 ≤ sval eps n := by
  have := alpha_nonneg eps n
  have := beta_nonneg eps n
  have : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  unfold sval; positivity

lemma sval_le (eps : ℕ → Fin 2) (n : ℕ) : sval eps n ≤ 1 + Real.sqrt 2 := by
  have h1 := alpha_le_one eps n
  have h2 := beta_le_one eps n
  have h3 : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  unfold sval; nlinarith

/-- **`prop:square`, second identity (the swap).** -/
theorem beta_succ (eps : ℕ → Fin 2) (n : ℕ) : beta eps (n + 1) = alpha eps n := by
  unfold beta alpha
  congr 1; funext i; congr 1; omega

/-- The unconditional form of the shift: `2 β_n = ε_{n+1} + α_{n+1}`. -/
theorem two_mul_beta (eps : ℕ → Fin 2) (n : ℕ) :
    2 * beta eps n = ((eps n : ℕ) : ℝ) + alpha eps (n + 1) := by
  have h := bsum_head (fun i => eps (n + 2*i))
  have e0 : ((eps (n + 2*0) : ℕ) : ℝ) = ((eps n : ℕ) : ℝ) := by norm_num
  have e1 : (fun i => eps (n + 2*(i+1))) = (fun i => eps ((n+1) + 2*i + 1)) := by
    funext i; congr 1; omega
  rw [beta, h, e0, e1, alpha]

/-- `α_n = 1` exactly for the degenerate itineraries whose digits are all `1` on
the relevant parity class. -/
theorem alpha_eq_one_iff (eps : ℕ → Fin 2) (n : ℕ) :
    alpha eps n = 1 ↔ ∀ i, eps (n + 2*i + 1) = 1 := bsum_eq_one_iff _

/-- One vanishing digit of the parity class is enough. -/
theorem alpha_lt_one (eps : ℕ → Fin 2) (n j : ℕ) (hj : eps (n + 2*j + 1) = 0) :
    alpha eps n < 1 := bsum_lt_one _ j hj

/-- **`prop:square`, second identity (the shift).**  `α_{n+1} = {2 β_n}`, under
the nondegeneracy hypothesis `α_{n+1} < 1`. -/
theorem alpha_succ (eps : ℕ → Fin 2) (n : ℕ) (hn : alpha eps (n + 1) < 1) :
    Int.fract (2 * beta eps n) = alpha eps (n + 1) := by
  rw [two_mul_beta, add_comm, Int.fract_add_natCast, Int.fract_eq_self.mpr
    ⟨alpha_nonneg eps (n+1), hn⟩]

/-- **`prop:square`, third identity.**  `ε_{n+1} = ⌊2 β_n⌋`, under the same
nondegeneracy hypothesis. -/
theorem eps_eq_floor (eps : ℕ → Fin 2) (n : ℕ) (hn : alpha eps (n + 1) < 1) :
    ⌊2 * beta eps n⌋ = ((eps n : ℕ) : ℤ) := by
  rw [two_mul_beta, add_comm, Int.floor_add_natCast,
    Int.floor_eq_zero_iff.mpr ⟨alpha_nonneg eps (n+1), hn⟩]
  simp

/-- The digit is `1` exactly when `β_n ≥ 1/2` (nondegenerate case). -/
theorem eps_eq_one_iff (eps : ℕ → Fin 2) (n : ℕ) (hn : alpha eps (n + 1) < 1) :
    eps n = 1 ↔ 1/2 ≤ beta eps n := by
  have h := two_mul_beta eps n
  have h0 := alpha_nonneg eps (n+1)
  constructor
  · intro he; rw [he] at h; norm_num at h; linarith
  · intro hb
    by_contra hne
    have he : eps n = 0 := by omega
    rw [he] at h; norm_num at h; linarith

/-! ### The position -/

/-- Shifting an itinerary along its own orbit. -/
lemma orbit_add (lam : ℝ) (eps : ℕ → Fin 2) (x : ℝ) (n m : ℕ) :
    orbit lam eps x (n + m) = orbit lam (fun k => eps (n + k)) (orbit lam eps x n) m := by
  induction m with
  | zero => simp [orbit]
  | succ m ih =>
      have : n + (m + 1) = (n + m) + 1 := by omega
      rw [this, orbit, ih, orbit]

/-- **`prop:square`, first identity.**  `x_n = (√2 − 1)(α_n + √2 β_n)`. -/
theorem pos_eq (eps : ℕ → Fin 2) (x : ℝ)
    (hb : ∀ n, orbit Sqrt2.lam2 eps x n ∈ Set.Icc (0:ℝ) 1) (n : ℕ) :
    orbit Sqrt2.lam2 eps x n = (Real.sqrt 2 - 1) * sval eps n := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  -- the shifted itinerary
  have hb' : ∀ m, orbit Sqrt2.lam2 (fun k => eps (n + k)) (orbit Sqrt2.lam2 eps x n) m
      ∈ Set.Icc (0:ℝ) 1 := by
    intro m; rw [← orbit_add]; exact hb (n + m)
  have hx := Ternary.itinerary_tsum Sqrt2.one_lt_lam2 (fun k => eps (n + k))
    (orbit Sqrt2.lam2 eps x n) hb'
  set rr : ℝ := r Sqrt2.lam2 with hrrdef
  have hrr : rr = Real.sqrt 2 / 2 := by
    rw [hrrdef, r, Sqrt2.lam2]
    rw [eq_div_iff (by norm_num : (2:ℝ) ≠ 0), inv_mul_eq_div,
      div_eq_iff (ne_of_gt Sqrt2.lam2_pos)]
    nlinarith [Sqrt2.lam2_sq]
  have hrsq : rr ^ 2 = 1/2 := by rw [hrr]; nlinarith
  have hev : ∀ i : ℕ, ((eps (n + 2*i) : ℕ) : ℝ) * rr ^ (2*i)
      = ((eps (n + 2*i) : ℕ) : ℝ) * (1/2:ℝ)^i := by
    intro i; rw [pow_mul, hrsq]
  have hod : ∀ i : ℕ, ((eps (n + (2*i+1)) : ℕ) : ℝ) * rr ^ (2*i+1)
      = rr * (((eps (n + 2*i + 1) : ℕ) : ℝ) * (1/2:ℝ)^i) := by
    intro i
    rw [show n + (2*i+1) = n + 2*i + 1 from by ring, pow_succ, pow_mul, hrsq]; ring
  have hsE : Summable (fun i : ℕ => ((eps (n + 2*i) : ℕ) : ℝ) * rr ^ (2*i)) := by
    refine ((summable_bsum (fun i => eps (n + 2*i))).mul_left 2).congr (fun i => ?_)
    rw [hev i, pow_succ]; ring
  have hsO : Summable (fun i : ℕ => ((eps (n + (2*i+1)) : ℕ) : ℝ) * rr ^ (2*i+1)) := by
    refine ((summable_bsum (fun i => eps (n + 2*i + 1))).mul_left (2*rr)).congr (fun i => ?_)
    rw [hod i, pow_succ]; ring
  have hsplit := tsum_even_add_odd (f := fun k : ℕ => ((eps (n + k) : ℕ) : ℝ) * rr ^ k) hsE hsO
  have hE : ∑' i : ℕ, ((eps (n + 2*i) : ℕ) : ℝ) * rr ^ (2*i)
      = 2 * beta eps n := by
    rw [beta, ← bsum_two]; exact tsum_congr hev
  have hO : ∑' i : ℕ, ((eps (n + (2*i+1)) : ℕ) : ℝ) * rr ^ (2*i+1)
      = rr * (2 * alpha eps n) := by
    rw [alpha, ← bsum_two, ← tsum_mul_left]; exact tsum_congr hod
  rw [hE, hO] at hsplit
  rw [sval, hx, ← hsplit, hrr]
  linear_combination (-(beta eps n + alpha eps n / 2)) * h2

/-- **`prop:square`**, the three identities together. -/
theorem square_normal_form (eps : ℕ → Fin 2) (x : ℝ)
    (hb : ∀ n, orbit Sqrt2.lam2 eps x n ∈ Set.Icc (0:ℝ) 1) (n : ℕ)
    (hn : alpha eps (n + 1) < 1) :
    orbit Sqrt2.lam2 eps x n
        = (Real.sqrt 2 - 1) * (alpha eps n + Real.sqrt 2 * beta eps n) ∧
      alpha eps (n + 1) = Int.fract (2 * beta eps n) ∧
      beta eps (n + 1) = alpha eps n ∧
      ((eps n : ℕ) : ℤ) = ⌊2 * beta eps n⌋ :=
  ⟨pos_eq eps x hb n, (alpha_succ eps n hn).symm, beta_succ eps n, (eps_eq_floor eps n hn).symm⟩

/-! ### The survival table -/

/-- The move `m` *spares* a knot at `x` and induces branch `e`. -/
def Spares (lam x : ℝ) (e : Fin 2) (m : Move) : Prop :=
  survives lam m x ∧ branch lam m x = e

/-- Region `(0, g)`: only `M` and `R` spare the knot, and both induce branch
`0`. -/
theorem spares_region₁ (lam x : ℝ) (h : 1 < lam) (hxg : x ≤ g lam) (hxr : x < r lam / 2) :
    {m | Spares lam x 0 m} = {Move.M, Move.R} ∧ {m | Spares lam x 1 m} = ∅ := by
  have hr0 : 0 < r lam := r_pos lam h
  constructor
  · ext m; cases m <;> simp [Spares, branch, survives, hxr]; linarith
  · ext m; cases m <;> simp [Spares, branch, survives, hxr]; linarith

/-- Region `(g, r/2)`: branch `0` is induced by `M` and `R`, branch `1` by
`L`. -/
theorem spares_region₂ (lam x : ℝ) (h : 1 < lam) (hxg : g lam < x) (hxr : x < r lam / 2) :
    {m | Spares lam x 0 m} = {Move.M, Move.R} ∧ {m | Spares lam x 1 m} = {Move.L} := by
  have hr0 : 0 < r lam := r_pos lam h
  constructor
  · ext m; cases m <;> simp [Spares, branch, survives, hxr, hxg]; linarith
  · ext m; cases m <;> simp [Spares, branch, survives, hxr, hxg]

/-- Region `(r/2, 1 − r/2)`: `M` kills; branch `0` is induced by `R` alone and
branch `1` by `L` alone. -/
theorem spares_region₃ (lam x : ℝ) (hxg : g lam < x) (hxr : x < r lam)
    (h1 : r lam / 2 ≤ x) (h2 : x ≤ 1 - r lam / 2) :
    {m | Spares lam x 0 m} = {Move.R} ∧ {m | Spares lam x 1 m} = {Move.L} := by
  have hn1 : ¬ (x < r lam / 2) := not_lt.mpr h1
  have hn2 : ¬ (1 - r lam / 2 < x) := not_lt.mpr h2
  constructor
  · ext m; cases m <;> simp [Spares, branch, survives, hxr, hxg, hn1, hn2]
  · ext m; cases m <;> simp [Spares, branch, survives, hxr, hxg, hn1, hn2]

/-- Region `(1 − r/2, r)`: branch `0` is induced by `R`, branch `1` by `L` and
`M`. -/
theorem spares_region₄ (lam x : ℝ) (h : 1 < lam) (hx1 : 1 - r lam / 2 < x) (hxr : x < r lam) :
    {m | Spares lam x 0 m} = {Move.R} ∧ {m | Spares lam x 1 m} = {Move.L, Move.M} := by
  have hr0 : 0 < r lam := r_pos lam h
  have hr1 : r lam < 1 := r_lt_one lam h
  have hxg : g lam < x := by unfold g; linarith
  have hnlt : ¬ x < r lam / 2 := by linarith
  constructor
  · ext m; cases m <;> simp [Spares, branch, survives, hxr, hxg, hnlt]
  · ext m; cases m <;> simp [Spares, branch, survives, hxr, hxg, hnlt, hx1]

/-- Region `(r, 1)`: `R` kills; branch `1` is induced by `L` and `M`, and no
move induces branch `0`.  Here `M` spares the knot because `x ≥ r > 1 - r/2`,
which is exactly the standing hypothesis `λ < 3/2` (equivalently `r > 2/3`);
at `λ = √2` it holds. -/
theorem spares_region₅ (lam x : ℝ) (h : 1 < lam) (hlam : lam < 3/2) (hxr : r lam ≤ x) :
    {m | Spares lam x 0 m} = ∅ ∧ {m | Spares lam x 1 m} = {Move.L, Move.M} := by
  have hr0 : 0 < r lam := r_pos lam h
  have hr1 : r lam < 1 := r_lt_one lam h
  have hrl : r lam * lam = 1 := by
    rw [r]; field_simp
  have h23 : 2/3 < r lam := by nlinarith
  have hxg : g lam < x := by unfold g; linarith
  have hnlt : ¬ x < r lam / 2 := by linarith
  have hx1 : 1 - r lam / 2 < x := by linarith
  constructor
  · ext m; cases m <;> simp [Spares, branch, survives, hxg, hnlt]; linarith
  · ext m; cases m <;> simp [Spares, branch, survives, hxg, hnlt, hx1]

/-- A move sparing the knot and inducing branch `0` exists exactly for `x < r`.
-/
theorem spares_zero_iff (lam x : ℝ) (h : 1 < lam) :
    (∃ m, Spares lam x 0 m) ↔ x < r lam := by
  have hr0 : 0 < r lam := r_pos lam h
  constructor
  · rintro ⟨m, hm⟩
    cases m
    · exact absurd hm.2 (by simp)
    · obtain ⟨hs, hbr⟩ := hm
      by_cases hx : x < r lam / 2
      · linarith
      · exact absurd hbr (by simp [branch, hx])
    · exact hm.1
  · intro hx
    exact ⟨Move.R, hx, rfl⟩

/-- A move sparing the knot and inducing branch `1` exists exactly for `g < x`.
-/
theorem spares_one_iff (lam x : ℝ) (h : 1 < lam) :
    (∃ m, Spares lam x 1 m) ↔ g lam < x := by
  have hr0 : 0 < r lam := r_pos lam h
  constructor
  · rintro ⟨m, hm⟩
    cases m
    · exact hm.1
    · obtain ⟨hs, hbr⟩ := hm
      have hx : ¬ x < r lam / 2 := by
        intro hx; exact absurd hbr (by simp [branch, hx])
      have : 1 - r lam / 2 < x := by
        rcases hs with hs | hs
        · exact absurd hs hx
        · exact hs
      unfold g; linarith
    · exact absurd hm.2 (by simp)
  · intro hx
    exact ⟨Move.L, hx, rfl⟩

/-- **`prop:squaresurv`, general form.**  A knot at `x` with required branch `e`
admits a move sparing it and inducing that branch unless `x ≤ g` and `e = 1`, or
`r ≤ x` and `e = 0`. -/
theorem squaresurv_general (lam x : ℝ) (h : 1 < lam) (e : Fin 2) :
    (∃ m, Spares lam x e m) ↔ ¬ ((x ≤ g lam ∧ e = 1) ∨ (r lam ≤ x ∧ e = 0)) := by
  have he2 : e = 0 ∨ e = 1 := by omega
  rcases he2 with rfl | rfl
  · rw [spares_zero_iff lam x h]
    constructor
    · rintro hx (⟨-, he⟩ | ⟨hr, -⟩)
      · exact absurd he (by decide)
      · linarith
    · intro hx
      by_contra hc
      exact hx (Or.inr ⟨not_lt.mp hc, rfl⟩)
  · rw [spares_one_iff lam x h]
    constructor
    · rintro hx (⟨hg, -⟩ | ⟨-, he⟩)
      · linarith
      · exact absurd he (by decide)
    · intro hx
      by_contra hc
      exact hx (Or.inl ⟨not_lt.mp hc, rfl⟩)

/-- **`prop:squaresurv`.**  In the coordinates of the binary square at
`λ = √2`: the knot with itinerary `eps` at time `n` admits a move sparing it and
inducing its required branch `ε_{n+1}` unless `s_n < 1/√2` while `β_n ≥ 1/2`,
or `s_n > (2+√2)/2` while `β_n < 1/2`.  (The position is `x_n = (√2−1) s_n`;
the hypothesis `alpha eps (n+1) < 1` is the nondegeneracy of the digit
reading, see the conventions above.) -/
theorem squaresurv (eps : ℕ → Fin 2) (x : ℝ)
    (hb : ∀ n, orbit Sqrt2.lam2 eps x n ∈ Set.Icc (0:ℝ) 1) (n : ℕ)
    (hn : alpha eps (n + 1) < 1) :
    (∃ m, Spares Sqrt2.lam2 (orbit Sqrt2.lam2 eps x n) (eps n) m) ↔
      ¬ ((sval eps n ≤ 1 / Real.sqrt 2 ∧ 1/2 ≤ beta eps n) ∨
         ((2 + Real.sqrt 2)/2 ≤ sval eps n ∧ beta eps n < 1/2)) := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2 : (1:ℝ) < Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
  have hpos : (0:ℝ) < Real.sqrt 2 - 1 := by linarith
  have hx := pos_eq eps x hb n
  have hg : g Sqrt2.lam2 = 1 - Real.sqrt 2 / 2 := Sqrt2.g_lam2
  have hr : r Sqrt2.lam2 = Real.sqrt 2 / 2 := Sqrt2.r_lam2
  rw [squaresurv_general _ _ Sqrt2.one_lt_lam2, hx, hg, hr]
  -- translate the two exceptional cases
  have hinv : (1:ℝ) / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    rw [div_eq_div_iff (by linarith) (by norm_num)]; linarith
  have hEq1 : ((Real.sqrt 2 - 1) * sval eps n ≤ 1 - Real.sqrt 2 / 2)
      ↔ (sval eps n ≤ 1 / Real.sqrt 2) := by
    rw [hinv]
    constructor <;> intro hh <;> nlinarith
  have hEq2 : ((Real.sqrt 2 / 2 : ℝ) ≤ (Real.sqrt 2 - 1) * sval eps n)
      ↔ ((2 + Real.sqrt 2)/2 ≤ sval eps n) := by
    constructor <;> intro hh <;> nlinarith
  have hb1 : (eps n = 1) ↔ 1/2 ≤ beta eps n := eps_eq_one_iff eps n hn
  have hb0 : (eps n = 0) ↔ beta eps n < 1/2 := by
    constructor
    · intro he
      by_contra hcon
      push_neg at hcon
      have h1 : eps n = 1 := hb1.mpr hcon
      rw [he] at h1; exact absurd h1 (by decide)
    · intro hlt
      by_contra hne
      have : eps n = 1 := by omega
      have := hb1.mp this
      linarith
  constructor
  · intro hnot hcase
    apply hnot
    rcases hcase with ⟨hs, hbb⟩ | ⟨hs, hbb⟩
    · exact Or.inl ⟨hEq1.mpr hs, hb1.mpr hbb⟩
    · exact Or.inr ⟨hEq2.mpr hs, hb0.mpr hbb⟩
  · intro hnot hcase
    apply hnot
    rcases hcase with ⟨hs, he⟩ | ⟨hs, he⟩
    · exact Or.inl ⟨hEq1.mp hs, hb1.mp he⟩
    · exact Or.inr ⟨hEq2.mp hs, hb0.mp he⟩

/-- **`prop:squaresurv`, the paper's "unless" direction verbatim** (with its
strict inequalities): if `s_n < 1/√2` while `β_n ≥ 1/2`, or `s_n > (2+√2)/2`
while `β_n < 1/2`, then no move both spares the knot and induces its required
branch. -/
theorem no_spare_of_exceptional (eps : ℕ → Fin 2) (x : ℝ)
    (hb : ∀ n, orbit Sqrt2.lam2 eps x n ∈ Set.Icc (0:ℝ) 1) (n : ℕ)
    (hn : alpha eps (n + 1) < 1)
    (hex : (sval eps n < 1 / Real.sqrt 2 ∧ 1/2 ≤ beta eps n) ∨
           ((2 + Real.sqrt 2)/2 < sval eps n ∧ beta eps n < 1/2)) :
    ¬ ∃ m, Spares Sqrt2.lam2 (orbit Sqrt2.lam2 eps x n) (eps n) m := by
  rw [squaresurv eps x hb n hn]
  intro hcon
  apply hcon
  rcases hex with ⟨hs, hbb⟩ | ⟨hs, hbb⟩
  · exact Or.inl ⟨le_of_lt hs, hbb⟩
  · exact Or.inr ⟨le_of_lt hs, hbb⟩

end Square
end KnotGame
