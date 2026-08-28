import RequestProject.Basic

/-!
# Branching below the golden ratio — the two branching lemmas (round 4, T11)

Throughout, `lam : ℝ` with `1 < lam < 2`, and (as in `RequestProject.Basic`)

* `r lam = lam⁻¹`,
* `g lam = 1 - r lam`,
* `f lam 0 x = lam * x`, `f lam 1 x = lam * x - (lam - 1)` — the two branch maps.

A branch is *legal* at `x` exactly when its image stays in `(0,1)`: branch `0`
needs `x < r`, branch `1` needs `x > g` (`Branching.BLegal`).  The **window** is
the open interval `Window lam = (g, r)`, where both branches are legal; outside
it exactly one branch is available, so the dynamics there is *forced*.

## Conventions (SCRUPLES)

* The window is **open** at both ends: `g` itself and `r` itself are *not*
  window points.  Consequently "outside the window" means `x ≤ g` or `r ≤ x`,
  and the forced branch at `x = g` is branch `0` (legal, since `g < r`), while
  the forced branch at `x = r` is branch `1`.
* `g lam + r lam = 1`, so the midpoint `(g+r)/2` of the window is always `1/2`
  (`g_add_r`, `mid_eq_half`).  The statements below keep the form `(g+r)/2` of
  the commission; the canonical branch selector `cb` is stated with the same
  expression.  The boundary case `x = (g+r)/2` is assigned to branch `0`.

## Contents

* `no_jump_low`, `no_jump_high` (T11a) and the sharp equivalences
  `lam_mul_g_lt_r_iff`, `no_jump_high_iff`;
* `sharp_two_cycle` (T11b);
* `good_child_low`, `good_child_high`, `good_child` (T11c);
* `bounded_return_low`, `bounded_return_high` (T11d).
-/

namespace KnotGame
namespace Branching

open Set

variable {lam lam0 lam1 : ℝ}

/-! ### Elementary facts about `g` and `r` -/

lemma r_mul_self (h : 1 < lam) : r lam * lam = 1 := by
  have hpos : (0:ℝ) < lam := lt_trans zero_lt_one h
  rw [r]
  exact inv_mul_cancel₀ (ne_of_gt hpos)

lemma g_eq (lam : ℝ) : g lam = 1 - r lam := rfl

lemma g_add_r (lam : ℝ) : g lam + r lam = 1 := by
  rw [g_eq]; ring

/-- The midpoint of the window is `1/2`, for every `lam`. -/
lemma mid_eq_half (lam : ℝ) : (g lam + r lam) / 2 = 1 / 2 := by
  rw [g_add_r]

lemma g_lt_r (h1 : 1 < lam) (h2 : lam < 2) : g lam < r lam := by
  have hr := r_mul_self h1
  have hrpos : 0 < r lam := r_pos lam h1
  rw [g_eq]
  nlinarith

lemma lam_mul_g (h : 1 < lam) : lam * g lam = lam - 1 := by
  have hr := r_mul_self h
  rw [g_eq]; nlinarith

lemma lam_mul_r (h : 1 < lam) : lam * r lam = 1 := by
  have hr := r_mul_self h; linarith [hr, mul_comm (r lam) lam]

/-- The window `(g, r)`: the set of points where **both** branches are legal. -/
def Window (lam : ℝ) : Set ℝ := Set.Ioo (g lam) (r lam)

lemma mem_Window {x : ℝ} : x ∈ Window lam ↔ g lam < x ∧ x < r lam := Iff.rfl

/-- The window is symmetric about `1/2`. -/
lemma one_sub_mem_Window {x : ℝ} : (1 - x) ∈ Window lam ↔ x ∈ Window lam := by
  have h := g_add_r lam
  simp only [Window, Set.mem_Ioo]
  constructor <;> intro hx <;> constructor <;> linarith [hx.1, hx.2]

/-- `1/2` is a window point for every `lam ∈ (1,2)`. -/
lemma half_mem_Window (h1 : 1 < lam) (h2 : lam < 2) : (1/2 : ℝ) ∈ Window lam := by
  have hg := g_lt_r h1 h2
  have h := g_add_r lam
  exact ⟨by linarith, by linarith⟩

/-- A branch `e` is legal at `x` when its image stays inside `(0,1)`. -/
noncomputable def BLegal (lam : ℝ) (e : Fin 2) (x : ℝ) : Prop :=
  if e = 0 then x < r lam else g lam < x

@[simp] lemma BLegal_zero (x : ℝ) : BLegal lam 0 x ↔ x < r lam := by simp [BLegal]

@[simp] lemma BLegal_one (x : ℝ) : BLegal lam 1 x ↔ g lam < x := by simp [BLegal]

/-- Inside the window both branches are legal. -/
lemma BLegal_of_mem_Window {x : ℝ} (hx : x ∈ Window lam) (e : Fin 2) : BLegal lam e x := by
  rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl
  · simpa using hx.2
  · simpa using hx.1

/-- A legal branch keeps a point of `(0,1)` inside `(0,1)`. -/
lemma f_mem_Ioo (h : 1 < lam) {x : ℝ} (hx : x ∈ Set.Ioo (0:ℝ) 1) {e : Fin 2}
    (he : BLegal lam e x) : f lam e x ∈ Set.Ioo (0:ℝ) 1 := by
  have hlam : (0:ℝ) < lam := lt_trans zero_lt_one h
  rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl
  · rw [BLegal_zero] at he
    refine ⟨by simpa using mul_pos hlam hx.1, ?_⟩
    have : lam * x < lam * r lam := by exact mul_lt_mul_of_pos_left he hlam
    rw [lam_mul_r h] at this
    simpa using this
  · rw [BLegal_one] at he
    constructor
    · have : lam * g lam < lam * x := mul_lt_mul_of_pos_left he hlam
      rw [lam_mul_g h] at this
      simp only [f_one]; linarith
    · simp only [f_one]; nlinarith [hx.2]

/-! ### T11a — no jumping -/

/-- No *crossing from below*: `lam * g < r` holds exactly when `lam² < lam+1`.
Equivalently, a crossing `lam * g ≥ r` is possible exactly when `lam ≥ φ`. -/
lemma lam_mul_g_lt_r_iff (h : 1 < lam) : lam * g lam < r lam ↔ lam ^ 2 < lam + 1 := by
  have hr := r_mul_self h
  have hg := lam_mul_g h
  have hlam : (0:ℝ) < lam := lt_trans zero_lt_one h
  rw [hg]
  constructor
  · intro hlt; nlinarith
  · intro hlt; nlinarith

/-- No *undershoot from above*: `lam * r - (lam-1) > g` holds exactly when
`lam² < lam+1`.  Equivalently, an undershoot is possible exactly when
`lam ≥ φ`. -/
lemma no_jump_high_iff (h : 1 < lam) :
    g lam < lam * r lam - (lam - 1) ↔ lam ^ 2 < lam + 1 := by
  have hr := lam_mul_r h
  have hrs := r_mul_self h
  have hlam : (0:ℝ) < lam := lt_trans zero_lt_one h
  rw [hr, g_eq]
  constructor
  · intro hlt; nlinarith
  · intro hlt; nlinarith

/-- **T11a (no jumping), lower side.**  For `lam² < lam+1`: a forced step from
`x ≤ g` cannot overshoot the window. -/
theorem no_jump_low (h : 1 < lam) (hphi : lam ^ 2 < lam + 1) {x : ℝ} (hx : x ≤ g lam) :
    lam * x < r lam := by
  have hlam : (0:ℝ) < lam := lt_trans zero_lt_one h
  have h1 : lam * x ≤ lam * g lam := mul_le_mul_of_nonneg_left hx (le_of_lt hlam)
  exact lt_of_le_of_lt h1 ((lam_mul_g_lt_r_iff h).mpr hphi)

/-- **T11a (no jumping), upper side.**  For `lam² < lam+1`: a forced step from
`x ≥ r` cannot undershoot the window. -/
theorem no_jump_high (h : 1 < lam) (hphi : lam ^ 2 < lam + 1) {x : ℝ} (hx : r lam ≤ x) :
    g lam < lam * x - (lam - 1) := by
  have hlam : (0:ℝ) < lam := lt_trans zero_lt_one h
  have h1 : lam * r lam ≤ lam * x := mul_le_mul_of_nonneg_left hx (le_of_lt hlam)
  exact lt_of_lt_of_le ((no_jump_high_iff h).mpr hphi) (by linarith)

/-- The forced step from `x ≤ g` lands in `(0, g]` or in the window. -/
theorem forced_low_dichotomy (h : 1 < lam) (hphi : lam ^ 2 < lam + 1) {x : ℝ}
    (hx0 : 0 < x) (hx : x ≤ g lam) :
    (0 < lam * x ∧ lam * x ≤ g lam) ∨ lam * x ∈ Window lam := by
  have hlam : (0:ℝ) < lam := lt_trans zero_lt_one h
  rcases le_or_gt (lam * x) (g lam) with hle | hgt
  · exact Or.inl ⟨mul_pos hlam hx0, hle⟩
  · exact Or.inr ⟨hgt, no_jump_low h hphi hx⟩

/-! ### T11b — sharpness -/

/-- **T11b (sharpness).**  For `lam ≥ φ`, i.e. `lam + 1 ≤ lam²`, the pair
`{1/(lam+1), lam/(lam+1)}` is a 2-cycle of the forced dynamics, and both points
lie outside the window; the branch taken at each of them is the forced one. -/
theorem sharp_two_cycle (h1 : 1 < lam) (h2 : lam < 2) (hphi : lam + 1 ≤ lam ^ 2) :
    f lam 0 (1 / (lam + 1)) = lam / (lam + 1) ∧
    f lam 1 (lam / (lam + 1)) = 1 / (lam + 1) ∧
    1 / (lam + 1) ≤ g lam ∧ r lam ≤ lam / (lam + 1) ∧
    1 / (lam + 1) ∉ Window lam ∧ lam / (lam + 1) ∉ Window lam ∧
    BLegal lam 0 (1 / (lam + 1)) ∧ ¬ BLegal lam 1 (1 / (lam + 1)) ∧
    BLegal lam 1 (lam / (lam + 1)) ∧ ¬ BLegal lam 0 (lam / (lam + 1)) := by
  have hlam : (0:ℝ) < lam := lt_trans zero_lt_one h1
  have hs : (0:ℝ) < lam + 1 := by linarith
  have hr := r_mul_self h1
  have hgr := g_lt_r h1 h2
  -- the two orbit identities
  have e0 : f lam 0 (1 / (lam + 1)) = lam / (lam + 1) := by
    rw [f_zero]; field_simp
  have e1 : f lam 1 (lam / (lam + 1)) = 1 / (lam + 1) := by
    rw [f_one]; field_simp; ring
  -- the two position inequalities
  have hag : 1 / (lam + 1) ≤ g lam := by
    rw [g_eq, le_sub_iff_add_le, div_add' _ _ _ (ne_of_gt hs)]
    rw [div_le_one hs]
    nlinarith
  have hbr : r lam ≤ lam / (lam + 1) := by
    rw [le_div_iff₀ hs]
    nlinarith
  refine ⟨e0, e1, hag, hbr, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun hmem => absurd hmem.1 (not_lt.mpr hag)
  · exact fun hmem => absurd hmem.2 (not_lt.mpr hbr)
  · rw [BLegal_zero]; linarith
  · rw [BLegal_one]; exact not_lt.mpr hag
  · rw [BLegal_one]; linarith
  · rw [BLegal_zero]; exact not_lt.mpr hbr

/-! ### T11c — the good child -/

/-- The uniform distance `η = min(lam₀ − 1, (2 − lam₁)/2)` from `{0,1}`. -/
noncomputable def eta (lam0 lam1 : ℝ) : ℝ := min (lam0 - 1) ((2 - lam1) / 2)

/-- `lam < φ` forces `lam < 2`. -/
lemma lt_two_of_sq_lt (h1 : 1 < lam) (hphi : lam ^ 2 < lam + 1) : lam < 2 := by nlinarith

lemma eta_pos (h0 : 1 < lam0) (h1 : lam1 < 2) : 0 < eta lam0 lam1 :=
  lt_min (by linarith) (by linarith)

/-- If `lam ≤ lam1` and `lam1² < lam1 + 1` (with `1 < lam`) then `lam² < lam + 1`. -/
lemma sq_lt_of_le (h1 : 1 < lam) (hle : lam ≤ lam1) (hphi : lam1 ^ 2 < lam1 + 1) :
    lam ^ 2 < lam + 1 := by nlinarith

/-- `2 - lam < r lam` — the elementary fact `(lam-1)² > 0` in disguise. -/
lemma two_sub_lt_r (h1 : 1 < lam) : 2 - lam < r lam := by
  have hr := r_mul_self h1
  have hlam : (0:ℝ) < lam := lt_trans zero_lt_one h1
  nlinarith

/-- **T11c, lower half.**  From a window point `x ≤ (g+r)/2` the selected child is
`lam*x ∈ (lam-1, lam/2]`. -/
theorem good_child_low (h1 : 1 < lam) {x : ℝ} (hx : x ∈ Window lam)
    (hmid : x ≤ (g lam + r lam) / 2) :
    lam - 1 < f lam 0 x ∧ f lam 0 x ≤ lam / 2 := by
  have hlam : (0:ℝ) < lam := lt_trans zero_lt_one h1
  rw [mid_eq_half] at hmid
  refine ⟨?_, ?_⟩
  · have : lam * g lam < lam * x := mul_lt_mul_of_pos_left hx.1 hlam
    rw [lam_mul_g h1] at this
    simpa using this
  · have : lam * x ≤ lam * (1/2) := mul_le_mul_of_nonneg_left hmid (le_of_lt hlam)
    simp only [f_zero]; linarith

/-- **T11c, upper half.**  From a window point `x > (g+r)/2` the selected child is
`lam*x - (lam-1) ∈ [(2-lam)/2, 2-lam)`, and `2 - lam < r`. -/
theorem good_child_high (h1 : 1 < lam) {x : ℝ} (hx : x ∈ Window lam)
    (hmid : (g lam + r lam) / 2 < x) :
    (2 - lam) / 2 ≤ f lam 1 x ∧ f lam 1 x < 2 - lam ∧ 2 - lam < r lam := by
  have hlam : (0:ℝ) < lam := lt_trans zero_lt_one h1
  rw [mid_eq_half] at hmid
  refine ⟨?_, ?_, two_sub_lt_r h1⟩
  · have : lam * (1/2) ≤ lam * x := le_of_lt (mul_lt_mul_of_pos_left hmid hlam)
    simp only [f_one]; linarith
  · have : lam * x < lam * r lam := mul_lt_mul_of_pos_left hx.2 hlam
    rw [lam_mul_r h1] at this
    simp only [f_one]; linarith

/-- The canonical ("good child") branch selector: branch `0` below the midpoint
`(g+r)/2 = 1/2`, branch `1` above it.  Outside the window this is exactly the
forced branch. -/
noncomputable def cb (lam : ℝ) (x : ℝ) : Fin 2 := if x ≤ (g lam + r lam) / 2 then 0 else 1

lemma cb_eq_zero {x : ℝ} (hx : x ≤ (g lam + r lam) / 2) : cb lam x = 0 := by simp [cb, hx]

lemma cb_eq_one {x : ℝ} (hx : (g lam + r lam) / 2 < x) : cb lam x = 1 := by
  simp [cb, not_le.mpr hx]

/-- Outside the window the canonical branch is the forced one: at `x ≤ g` it is
branch `0`. -/
lemma cb_of_le_g (h1 : 1 < lam) (h2 : lam < 2) {x : ℝ} (hx : x ≤ g lam) : cb lam x = 0 := by
  have := g_lt_r h1 h2
  exact cb_eq_zero (by linarith)

/-- Outside the window the canonical branch is the forced one: at `x ≥ r` it is
branch `1`. -/
lemma cb_of_r_le (h1 : 1 < lam) (h2 : lam < 2) {x : ℝ} (hx : r lam ≤ x) : cb lam x = 1 := by
  have := g_lt_r h1 h2
  exact cb_eq_one (by linarith)

/-- The canonical branch is always legal. -/
lemma cb_legal (h1 : 1 < lam) (h2 : lam < 2) (x : ℝ) : BLegal lam (cb lam x) x := by
  have hgr := g_lt_r h1 h2
  rcases le_or_gt x ((g lam + r lam) / 2) with hx | hx
  · rw [cb_eq_zero hx, BLegal_zero]; linarith
  · rw [cb_eq_one hx, BLegal_one]; linarith

/-- **T11c (good child).**  For `lam ∈ [lam₀, lam₁] ⊆ (1, φ)` the canonical child
of a window point has distance at least `η = min(lam₀−1, (2−lam₁)/2)` from
`{0,1}`. -/
theorem good_child (h0 : 1 < lam0) (h0l : lam0 ≤ lam) (hl1 : lam ≤ lam1)
    (hphi1 : lam1 ^ 2 < lam1 + 1) {x : ℝ} (hx : x ∈ Window lam) :
    eta lam0 lam1 ≤ f lam (cb lam x) x ∧ f lam (cb lam x) x ≤ 1 - eta lam0 lam1 := by
  have h1 : 1 < lam := lt_of_lt_of_le h0 h0l
  have h1' : 1 < lam1 := lt_of_lt_of_le h1 hl1
  have h12 : lam1 < 2 := lt_two_of_sq_lt h1' hphi1
  have he1 : eta lam0 lam1 ≤ lam0 - 1 := min_le_left _ _
  have he2 : eta lam0 lam1 ≤ (2 - lam1) / 2 := min_le_right _ _
  rcases le_or_gt x ((g lam + r lam) / 2) with hmid | hmid
  · rw [cb_eq_zero hmid]
    obtain ⟨hlo, hhi⟩ := good_child_low h1 hx hmid
    constructor
    · linarith
    · linarith
  · rw [cb_eq_one hmid]
    obtain ⟨hlo, hhi, _⟩ := good_child_high h1 hx hmid
    constructor
    · linarith
    · linarith

/-! ### T11d — bounded return -/

/-- Iterating branch `0` is multiplication by `lam^k`. -/
lemma iterate_f_zero (lam : ℝ) (k : ℕ) (x : ℝ) : (f lam 0)^[k] x = lam ^ k * x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply, ih, f_zero]; ring

/-- Iterating branch `1` is the conjugate, by `x ↦ 1 - x`, of multiplication by
`lam^k`. -/
lemma iterate_f_one (lam : ℝ) (k : ℕ) (x : ℝ) : (f lam 1)^[k] x = 1 - lam ^ k * (1 - x) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply, ih, f_one]; ring

/-- `g` is monotone in `lam`. -/
lemma g_mono (h1 : 1 < lam) (hle : lam ≤ lam1) : g lam ≤ g lam1 := by
  have hlam : (0:ℝ) < lam := lt_trans zero_lt_one h1
  have hlam1 : (0:ℝ) < lam1 := lt_of_lt_of_le hlam hle
  have h1' : r lam1 ≤ r lam := by
    simp only [r]
    exact inv_anti₀ hlam hle
  rw [g_eq, g_eq]; linarith

/-- **T11d (bounded return), lower side.**  From `x ∈ [η, g]` the forced orbit
enters the window after at most `B` steps, all earlier iterates staying in
`(0, g]`. -/
theorem bounded_return_low {B : ℕ} (hB1 : 1 ≤ B) (h0 : 1 < lam0) (h0l : lam0 ≤ lam)
    (hl1 : lam ≤ lam1) (hphi1 : lam1 ^ 2 < lam1 + 1)
    (hB : g lam1 < lam0 ^ (B - 1) * eta lam0 lam1)
    {x : ℝ} (hx1 : eta lam0 lam1 ≤ x) (hx2 : x ≤ g lam) :
    ∃ k ≤ B, (f lam 0)^[k] x ∈ Window lam ∧
      ∀ j < k, (f lam 0)^[j] x ∈ Set.Ioc (0:ℝ) (g lam) := by
  have h1 : 1 < lam := lt_of_lt_of_le h0 h0l
  have h1' : 1 < lam1 := lt_of_lt_of_le h1 hl1
  have h12 : lam1 < 2 := lt_two_of_sq_lt h1' hphi1
  have hphi : lam ^ 2 < lam + 1 := sq_lt_of_le h1 hl1 hphi1
  have hlam : (0:ℝ) < lam := lt_trans zero_lt_one h1
  have hep : 0 < eta lam0 lam1 := eta_pos h0 h12
  have hx0 : 0 < x := lt_of_lt_of_le hep hx1
  have hgle : g lam ≤ g lam1 := g_mono h1 hl1
  -- the predicate "the `k`-th iterate has left `(0,g]`"
  have hwitness : g lam < lam ^ B * x := by
    have hpow : lam0 ^ B ≤ lam ^ B := pow_le_pow_left₀ (by linarith) h0l B
    have hmul : lam0 ^ B * eta lam0 lam1 ≤ lam ^ B * x :=
      mul_le_mul hpow hx1 (le_of_lt hep) (le_trans (by positivity) hpow)
    have hsplit : lam0 ^ B = lam0 * lam0 ^ (B - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have hgpos : 0 < g lam1 := g_pos lam1 h1'
    have : g lam1 < lam0 ^ B * eta lam0 lam1 := by
      rw [hsplit, mul_assoc]
      nlinarith [hB, h0]
    linarith
  have hexists : ∃ k, g lam < lam ^ k * x := ⟨B, hwitness⟩
  classical
  set k := Nat.find hexists with hk
  have hkspec : g lam < lam ^ k * x := Nat.find_spec hexists
  have hkle : k ≤ B := Nat.find_le hwitness
  have hbefore : ∀ j < k, lam ^ j * x ≤ g lam := by
    intro j hj
    have := Nat.find_min hexists hj
    linarith [not_lt.mp this]
  have hkpos : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exfalso; rw [h] at hkspec; simp at hkspec; linarith
    · exact h
  refine ⟨k, hkle, ?_, ?_⟩
  · rw [iterate_f_zero]
    refine ⟨hkspec, ?_⟩
    have hprev : lam ^ (k - 1) * x ≤ g lam := hbefore (k - 1) (by omega)
    have : lam ^ k * x = lam * (lam ^ (k - 1) * x) := by
      rw [← mul_assoc, ← pow_succ']
      congr 2
      omega
    rw [this]
    exact no_jump_low h1 hphi hprev
  · intro j hj
    rw [iterate_f_zero]
    exact ⟨by positivity, hbefore j hj⟩

/-- **T11d (bounded return), upper side.**  From `x ∈ [r, 1-η]` the forced orbit
under branch `1` enters the window after at most `B` steps, all earlier iterates
staying in `[r, 1)`. -/
theorem bounded_return_high {B : ℕ} (hB1 : 1 ≤ B) (h0 : 1 < lam0) (h0l : lam0 ≤ lam)
    (hl1 : lam ≤ lam1) (hphi1 : lam1 ^ 2 < lam1 + 1)
    (hB : g lam1 < lam0 ^ (B - 1) * eta lam0 lam1)
    {x : ℝ} (hx1 : r lam ≤ x) (hx2 : x ≤ 1 - eta lam0 lam1) :
    ∃ k ≤ B, (f lam 1)^[k] x ∈ Window lam ∧
      ∀ j < k, (f lam 1)^[j] x ∈ Set.Ico (r lam) 1 := by
  have h1 : 1 < lam := lt_of_lt_of_le h0 h0l
  have hgr : g lam + r lam = 1 := g_add_r lam
  have hy1 : eta lam0 lam1 ≤ 1 - x := by linarith
  have hy2 : 1 - x ≤ g lam := by linarith
  obtain ⟨k, hk, hwin, hbefore⟩ :=
    bounded_return_low hB1 h0 h0l hl1 hphi1 hB hy1 hy2
  rw [iterate_f_zero] at hwin
  refine ⟨k, hk, ?_, ?_⟩
  · rw [iterate_f_one]
    exact one_sub_mem_Window.mpr hwin
  · intro j hj
    have := hbefore j hj
    rw [iterate_f_zero] at this
    rw [iterate_f_one]
    exact ⟨by linarith [this.2], by linarith [this.1]⟩

end Branching
end KnotGame
