import RequestProject.Gaps

/-!
# Circle normal form (paper `prop:circle`)

Proposition 4 of *Knot counts in an interval deletion game* (`prop:circle`)
puts the three moves into a single normal form.  Identifying the endpoints of
`[0,1]` turns the strip into a circle carrying a marked point — the seam — and
the knots; writing `D` for

> delete the closed arc of length `g` centred at `0`, rejoin, rescale by `λ`,
> place the join at `0`, and mark it,

and `ρ_θ` for rotation by `θ`, the proposition reads

  `L = D ∘ ρ_{−g/2}`,  `R = D ∘ ρ_{g/2}`,  `M = ρ_{−1/2} ∘ D ∘ ρ_{−1/2}`,

and the number of knots is one less than the number of marked points.

**The model.**  The circle `ℝ/ℤ` is represented here by its fundamental domain
`[0,1)` through `Int.fract`: a rotation is `rot θ x = fract (x + θ)` and the
deletion operator is `Dop λ y = fract (λ (fract y − g/2))`.  On the surviving
arc `(g/2, 1 − g/2)` — the complement of the deleted arc `[−g/2, g/2]` — the
inner `fract` is the identity and `λ (y − g/2)` runs over `[0, 1)`, so `Dop` is
exactly the operator `D` of the paper there (`Dop_eq`); off that arc it is a
harmless total extension, which is what lets the three identities be stated as
equations between honest functions rather than between partial ones.

The three identities are `circle_L`, `circle_R`, `circle_M`, each stated for a
knot of `(0,1)` that survives the move in question, and the count of marked
points is `card_marked`.
-/

namespace KnotGame
namespace CircleForm

variable {lam : ℝ}

/-- Rotation of the circle by `theta`. -/
noncomputable def rot (theta : ℝ) (x : ℝ) : ℝ := Int.fract (x + theta)

/-- The deletion operator `D`: delete the closed arc of length `g` centred at
`0`, rejoin, rescale by `lam`, and place the join at `0`. -/
noncomputable def Dop (lam : ℝ) (y : ℝ) : ℝ := Int.fract (lam * (Int.fract y - g lam / 2))

lemma fract_eq_self_of_mem {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) : Int.fract t = t :=
  Int.fract_eq_self.2 ⟨h0, h1⟩

/-- Reading off a value of `fract` from a representative in `[0,1)`. -/
lemma fract_eq_of_sub_int {t s : ℝ} (m : ℤ) (h : t = s + (m : ℝ)) (h0 : 0 ≤ s) (h1 : s < 1) :
    Int.fract t = s := by
  rw [h, Int.fract_add_intCast, fract_eq_self_of_mem h0 h1]

/-- On the surviving arc `D` is the affine rescaling `y ↦ λ(y − g/2)`. -/
lemma Dop_eq (h : 1 < lam) {y : ℝ} (h0 : g lam / 2 ≤ y) (h1 : y < 1 - g lam / 2) :
    Dop lam y = lam * (y - g lam / 2) := by
  have hg0 : 0 < g lam := g_pos lam h
  have hlam0 : (0:ℝ) < lam := lt_trans zero_lt_one h
  have hr : lam * r lam = 1 := lam_mul_r h
  have hgr : g lam = 1 - r lam := rfl
  have hy0 : (0:ℝ) ≤ y := le_trans (by linarith) h0
  have hy1 : y < 1 := by linarith
  rw [Dop, fract_eq_self_of_mem hy0 hy1]
  refine fract_eq_self_of_mem (by nlinarith) ?_
  have hlt : lam * (y - g lam / 2) < lam * (1 - g lam) := by
    have hyy : y - g lam / 2 < 1 - g lam := by linarith
    nlinarith
  have hone : lam * (1 - g lam) = 1 := by
    rw [hgr]; simpa using hr
  linarith

/-- **`prop:circle`, the move `L`.**  `L = D ∘ ρ_{−g/2}`. -/
theorem circle_L (h : 1 < lam) {x : ℝ} (hx1 : x < 1) (hs : survives lam Move.L x) :
    Dop lam (rot (-(g lam / 2)) x) = act lam Move.L x := by
  have hg0 : 0 < g lam := g_pos lam h
  have hgx : g lam < x := hs
  have hlamg : lam * g lam = lam - 1 := lam_mul_g h
  have hrot : rot (-(g lam / 2)) x = x - g lam / 2 :=
    fract_eq_of_sub_int 0 (by push_cast; ring) (by linarith) (by linarith)
  rw [hrot, Dop_eq h (by linarith) (by linarith), act_L]
  have hexp : lam * (x - g lam / 2 - g lam / 2) = lam * x - lam * g lam := by ring
  rw [hexp, hlamg]

/-- **`prop:circle`, the move `R`.**  `R = D ∘ ρ_{g/2}`. -/
theorem circle_R (h : 1 < lam) {x : ℝ} (hx0 : 0 < x) (hs : survives lam Move.R x) :
    Dop lam (rot (g lam / 2) x) = act lam Move.R x := by
  have hg0 : 0 < g lam := g_pos lam h
  have hxr : x < r lam := hs
  have hgr : g lam = 1 - r lam := rfl
  have hrot : rot (g lam / 2) x = x + g lam / 2 :=
    fract_eq_of_sub_int 0 (by push_cast; ring) (by linarith) (by linarith)
  rw [hrot, Dop_eq h (by linarith) (by linarith), act_R]
  ring

/-- **`prop:circle`, the move `M`.**  `M = ρ_{−1/2} ∘ D ∘ ρ_{−1/2}`. -/
theorem circle_M (h : 1 < lam) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (hs : survives lam Move.M x) :
    rot (-(1/2)) (Dop lam (rot (-(1/2)) x)) = act lam Move.M x := by
  have hg0 : 0 < g lam := g_pos lam h
  have hg1 : g lam < 1 := g_lt_one lam h
  have hr0 : 0 < r lam := r_pos lam h
  have hr1 : r lam < 1 := r_lt_one lam h
  have hlam0 : (0:ℝ) < lam := lt_trans zero_lt_one h
  have hlamr : lam * r lam = 1 := lam_mul_r h
  have hlamg : lam * g lam = lam - 1 := lam_mul_g h
  have hgr : g lam = 1 - r lam := rfl
  rcases hs with hlow | hhigh
  · -- lower branch: `x < r/2`, image `λ x`
    have hrot : rot (-(1/2)) x = x + 1/2 :=
      fract_eq_of_sub_int (-1) (by push_cast; ring) (by linarith) (by linarith)
    have hD : Dop lam (x + 1/2) = lam * x + 1/2 := by
      rw [Dop_eq h (by linarith) (by linarith [hgr])]
      have : lam * (x + 1/2 - g lam / 2) = lam * x + (lam - lam * g lam) / 2 := by ring
      rw [this, hlamg]
      ring
    have hlamx : lam * x < 1/2 := by nlinarith
    have hfin : rot (-(1/2)) (lam * x + 1/2) = lam * x :=
      fract_eq_of_sub_int 0 (by push_cast; ring) (by nlinarith) (by linarith)
    rw [hrot, hD, hfin, act_M_of_lt lam x hlow]
  · -- upper branch: `x > 1 − r/2`, image `λ x − (λ − 1)`
    have hnlt : ¬ x < r lam / 2 := by
      intro hc; linarith
    have hrot : rot (-(1/2)) x = x - 1/2 :=
      fract_eq_of_sub_int 0 (by push_cast; ring) (by linarith) (by linarith)
    have hD : Dop lam (x - 1/2) = lam * x - lam + 1/2 := by
      rw [Dop_eq h (by linarith [hgr]) (by linarith)]
      have : lam * (x - 1/2 - g lam / 2) = lam * x - (lam + lam * g lam) / 2 := by ring
      rw [this, hlamg]
      ring
    have himg : 0 < lam * x - lam + 1 := by nlinarith
    have himg1 : lam * x - lam + 1 < 1 := by nlinarith
    have hfin : rot (-(1/2)) (lam * x - lam + 1/2) = lam * x - lam + 1 :=
      fract_eq_of_sub_int (-1) (by push_cast; ring) (by linarith) (by linarith)
    rw [hrot, hD, hfin, act_M_of_gt lam x hnlt]
    ring

/-- **`prop:circle`, the count.**  The marked points are the knots together
with the seam, so their number is one more than the number of knots. -/
theorem card_marked (h : 1 < lam) (w : List Move) :
    (insert (0:ℝ) (run lam w)).card = (run lam w).card + 1 := by
  refine Finset.card_insert_of_notMem ?_
  intro h0
  exact absurd (run_subset_Ioo h w 0 h0).1 (lt_irrefl 0)

end CircleForm
end KnotGame
