import RequestProject.ExpCert

/-!
# Doubling with a *variable* return time (round 10, for T32)

`ExpCount.Doubling lam a b T` asks that every point of `[a,b]` have two distinct
branch words **of the same length `T`** whose images return to `[a,b]`.  Above
the golden ratio this is a severe requirement: the certified two-cycle
`{1/(lam+1), lam/(lam+1)}` of `RequestProject.Branching` lies outside the
branching window, so returns are slow and irregular, and the search of round 7
finds no such certificate at any word length that the kernel can check
(see `CENSUS-round10.md`).

The requirement is easy to weaken.  For the renewal argument the two words need
not have the same length: it is enough that

* neither is a prefix of the other — here in the concrete form that they
  *diverge*, i.e. disagree at some index below both lengths (`Divergent`), which
  is what makes the two families of continuations disjoint; and
* both lengths are at most `T`, which lets `ExpCount.Kx_mono` pad the shorter
  continuation.

This is `VDoubling lam a b T`, and it yields the same conclusion
`2 ^ (m / T) ≤ K lam m` (`two_pow_le_K_of_vdoubling`).  Certificates are checked
by the interval arithmetic of `RequestProject.ExpCert`, unchanged
(`vcellOK`, `vdoubling_of_cert`); only the per-cell conditions on the two words
differ — divergence instead of inequality, and `length ≤ T` instead of
`length = T`.

## Conventions (SCRUPLES)

* `Divergent u v` is a decidable `Bool`; it is *stronger* than `u ≠ v` and than
  prefix-incomparability only in that it is stated positively, and it is exactly
  what the disjointness proof consumes (`append_ne_of_divergent`).
* The rate certified is `2 ^ (1/T)` with `T` the *worst* return time in the
  certificate, not the average; most cells return sooner.
-/

namespace KnotGame
namespace ExpVar

open KnotGame.Branching KnotGame.ExpCount KnotGame.ExpCert
open scoped Classical

variable {lam a b : ℝ} {T : ℕ}

/-! ### Divergence of two words -/

/-- `Divergent u v`: the words disagree at some index below both lengths.  Then
neither is a prefix of the other, and no two extensions of them can agree. -/
def Divergent : List (Fin 2) → List (Fin 2) → Bool
  | [], _ => false
  | _ :: _, [] => false
  | c :: u, d :: v => if c = d then Divergent u v else true

/-- Diverging words have disjoint sets of extensions. -/
lemma append_ne_of_divergent : ∀ {u v : List (Fin 2)}, Divergent u v = true →
    ∀ z1 z2 : List (Fin 2), u ++ z1 ≠ v ++ z2 := by
  intro u
  induction u with
  | nil => intro v h; simp [Divergent] at h
  | cons c u ih =>
      intro v h z1 z2
      cases v with
      | nil => simp [Divergent] at h
      | cons d v =>
          simp only [Divergent] at h
          by_cases hcd : c = d
          · rw [if_pos hcd] at h
            intro hcon
            simp only [List.cons_append, List.cons.injEq] at hcon
            exact ih h z1 z2 hcon.2
          · intro hcon
            simp only [List.cons_append, List.cons.injEq] at hcon
            exact hcd hcon.1

/-! ### The hypothesis and the renewal step -/

/-- **Doubling with a variable return time.**  Every point of `[a,b]` admits two
diverging branch words, each of length at most `T`, whose images again lie in
`[a,b]`. -/
def VDoubling (lam a b : ℝ) (T : ℕ) : Prop :=
  ∀ x : ℝ, a ≤ x → x ≤ b → ∃ u v : List (Fin 2), Divergent u v = true ∧
    u.length ≤ T ∧ v.length ≤ T ∧
    a ≤ rapp lam x u ∧ rapp lam x u ≤ b ∧ a ≤ rapp lam x v ∧ rapp lam x v ≤ b

/-- **The renewal step with a variable return time.**  Inside `[a,b]` the count
at least doubles every `T` steps. -/
lemma two_mul_kappa_le_var (h1 : 1 < lam) (h2 : lam < 2) (ha : 0 < a) (hb : b < 1)
    (hv : VDoubling lam a b T) (n : ℕ) {x : ℝ} (hx0 : a ≤ x) (hx1 : x ≤ b) :
    2 * kappa lam a b n ≤ Kx lam x (n + T) := by
  obtain ⟨u, v, hdiv, hlu, hlv, hu1, hu2, hv1, hv2⟩ := hv x hx0 hx1
  have hx0' : (0:ℝ) < x := lt_of_lt_of_le ha hx0
  have hx1' : x < 1 := lt_of_le_of_lt hx1 hb
  have hsu : bSurvives lam x u :=
    bSurvives_of_image_mem h1 hx0' hx1' (by linarith) (by linarith)
  have hsv : bSurvives lam x v :=
    bSurvives_of_image_mem h1 hx0' hx1' (by linarith) (by linarith)
  -- the two families of continuations, padded to a common total length `n + T`
  set nu := n + T - u.length with hnu
  set nv := n + T - v.length with hnv
  have hu' : nu + u.length = n + T := by omega
  have hv' : nv + v.length = n + T := by omega
  have hsubu : (SW lam (rapp lam x u) nu).image (fun z => u ++ z) ⊆ SW lam x (n + T) := by
    have := image_append_subset (T := u.length) hsu rfl nu
    rwa [hu'] at this
  have hsubv : (SW lam (rapp lam x v) nv).image (fun z => v ++ z) ⊆ SW lam x (n + T) := by
    have := image_append_subset (T := v.length) hsv rfl nv
    rwa [hv'] at this
  have hiu : Function.Injective (fun z : List (Fin 2) => u ++ z) :=
    fun z1 z2 h => List.append_cancel_left h
  have hiv : Function.Injective (fun z : List (Fin 2) => v ++ z) :=
    fun z1 z2 h => List.append_cancel_left h
  have hdisj : Disjoint ((SW lam (rapp lam x u) nu).image (fun z => u ++ z))
      ((SW lam (rapp lam x v) nv).image (fun z => v ++ z)) := by
    rw [Finset.disjoint_left]
    rintro c hc hc'
    simp only [Finset.mem_image] at hc hc'
    obtain ⟨z1, -, rfl⟩ := hc
    obtain ⟨z2, -, h2'⟩ := hc'
    exact append_ne_of_divergent hdiv z1 z2 h2'.symm
  -- padding the shorter of the two continuations
  have hpadu : kappa lam a b n ≤ Kx lam (rapp lam x u) nu := by
    refine le_trans (kappa_le hu1 hu2 n) (Kx_mono h1 h2 ?_ ?_ (by omega))
    · linarith
    · linarith
  have hpadv : kappa lam a b n ≤ Kx lam (rapp lam x v) nv := by
    refine le_trans (kappa_le hv1 hv2 n) (Kx_mono h1 h2 ?_ ?_ (by omega))
    · linarith
    · linarith
  calc 2 * kappa lam a b n = kappa lam a b n + kappa lam a b n := by ring
    _ ≤ Kx lam (rapp lam x u) nu + Kx lam (rapp lam x v) nv := Nat.add_le_add hpadu hpadv
    _ = ((SW lam (rapp lam x u) nu).image (fun z => u ++ z)).card +
          ((SW lam (rapp lam x v) nv).image (fun z => v ++ z)).card := by
        rw [Finset.card_image_of_injective _ hiu, Finset.card_image_of_injective _ hiv]; rfl
    _ = (((SW lam (rapp lam x u) nu).image (fun z => u ++ z)) ∪
          ((SW lam (rapp lam x v) nv).image (fun z => v ++ z))).card :=
        (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ Kx lam x (n + T) := Finset.card_le_card (Finset.union_subset hsubu hsubv)

lemma two_pow_le_kappa_var (h1 : 1 < lam) (h2 : lam < 2) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hv : VDoubling lam a b T) (j : ℕ) : 2 ^ j ≤ kappa lam a b (T * j) := by
  induction j with
  | zero =>
      refine le_kappa hab (fun x _ _ => ?_)
      rw [Nat.mul_zero, pow_zero, Kx_zero]
  | succ j ih =>
      have h5 : T * (j + 1) = T * j + T := by ring
      rw [h5]
      refine le_kappa hab (fun x hx1 hx2 => ?_)
      calc 2 ^ (j + 1) = 2 * 2 ^ j := by ring
        _ ≤ 2 * kappa lam a b (T * j) := Nat.mul_le_mul_left 2 ih
        _ ≤ Kx lam x (T * j + T) := two_mul_kappa_le_var h1 h2 ha hb hv (T * j) hx1 hx2

/-- **From variable-time doubling to an exponential count.**  If every point of a
closed interval `[a,b] ⊆ (0,1)` containing `1/2` has two diverging legal
continuations of length at most `T` returning to `[a,b]`, then
`K lam m ≥ 2 ^ (m / T)`. -/
theorem two_pow_le_K_of_vdoubling (h1 : 1 < lam) (h2 : lam < 2) (ha : 0 < a) (hb : b < 1)
    (ha2 : a ≤ 1/2) (hb2 : (1/2 : ℝ) ≤ b) (hv : VDoubling lam a b T) (m : ℕ) :
    2 ^ (m / T) ≤ K lam m := by
  have hab : a ≤ b := le_trans ha2 hb2
  rw [← Kx_eq_K]
  calc 2 ^ (m / T) ≤ kappa lam a b (T * (m / T)) := two_pow_le_kappa_var h1 h2 ha hb hab hv _
    _ ≤ Kx lam (1/2 : ℝ) (T * (m / T)) := kappa_le ha2 hb2 _
    _ ≤ Kx lam (1/2 : ℝ) m := by
        refine Kx_mono h1 h2 (by linarith) (by linarith) ?_
        calc T * (m / T) = m / T * T := Nat.mul_comm _ _
          _ ≤ m := Nat.div_mul_le_self m T

/-! ### Certificates -/

/-- A cell is valid for the variable-time property: two diverging words of length
at most `T` whose enclosures over the cell, for every parameter in `[l0,l1]`, lie
inside `[a,b]`. -/
def vcellOK (l0 l1 a b : ℚ) (T : ℕ) (c : Cell) : Bool :=
  Divergent c.2.2.1 c.2.2.2 && decide (c.2.2.1.length ≤ T) && decide (c.2.2.2.length ≤ T) &&
    iok l0 l1 a b c.2.2.1 c.1 c.2.1 && iok l0 l1 a b c.2.2.2 c.1 c.2.1

/-- **A certificate yields the variable-time doubling property**, for every
parameter in the certified interval. -/
theorem vdoubling_of_cert {l0 l1 a' b' : ℚ} {T : ℕ} {cs : List Cell} {lam : ℝ}
    (hl0 : (0:ℚ) < l0) (hlam0 : ((l0 : ℚ) : ℝ) ≤ lam) (hlam1 : lam ≤ ((l1 : ℚ) : ℝ))
    (hch : chained a' cs b' = true) (hne : cs ≠ [])
    (hall : cs.all (vcellOK l0 l1 a' b' T) = true) :
    VDoubling lam ((a' : ℚ) : ℝ) ((b' : ℚ) : ℝ) T := by
  intro x hxa hxb
  obtain ⟨c, hc, hp, hq⟩ := exists_cell hch hne hxa hxb
  have hok : vcellOK l0 l1 a' b' T c = true := (List.all_eq_true.1 hall) c hc
  simp only [vcellOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨hdiv, hlu⟩, hlv⟩, hu⟩, hv⟩ := hok
  have hl0' : (0:ℝ) < ((l0 : ℚ) : ℝ) := by exact_mod_cast hl0
  obtain ⟨hu1, hu2⟩ := rapp_mem_of_iok hlam0 hlam1 hl0' c.2.2.1 c.1 c.2.1 x hp hq hu
  obtain ⟨hv1, hv2⟩ := rapp_mem_of_iok hlam0 hlam1 hl0' c.2.2.2 c.1 c.2.1 x hp hq hv
  exact ⟨c.2.2.1, c.2.2.2, hdiv, hlu, hlv, hu1, hu2, hv1, hv2⟩

/-- A parameter cell: a parameter interval `[l0,l1]` together with a list of
point cells tiling `[a,b]`. -/
abbrev VLamCell := ℚ × ℚ × List Cell

/-- Validity of one parameter cell against the target interval `[a,b]` and the
return-time bound `T`. -/
def vlamCellOK (a b : ℚ) (T : ℕ) (c : VLamCell) : Bool :=
  decide (0 < c.1) && chained a c.2.2 b && decide (c.2.2 ≠ []) &&
    c.2.2.all (vcellOK c.1 c.2.1 a b T)

/-- **A parameter-window certificate yields the variable-time doubling
property** at every parameter of the window. -/
theorem vdoubling_of_window {a' b' L0 L1 : ℚ} {T : ℕ} {cs : List VLamCell} {lam : ℝ}
    (hch : chained L0 cs L1 = true) (hne : cs ≠ [])
    (hall : cs.all (vlamCellOK a' b' T) = true)
    (h0 : ((L0 : ℚ) : ℝ) ≤ lam) (h1 : lam ≤ ((L1 : ℚ) : ℝ)) :
    VDoubling lam ((a' : ℚ) : ℝ) ((b' : ℚ) : ℝ) T := by
  obtain ⟨c, hc, hp, hq⟩ := exists_cell hch hne h0 h1
  have hok : vlamCellOK a' b' T c = true := (List.all_eq_true.1 hall) c hc
  simp only [vlamCellOK, Bool.and_eq_true, decide_eq_true_eq, ne_eq] at hok
  obtain ⟨⟨⟨hl0, hchain⟩, hnec⟩, hcells⟩ := hok
  exact vdoubling_of_cert hl0 hp hq hchain hnec hcells

end ExpVar
end KnotGame
