import RequestProject.TransversalityChecker

/-!
# Soundness of the integer bounds used by the checker

Each quantity computed by the checker is shown to bound the corresponding real
quantity in the safe direction:

* `BP_ge`, `DS_ge`, `DD_ge` — the bound arrays are upper bounds (all divisions
  are rounded up);
* `XGS_le`, `XGS_ge` — the rounded powers of the cell midpoint are below the
  true powers, and within `4` of them;
* `TAn_ge`, `TBn_ge` — the two thresholds dominate `δ` plus the variation over
  the cell plus the tail, with the slacks `SLA`, `SLB` to spare.
-/

namespace KnotGame
namespace Transversality

open Finset

lemma Qn_pos : 0 < Qn := by norm_num [Qn]

lemma Qn_posR : (0:ℝ) < (Qn : ℝ) := by norm_num [Qn]

lemma cdiv_ge_nat (x d : ℕ) (hd : 0 < d) : x ≤ cdiv x d * d := by
  unfold cdiv
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · have h1 : x + d - 1 = (x - 1) + d := by omega
    rw [h1, Nat.add_div_right _ hd]
    have h2 : (x - 1) / d * d + (x-1) % d = x - 1 := Nat.div_add_mod' (x-1) d
    have h3 : (x - 1) % d < d := Nat.mod_lt _ hd
    have h4 : ((x-1)/d + 1) * d = (x-1)/d * d + d := by ring
    omega

lemma cdiv_ge (x d : ℕ) (hd : 0 < d) : (x : ℝ) ≤ (cdiv x d : ℝ) * d := by
  have := cdiv_ge_nat x d hd
  exact_mod_cast this

lemma nat_div_le (a d : ℕ) : ((a / d : ℕ) : ℝ) ≤ (a : ℝ) / d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · rw [le_div_iff₀ (by exact_mod_cast hd)]
    exact_mod_cast Nat.div_mul_le_self a d

lemma le_nat_div_add_one (a d : ℕ) (hd : 0 < d) : (a : ℝ) / d ≤ ((a / d : ℕ) : ℝ) + 1 := by
  have hdm : a / d * d + a % d = a := Nat.div_add_mod' a d
  have hlt : a % d < d := Nat.mod_lt a hd
  have hexp : (a / d + 1) * d = a / d * d + d := by ring
  have h : a < (a / d + 1) * d := by omega
  have hdR : (0:ℝ) < (d : ℝ) := by exact_mod_cast hd
  rw [div_le_iff₀ hdR]
  have : (a : ℝ) ≤ (((a / d : ℕ) : ℝ) + 1) * d := by exact_mod_cast h.le
  linarith

section Cell

variable {an bn mn : ℕ}

/-- `BP` bounds the powers of the right endpoint from above. -/
lemma BP_ge (i : ℕ) : (Scn : ℝ) * ((bn:ℝ)/Qn) ^ i ≤ (BP bn i : ℝ) := by
  induction i with
  | zero => simp [BP]
  | succ i ih =>
      have hQ : (0:ℝ) < (Qn:ℝ) := Qn_posR
      have h1 : ((BP bn i : ℝ) * (bn:ℝ)) ≤ (BP bn (i+1) : ℝ) * Qn := by
        have h := cdiv_ge (BP bn i * bn) Qn Qn_pos
        have hbp : BP bn (i+1) = cdiv (BP bn i * bn) Qn := rfl
        rw [hbp]
        push_cast at h ⊢
        exact h
      have hbn : (0:ℝ) ≤ (bn:ℝ) := Nat.cast_nonneg _
      have h2 : (Scn:ℝ) * ((bn:ℝ)/Qn)^i * (bn:ℝ) ≤ (BP bn i : ℝ) * (bn:ℝ) := by nlinarith
      have key : (Scn:ℝ) * ((bn:ℝ)/Qn)^(i+1) * Qn ≤ (BP bn (i+1):ℝ) * Qn := by
        have heq : (Scn:ℝ) * ((bn:ℝ)/Qn)^(i+1) * Qn = (Scn:ℝ) * ((bn:ℝ)/Qn)^i * (bn:ℝ) := by
          rw [pow_succ]
          field_simp
        rw [heq]
        linarith
      exact le_of_mul_le_mul_right key hQ

/-- `DS` bounds `∑ j b^{j-1}` from above. -/
lemma DS_ge (i : ℕ) :
    (Scn : ℝ) * (∑ j ∈ range (i+1), (j:ℝ) * ((bn:ℝ)/Qn)^(j-1)) ≤ (DS bn i : ℝ) := by
  induction i with
  | zero => simp [DS]
  | succ i ih =>
      have hb := BP_ge (bn := bn) i
      rw [Finset.sum_range_succ]
      have hcast : ((i+1 : ℕ) : ℝ) * ((bn:ℝ)/Qn)^((i+1) - 1) = ((i:ℝ)+1) * ((bn:ℝ)/Qn)^i := by
        push_cast
        simp
      rw [hcast, mul_add]
      have hDS : DS bn (i+1) = DS bn i + (i+1) * BP bn i := rfl
      rw [hDS]
      have hi : (0:ℝ) ≤ (i:ℝ) + 1 := by positivity
      have hterm : (Scn:ℝ) * (((i:ℝ)+1) * ((bn:ℝ)/Qn)^i) ≤ ((i:ℝ)+1) * (BP bn i : ℝ) := by
        nlinarith
      push_cast
      linarith

/-- `DD` bounds `∑ j (j-1) b^{j-2}` from above. -/
lemma DD_ge (i : ℕ) :
    (Scn : ℝ) * (∑ j ∈ range (i+1), ((j * (j-1) : ℕ):ℝ) * ((bn:ℝ)/Qn)^(j-2)) ≤ (DD bn i : ℝ) := by
  induction i with
  | zero => simp [DD]
  | succ i ih =>
      have hb := BP_ge (bn := bn) (i - 1)
      rw [Finset.sum_range_succ]
      have hexp : (i + 1) - 2 = i - 1 := by omega
      have hcast : (((i+1) * ((i+1)-1) : ℕ):ℝ) = ((i:ℝ)+1) * (i:ℝ) := by
        push_cast
        simp
      rw [hexp, hcast, mul_add]
      have hDD : DD bn (i+1) = DD bn i + (i+1) * i * BP bn (i - 1) := rfl
      rw [hDD]
      have hi : (0:ℝ) ≤ ((i:ℝ)+1) * (i:ℝ) := by positivity
      have hterm : (Scn:ℝ) * (((i:ℝ)+1) * (i:ℝ) * ((bn:ℝ)/Qn)^(i-1))
          ≤ ((i:ℝ)+1) * (i:ℝ) * (BP bn (i-1) : ℝ) := by
        nlinarith
      push_cast at ih ⊢
      linarith

/-- The rounded powers of the midpoint are below the true ones. -/
lemma XGS_le (i : ℕ) : (XGS mn i : ℝ) ≤ (Scn : ℝ) * ((mn:ℝ)/Qn) ^ i := by
  induction i with
  | zero => simp [XGS]
  | succ i ih =>
      have hXGS : XGS mn (i+1) = XGS mn i * mn / Qn := rfl
      rw [hXGS]
      refine le_trans (nat_div_le _ _) ?_
      have hQ : (0:ℝ) < (Qn:ℝ) := Qn_posR
      rw [div_le_iff₀ hQ]
      have hmn : (0:ℝ) ≤ (mn:ℝ) := Nat.cast_nonneg _
      have h2 : (XGS mn i : ℝ) * (mn:ℝ) ≤ (Scn:ℝ) * ((mn:ℝ)/Qn)^i * (mn:ℝ) := by nlinarith
      have heq : (Scn:ℝ) * ((mn:ℝ)/Qn)^(i+1) * Qn = (Scn:ℝ) * ((mn:ℝ)/Qn)^i * (mn:ℝ) := by
        rw [pow_succ]; field_simp
      push_cast
      rw [heq]
      exact h2

/-- The rounded powers of the midpoint are within `4` of the true ones. -/
lemma XGS_ge (h34 : 4 * mn ≤ 3 * Qn) (i : ℕ) :
    (Scn : ℝ) * ((mn:ℝ)/Qn) ^ i ≤ (XGS mn i : ℝ) + 4 := by
  have hmQ : (mn:ℝ)/Qn ≤ 3/4 := by
    rw [div_le_iff₀ Qn_posR]
    have : (4:ℝ) * (mn:ℝ) ≤ 3 * (Qn:ℝ) := by exact_mod_cast h34
    linarith
  have hm0 : (0:ℝ) ≤ (mn:ℝ)/Qn := by positivity
  induction i with
  | zero => simp [XGS]
  | succ i ih =>
      have hXGS : XGS mn (i+1) = XGS mn i * mn / Qn := rfl
      have hQ : (0:ℝ) < (Qn:ℝ) := Qn_posR
      have hstep : ((XGS mn i : ℝ) * (mn:ℝ))/Qn ≤ (XGS mn (i+1) : ℝ) + 1 := by
        rw [hXGS]
        have h := le_nat_div_add_one (XGS mn i * mn) Qn Qn_pos
        push_cast at h ⊢
        exact h
      have hmn : (0:ℝ) ≤ (mn:ℝ) := Nat.cast_nonneg _
      have h2 : ((Scn:ℝ) * ((mn:ℝ)/Qn)^i - 4) * (mn:ℝ) ≤ (XGS mn i : ℝ) * (mn:ℝ) := by nlinarith
      have h3 : ((Scn:ℝ) * ((mn:ℝ)/Qn)^i - 4) * ((mn:ℝ)/Qn) ≤ (XGS mn (i+1) : ℝ) + 1 := by
        have hdiv : ((Scn:ℝ) * ((mn:ℝ)/Qn)^i - 4) * ((mn:ℝ)/Qn)
            = (((Scn:ℝ) * ((mn:ℝ)/Qn)^i - 4) * (mn:ℝ))/Qn := by
          field_simp
        rw [hdiv]
        refine le_trans (div_le_div_of_nonneg_right h2 hQ.le) hstep
      have h4 : (4:ℝ) * ((mn:ℝ)/Qn) ≤ 3 := by linarith
      have heq : (Scn:ℝ) * ((mn:ℝ)/Qn)^(i+1) = ((Scn:ℝ) * ((mn:ℝ)/Qn)^i) * ((mn:ℝ)/Qn) := by
        rw [pow_succ]; ring
      rw [heq]
      nlinarith

lemma XGS_le_Scn (hmq : mn ≤ Qn) (i : ℕ) : XGS mn i ≤ Scn := by
  induction i with
  | zero => simp [XGS]
  | succ i ih =>
      have hXGS : XGS mn (i+1) = XGS mn i * mn / Qn := rfl
      rw [hXGS]
      refine le_trans ?_ ih
      calc XGS mn i * mn / Qn ≤ XGS mn i * Qn / Qn :=
            Nat.div_le_div_right (Nat.mul_le_mul_left _ hmq)
        _ = XGS mn i := by rw [Nat.mul_div_cancel _ Qn_pos]

/-- The basic use of `cdiv`: a real number bounded by `x / d` is bounded by `cdiv x d`. -/
lemma le_cdiv (x d : ℕ) (hd : 0 < d) {r : ℝ} (h : r * d ≤ x) : r ≤ (cdiv x d : ℝ) := by
  have hdR : (0:ℝ) < (d : ℝ) := by exact_mod_cast hd
  have h2 : (x:ℝ) ≤ (cdiv x d : ℝ) * d := cdiv_ge x d hd
  exact le_of_mul_le_mul_right (le_trans h h2) hdR

lemma deltaS_eq : (deltaS : ℝ) = (Scn : ℝ) * (1/1000) := by norm_num [deltaS, Scn]

lemma one_sub_b_inv :
    (1 - (bn:ℝ)/Qn)⁻¹ = (Qn:ℝ) / ((Qn:ℝ) - (bn:ℝ)) := by
  have hQ : (0:ℝ) < (Qn:ℝ) := Qn_posR
  have h1 : (1:ℝ) - (bn:ℝ)/Qn = ((Qn:ℝ) - bn)/Qn := by field_simp
  rw [h1, inv_div]

/-- The threshold on the value coordinate dominates `δ`, the tail and the
variation over the cell, with the slack `SLA` to spare. -/
lemma TAn_ge (hab : an ≤ bn) (hb : bn < Qn) (i : ℕ) :
    (Scn:ℝ) * (1/1000)
      + (Scn:ℝ) * (((bn:ℝ)/Qn)^(i+1) * (1 - (bn:ℝ)/Qn)⁻¹)
      + (Scn:ℝ) * ((∑ j ∈ range (i+1), (j:ℝ) * ((bn:ℝ)/Qn)^(j-1)) * (((bn:ℝ) - an)/(2*Qn)))
      + (SLA : ℝ) ≤ (TAn an bn i : ℝ) := by
  have hQ : (0:ℝ) < (Qn:ℝ) := Qn_posR
  have hlt : (bn:ℝ) < (Qn:ℝ) := by exact_mod_cast hb
  have hba : (an:ℝ) ≤ (bn:ℝ) := by exact_mod_cast hab
  have ht1 : (Scn:ℝ) * ((∑ j ∈ range (i+1), (j:ℝ) * ((bn:ℝ)/Qn)^(j-1)) * (((bn:ℝ) - an)/(2*Qn)))
      ≤ (cdiv (DS bn i * (bn - an)) (2 * Qn) : ℝ) := by
    refine le_cdiv _ _ (by omega) ?_
    have hDS := DS_ge (bn := bn) i
    set S : ℝ := ∑ j ∈ range (i+1), (j:ℝ) * ((bn:ℝ)/Qn)^(j-1) with hSdef
    have hsum : (0:ℝ) ≤ (bn:ℝ) - an := by linarith
    have hcast : ((DS bn i * (bn - an) : ℕ) : ℝ) = (DS bn i : ℝ) * ((bn:ℝ) - an) := by
      push_cast [Nat.cast_sub hab]; ring
    have hlhs : (Scn:ℝ) * (S * (((bn:ℝ) - an)/(2*(Qn:ℝ)))) * ((2 * Qn : ℕ) : ℝ)
        = ((Scn:ℝ) * S) * ((bn:ℝ) - an) := by
      push_cast
      field_simp
    rw [hcast, hlhs]
    exact mul_le_mul_of_nonneg_right hDS hsum
  have ht2 : (Scn:ℝ) * (((bn:ℝ)/Qn)^(i+1) * (1 - (bn:ℝ)/Qn)⁻¹)
      ≤ (cdiv (BP bn (i+1) * Qn) (Qn - bn) : ℝ) := by
    refine le_cdiv _ _ (by omega) ?_
    have hBP := BP_ge (bn := bn) (i+1)
    have hpos : (0:ℝ) < (Qn:ℝ) - bn := by linarith
    rw [one_sub_b_inv]
    push_cast [Nat.cast_sub hb.le]
    have heq : (Scn:ℝ) * (((bn:ℝ)/Qn)^(i+1) * ((Qn:ℝ)/((Qn:ℝ) - bn))) * ((Qn:ℝ) - bn)
        = (Scn:ℝ) * ((bn:ℝ)/Qn)^(i+1) * (Qn:ℝ) := by
      field_simp
    rw [heq]
    nlinarith
  have hT : (TAn an bn i : ℝ)
      = (deltaS : ℝ) + (cdiv (DS bn i * (bn - an)) (2 * Qn) : ℝ)
        + (cdiv (BP bn (i+1) * Qn) (Qn - bn) : ℝ) + (SLA : ℝ) := by
    simp only [TAn]; push_cast; ring
  rw [hT, deltaS_eq]
  linarith

/-- The threshold on the derivative coordinate dominates `δ`, the derivative
tail and the variation of the derivative over the cell, with the slack `SLB`
to spare. -/
lemma TBn_ge (hab : an ≤ bn) (hb : bn < Qn) (i : ℕ) :
    (Scn:ℝ) * (1/1000)
      + (Scn:ℝ) * (((i:ℝ) + 1) * ((bn:ℝ)/Qn)^i * (1 - (bn:ℝ)/Qn)⁻¹ ^ 2)
      + (Scn:ℝ) * ((∑ j ∈ range (i+1), ((j * (j-1) : ℕ) : ℝ) * ((bn:ℝ)/Qn)^(j-2))
          * (((bn:ℝ) - an)/(2*Qn)))
      + (SLB : ℝ) ≤ (TBn an bn i : ℝ) := by
  have hQ : (0:ℝ) < (Qn:ℝ) := Qn_posR
  have hlt : (bn:ℝ) < (Qn:ℝ) := by exact_mod_cast hb
  have hba : (an:ℝ) ≤ (bn:ℝ) := by exact_mod_cast hab
  have ht1 : (Scn:ℝ) * ((∑ j ∈ range (i+1), ((j * (j-1) : ℕ) : ℝ) * ((bn:ℝ)/Qn)^(j-2))
        * (((bn:ℝ) - an)/(2*Qn)))
      ≤ (cdiv (DD bn i * (bn - an)) (2 * Qn) : ℝ) := by
    refine le_cdiv _ _ (by omega) ?_
    have hDD := DD_ge (bn := bn) i
    set S : ℝ := ∑ j ∈ range (i+1), ((j * (j-1) : ℕ) : ℝ) * ((bn:ℝ)/Qn)^(j-2) with hSdef
    have hsum : (0:ℝ) ≤ (bn:ℝ) - an := by linarith
    have hcast : ((DD bn i * (bn - an) : ℕ) : ℝ) = (DD bn i : ℝ) * ((bn:ℝ) - an) := by
      push_cast [Nat.cast_sub hab]; ring
    have hlhs : (Scn:ℝ) * (S * (((bn:ℝ) - an)/(2*(Qn:ℝ)))) * ((2 * Qn : ℕ) : ℝ)
        = ((Scn:ℝ) * S) * ((bn:ℝ) - an) := by
      push_cast
      field_simp
    rw [hcast, hlhs]
    exact mul_le_mul_of_nonneg_right hDD hsum
  have ht2 : (Scn:ℝ) * (((i:ℝ) + 1) * ((bn:ℝ)/Qn)^i * (1 - (bn:ℝ)/Qn)⁻¹ ^ 2)
      ≤ (cdiv ((i + 1) * BP bn i * Qn * Qn) ((Qn - bn) * (Qn - bn)) : ℝ) := by
    refine le_cdiv _ _ (by
      have hp : 0 < Qn - bn := by omega
      exact Nat.mul_pos hp hp) ?_
    have hBP := BP_ge (bn := bn) i
    have hpos : (0:ℝ) < (Qn:ℝ) - bn := by linarith
    rw [one_sub_b_inv]
    push_cast [Nat.cast_sub hb.le]
    have heq : (Scn:ℝ) * (((i:ℝ) + 1) * ((bn:ℝ)/Qn)^i * ((Qn:ℝ)/((Qn:ℝ) - bn)) ^ 2)
          * (((Qn:ℝ) - bn) * ((Qn:ℝ) - bn))
        = ((i:ℝ) + 1) * ((Scn:ℝ) * ((bn:ℝ)/Qn)^i) * (Qn:ℝ) * (Qn:ℝ) := by
      field_simp
    rw [heq]
    gcongr
  have hT : (TBn an bn i : ℝ)
      = (deltaS : ℝ) + (cdiv (DD bn i * (bn - an)) (2 * Qn) : ℝ)
        + (cdiv ((i + 1) * BP bn i * Qn * Qn) ((Qn - bn) * (Qn - bn)) : ℝ) + (SLB : ℝ) := by
    simp only [TBn]; push_cast; ring
  rw [hT, deltaS_eq]
  linarith

end Cell

end Transversality
end KnotGame
