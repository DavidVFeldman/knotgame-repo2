import RequestProject.TransversalitySound

/-!
# Soundness of the branch-and-bound certificate for one cell (round 3, Target T9)

The checker of `RequestProject.TransversalityChecker` explores, for a cell
`[an/Qn, bn/Qn]`, the tree of coefficient prefixes `c 1, …, c Dep`.  A node at
depth `i` records the pair

  `(OFF + ⟨value of the truncation at the midpoint⟩, OFF + ⟨its derivative⟩)`

at scale `Scn`, computed with the *rounded* powers `XGS`, `XPS` of the
midpoint.  This file shows that if `c` were a counterexample to
δ-transversality inside the cell, then the node attached to its prefix of
length `i` would survive every pruning test, so all the layers would be
nonempty; `cellOK an bn = true` says that the layer at depth `Dep` is empty, and
this is the contradiction proving `cell_sound`.
-/

namespace KnotGame
namespace Transversality

open Finset

/-- The exact (integer) value coordinate of the node reached by the prefix
`c 1, …, c i`, shifted by `OFF`. -/
def SV (c : ℕ → ℤ) (mn : ℕ) : ℕ → ℤ
  | 0 => (OFF : ℤ) + (Scn : ℤ)
  | i + 1 => SV c mn i + c (i + 1) * (XGS mn (i + 1) : ℤ)

/-- The exact (integer) derivative coordinate of the node reached by the prefix
`c 1, …, c i`, shifted by `OFF`. -/
def SD (c : ℕ → ℤ) (mn : ℕ) : ℕ → ℤ
  | 0 => (OFF : ℤ)
  | i + 1 => SD c mn i + c (i + 1) * (XPS mn (i + 1) : ℤ)

lemma OFF_val : OFF = 10000000000000000000000000 := by norm_num [OFF]

lemma TCAP_val : TCAP = 100000000000000000000000 := by norm_num [TCAP]

lemma Scn_val : Scn = 1000000000000000000 := by norm_num [Scn]

lemma Dep_val : Dep = 48 := rfl

lemma Qn_val : Qn = 1024000000 := rfl

section Approx

variable {c : ℕ → ℤ} {mn : ℕ}

/-- The rounded power differs from the true one by at most `4`. -/
lemma XGS_diff (h34 : 4 * mn ≤ 3 * Qn) (j : ℕ) :
    |(XGS mn j : ℝ) - (Scn : ℝ) * ((mn : ℝ) / Qn) ^ j| ≤ 4 := by
  have h1 := XGS_le (mn := mn) j
  have h2 := XGS_ge h34 j
  rw [abs_le]
  constructor <;> linarith

/-- The integer value coordinate approximates `Scn` times the truncation at the
midpoint, with error at most `4 i`. -/
lemma SV_approx (h34 : 4 * mn ≤ 3 * Qn) (hc0 : c 0 = 1) (hc : ∀ i, |(c i : ℝ)| ≤ 1) (i : ℕ) :
    |(SV c mn i : ℝ) - OFF - (Scn : ℝ) * gpart c i ((mn : ℝ) / Qn)| ≤ 4 * i := by
  induction i with
  | zero =>
      have h0 : gpart c 0 ((mn : ℝ) / Qn) = 1 := by
        simp [gpart, hc0]
      rw [h0]
      have e1 : SV c mn 0 = (OFF : ℤ) + (Scn : ℤ) := rfl
      rw [e1]
      push_cast
      simp
  | succ i ih =>
      have hd := XGS_diff h34 (i + 1)
      have e1 : SV c mn (i + 1) = SV c mn i + c (i + 1) * (XGS mn (i + 1) : ℤ) := rfl
      have e2 : gpart c (i + 1) ((mn : ℝ) / Qn)
          = gpart c i ((mn : ℝ) / Qn) + (c (i + 1) : ℝ) * ((mn : ℝ) / Qn) ^ (i + 1) := by
        rw [gpart, gpart, Finset.sum_range_succ]
      have hstep : (SV c mn (i + 1) : ℝ) - OFF - (Scn : ℝ) * gpart c (i + 1) ((mn : ℝ) / Qn)
          = ((SV c mn i : ℝ) - OFF - (Scn : ℝ) * gpart c i ((mn : ℝ) / Qn))
            + (c (i + 1) : ℝ) * ((XGS mn (i + 1) : ℝ)
                - (Scn : ℝ) * ((mn : ℝ) / Qn) ^ (i + 1)) := by
        rw [e1, e2]
        push_cast
        ring
      rw [hstep]
      have hterm : |(c (i + 1) : ℝ) * ((XGS mn (i + 1) : ℝ)
          - (Scn : ℝ) * ((mn : ℝ) / Qn) ^ (i + 1))| ≤ 4 := by
        rw [abs_mul]
        nlinarith [abs_nonneg ((c (i + 1) : ℝ)),
          abs_nonneg ((XGS mn (i + 1) : ℝ) - (Scn : ℝ) * ((mn : ℝ) / Qn) ^ (i + 1)),
          hc (i + 1), hd]
      calc |((SV c mn i : ℝ) - OFF - (Scn : ℝ) * gpart c i ((mn : ℝ) / Qn))
              + (c (i + 1) : ℝ) * ((XGS mn (i + 1) : ℝ)
                  - (Scn : ℝ) * ((mn : ℝ) / Qn) ^ (i + 1))|
          ≤ |(SV c mn i : ℝ) - OFF - (Scn : ℝ) * gpart c i ((mn : ℝ) / Qn)|
            + |(c (i + 1) : ℝ) * ((XGS mn (i + 1) : ℝ)
                - (Scn : ℝ) * ((mn : ℝ) / Qn) ^ (i + 1))| := abs_add_le _ _
        _ ≤ 4 * i + 4 := by linarith
        _ = 4 * ((i : ℝ) + 1) := by ring
        _ = 4 * ((i + 1 : ℕ) : ℝ) := by push_cast; ring

/-- The integer derivative coordinate approximates `Scn` times the derivative of
the truncation at the midpoint, with error at most `2 i (i+1)`. -/
lemma SD_approx (h34 : 4 * mn ≤ 3 * Qn) (hc : ∀ i, |(c i : ℝ)| ≤ 1) (i : ℕ) :
    |(SD c mn i : ℝ) - OFF - (Scn : ℝ) * dpart c i ((mn : ℝ) / Qn)| ≤ 2 * i * (i + 1) := by
  induction i with
  | zero =>
      have h0 : dpart c 0 ((mn : ℝ) / Qn) = 0 := by
        simp [dpart]
      rw [h0]
      have e1 : SD c mn 0 = (OFF : ℤ) := rfl
      rw [e1]
      push_cast
      simp
  | succ i ih =>
      have hd := XGS_diff h34 i
      have e1 : SD c mn (i + 1) = SD c mn i + c (i + 1) * (XPS mn (i + 1) : ℤ) := rfl
      have eX : XPS mn (i + 1) = (i + 1) * XGS mn i := rfl
      have e2 : dpart c (i + 1) ((mn : ℝ) / Qn)
          = dpart c i ((mn : ℝ) / Qn)
            + ((i : ℝ) + 1) * (c (i + 1) : ℝ) * ((mn : ℝ) / Qn) ^ i := by
        rw [dpart, dpart, Finset.sum_range_succ]
        push_cast
        simp
      have hstep : (SD c mn (i + 1) : ℝ) - OFF - (Scn : ℝ) * dpart c (i + 1) ((mn : ℝ) / Qn)
          = ((SD c mn i : ℝ) - OFF - (Scn : ℝ) * dpart c i ((mn : ℝ) / Qn))
            + ((i : ℝ) + 1) * (c (i + 1) : ℝ)
                * ((XGS mn i : ℝ) - (Scn : ℝ) * ((mn : ℝ) / Qn) ^ i) := by
        rw [e1, e2, eX]
        push_cast
        ring
      rw [hstep]
      have hi0 : (0:ℝ) ≤ (i : ℝ) + 1 := by positivity
      have hterm : |((i : ℝ) + 1) * (c (i + 1) : ℝ)
          * ((XGS mn i : ℝ) - (Scn : ℝ) * ((mn : ℝ) / Qn) ^ i)| ≤ 4 * ((i : ℝ) + 1) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hi0]
        have hb : |(c (i + 1) : ℝ)| * |(XGS mn i : ℝ) - (Scn : ℝ) * ((mn : ℝ) / Qn) ^ i| ≤ 4 := by
          nlinarith [abs_nonneg ((c (i + 1) : ℝ)),
            abs_nonneg ((XGS mn i : ℝ) - (Scn : ℝ) * ((mn : ℝ) / Qn) ^ i), hc (i + 1), hd]
        nlinarith
      have hcast : (2:ℝ) * i * (i + 1) + 4 * ((i : ℝ) + 1)
          = 2 * ((i + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) + 1) := by push_cast; ring
      calc |((SD c mn i : ℝ) - OFF - (Scn : ℝ) * dpart c i ((mn : ℝ) / Qn))
              + ((i : ℝ) + 1) * (c (i + 1) : ℝ)
                  * ((XGS mn i : ℝ) - (Scn : ℝ) * ((mn : ℝ) / Qn) ^ i)|
          ≤ |(SD c mn i : ℝ) - OFF - (Scn : ℝ) * dpart c i ((mn : ℝ) / Qn)|
            + |((i : ℝ) + 1) * (c (i + 1) : ℝ)
                * ((XGS mn i : ℝ) - (Scn : ℝ) * ((mn : ℝ) / Qn) ^ i)| := abs_add_le _ _
        _ ≤ 2 * i * (i + 1) + 4 * ((i : ℝ) + 1) := by linarith
        _ = 2 * ((i + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) + 1) := hcast

end Approx

section Bounds

variable {an bn mn : ℕ} {c : ℕ → ℤ} {x : ℝ}

/-- The standing geometric facts about a cell of the window. -/
lemma cell_facts (hab : an ≤ bn) (hb34 : 4 * bn ≤ 3 * Qn) (hm : 2 * mn = an + bn)
    (hxa : (an : ℝ) / Qn ≤ x) (hxb : x ≤ (bn : ℝ) / Qn) :
    0 ≤ x ∧ x ≤ (bn : ℝ) / Qn ∧ (bn : ℝ) / Qn < 1 ∧ 0 ≤ (mn : ℝ) / Qn ∧
      (mn : ℝ) / Qn ≤ (bn : ℝ) / Qn ∧
      |(mn : ℝ) / Qn - x| ≤ ((bn : ℝ) - an) / (2 * Qn) := by
  have hQ : (0:ℝ) < (Qn : ℝ) := Qn_posR
  have hQn : Qn = 1024000000 := rfl
  have hbQ : bn < Qn := by omega
  have hmb : mn ≤ bn := by omega
  have hbR : (bn : ℝ) < (Qn : ℝ) := by exact_mod_cast hbQ
  have hmR : ((mn : ℝ)) ≤ (bn : ℝ) := by exact_mod_cast hmb
  have hx0 : (0:ℝ) ≤ x := le_trans (by positivity) hxa
  have hb1 : (bn : ℝ) / Qn < 1 := by
    rw [div_lt_one hQ]; exact hbR
  have hm0 : (0:ℝ) ≤ (mn : ℝ) / Qn := by positivity
  have hmb' : (mn : ℝ) / Qn ≤ (bn : ℝ) / Qn := by
    apply div_le_div_of_nonneg_right hmR hQ.le
  have hmid : 2 * (mn : ℝ) = (an : ℝ) + bn := by exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hm
  have hmx : |(mn : ℝ) / Qn - x| ≤ ((bn : ℝ) - an) / (2 * Qn) := by
    rw [abs_le]
    constructor
    · have h1 : (mn : ℝ) / Qn - x ≥ (mn : ℝ) / Qn - (bn : ℝ) / Qn := by linarith
      have h2 : (mn : ℝ) / Qn - (bn : ℝ) / Qn = -(((bn : ℝ) - an) / (2 * Qn)) := by
        field_simp
        linarith
      linarith [h1, h2.symm.le, h2.le]
    · have h1 : (mn : ℝ) / Qn - x ≤ (mn : ℝ) / Qn - (an : ℝ) / Qn := by linarith
      have h2 : (mn : ℝ) / Qn - (an : ℝ) / Qn = ((bn : ℝ) - an) / (2 * Qn) := by
        field_simp
        linarith
      linarith
  exact ⟨hx0, hxb, hb1, hm0, hmb', hmx⟩

/-- The value coordinate of the node of a counterexample stays inside the
threshold. -/
lemma SV_bound (hab : an ≤ bn) (hb34 : 4 * bn ≤ 3 * Qn) (hm : 2 * mn = an + bn)
    (hc0 : c 0 = 1) (hc : ∀ i, |(c i : ℝ)| ≤ 1)
    (hxa : (an : ℝ) / Qn ≤ x) (hxb : x ≤ (bn : ℝ) / Qn)
    (hg : |gval c x| ≤ 1 / 1000) (i : ℕ) (hi : i ≤ Dep) :
    |SV c mn i - (OFF : ℤ)| ≤ (TAn an bn i : ℤ) := by
  obtain ⟨hx0, hxb', hb1, hm0, hmb', hmx⟩ := cell_facts hab hb34 hm hxa hxb
  have hQn : Qn = 1024000000 := rfl
  have hbQ : bn < Qn := by omega
  have hmQ : 4 * mn ≤ 3 * Qn := by omega
  have htail := tail_le hc hx0 hxb' hb1 i
  have hvar := var_le hc hx0 hxb' hm0 hmb' i
  have hSnn : (0:ℝ) ≤ ∑ j ∈ range (i + 1), (j : ℝ) * ((bn : ℝ) / Qn) ^ (j - 1) := by
    refine Finset.sum_nonneg ?_
    intro j _
    have : (0:ℝ) ≤ ((bn : ℝ) / Qn) ^ (j - 1) := by positivity
    positivity
  have hvar' : |gpart c i ((mn : ℝ) / Qn) - gpart c i x|
      ≤ (∑ j ∈ range (i + 1), (j : ℝ) * ((bn : ℝ) / Qn) ^ (j - 1))
          * (((bn : ℝ) - an) / (2 * Qn)) := by
    refine le_trans hvar ?_
    exact mul_le_mul_of_nonneg_left hmx hSnn
  have htail2 : |gval c x - gpart c i x| ≤ ((bn : ℝ) / Qn) ^ (i + 1) * (1 - (bn : ℝ) / Qn)⁻¹ :=
    htail
  have hpart : |gpart c i ((mn : ℝ) / Qn)|
      ≤ 1 / 1000 + ((bn : ℝ) / Qn) ^ (i + 1) * (1 - (bn : ℝ) / Qn)⁻¹
        + (∑ j ∈ range (i + 1), (j : ℝ) * ((bn : ℝ) / Qn) ^ (j - 1))
            * (((bn : ℝ) - an) / (2 * Qn)) := by
    have h1 : |gpart c i ((mn : ℝ) / Qn)|
        ≤ |gpart c i ((mn : ℝ) / Qn) - gpart c i x| + |gpart c i x| := by
      have := abs_add_le (gpart c i ((mn : ℝ) / Qn) - gpart c i x) (gpart c i x)
      simpa using this
    have h2 : |gpart c i x| ≤ |gval c x - gpart c i x| + |gval c x| := by
      have := abs_add_le (gpart c i x - gval c x) (gval c x)
      have h3 : |gpart c i x - gval c x| = |gval c x - gpart c i x| := abs_sub_comm _ _
      simpa [h3] using this
    linarith
  have hScn : (0:ℝ) ≤ (Scn : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hpart hScn
  rw [mul_add, mul_add] at hmul
  have habs : (Scn : ℝ) * |gpart c i ((mn : ℝ) / Qn)| = |(Scn : ℝ) * gpart c i ((mn : ℝ) / Qn)| := by
    rw [abs_mul, abs_of_nonneg hScn]
  have hTA := TAn_ge (an := an) (bn := bn) hab hbQ i
  have happ := SV_approx (c := c) (mn := mn) hmQ hc0 hc i
  have hSLA : (4:ℝ) * i ≤ (SLA : ℝ) := by
    have h1 : (i : ℝ) ≤ 48 := by
      have : i ≤ 48 := hi
      exact_mod_cast this
    have h2 : (SLA : ℝ) = 196 := by norm_num [SLA, Dep]
    rw [h2]; linarith
  have hreal : |(SV c mn i : ℝ) - OFF| ≤ (TAn an bn i : ℝ) := by
    have hsplit : |(SV c mn i : ℝ) - OFF|
        ≤ |(SV c mn i : ℝ) - OFF - (Scn : ℝ) * gpart c i ((mn : ℝ) / Qn)|
          + |(Scn : ℝ) * gpart c i ((mn : ℝ) / Qn)| := by
      have := abs_add_le ((SV c mn i : ℝ) - OFF - (Scn : ℝ) * gpart c i ((mn : ℝ) / Qn))
        ((Scn : ℝ) * gpart c i ((mn : ℝ) / Qn))
      simpa using this
    rw [← habs] at hsplit
    linarith
  have : |((SV c mn i - (OFF : ℤ) : ℤ) : ℝ)| ≤ ((TAn an bn i : ℤ) : ℝ) := by
    push_cast
    push_cast at hreal
    exact hreal
  exact_mod_cast this

/-- The derivative coordinate of the node of a counterexample stays above the
threshold. -/
lemma SD_bound (hab : an ≤ bn) (hb34 : 4 * bn ≤ 3 * Qn) (hm : 2 * mn = an + bn)
    (hc : ∀ i, |(c i : ℝ)| ≤ 1)
    (hxa : (an : ℝ) / Qn ≤ x) (hxb : x ≤ (bn : ℝ) / Qn)
    (hd : -(1 / 1000) ≤ gder c x) (i : ℕ) (hi : i ≤ Dep) :
    -(TBn an bn i : ℤ) ≤ SD c mn i - (OFF : ℤ) := by
  obtain ⟨hx0, hxb', hb1, hm0, hmb', hmx⟩ := cell_facts hab hb34 hm hxa hxb
  have hQn : Qn = 1024000000 := rfl
  have hbQ : bn < Qn := by omega
  have hmQ : 4 * mn ≤ 3 * Qn := by omega
  have htail := dtail_le hc hx0 hxb' hb1 i
  have hvar := dvar_le hc hx0 hxb' hm0 hmb' i
  have hSnn : (0:ℝ) ≤ ∑ j ∈ range (i + 1), ((j * (j - 1) : ℕ) : ℝ) * ((bn : ℝ) / Qn) ^ (j - 2) := by
    refine Finset.sum_nonneg ?_
    intro j _
    have h1 : (0:ℝ) ≤ ((bn : ℝ) / Qn) ^ (j - 2) := by positivity
    positivity
  have hvar' : |dpart c i ((mn : ℝ) / Qn) - dpart c i x|
      ≤ (∑ j ∈ range (i + 1), ((j * (j - 1) : ℕ) : ℝ) * ((bn : ℝ) / Qn) ^ (j - 2))
          * (((bn : ℝ) - an) / (2 * Qn)) := by
    refine le_trans hvar ?_
    exact mul_le_mul_of_nonneg_left hmx hSnn
  have hlow : -(1 / 1000 + ((i : ℝ) + 1) * ((bn : ℝ) / Qn) ^ i * (1 - (bn : ℝ) / Qn)⁻¹ ^ 2
        + (∑ j ∈ range (i + 1), ((j * (j - 1) : ℕ) : ℝ) * ((bn : ℝ) / Qn) ^ (j - 2))
            * (((bn : ℝ) - an) / (2 * Qn)))
      ≤ dpart c i ((mn : ℝ) / Qn) := by
    have h1 := abs_le.mp htail
    have h2 := abs_le.mp hvar'
    linarith [h1.1, h1.2, h2.1, h2.2]
  have hScn : (0:ℝ) ≤ (Scn : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hlow hScn
  have hTB := TBn_ge (an := an) (bn := bn) hab hbQ i
  have happ := SD_approx (c := c) (mn := mn) hmQ hc i
  have hSLB : (2:ℝ) * i * (i + 1) ≤ (SLB : ℝ) := by
    have h1 : (i : ℝ) ≤ 48 := by
      have : i ≤ 48 := hi
      exact_mod_cast this
    have h2 : (SLB : ℝ) = 9604 := by norm_num [SLB, Dep]
    have h3 : (0:ℝ) ≤ (i : ℝ) := Nat.cast_nonneg _
    rw [h2]; nlinarith
  have happ' := abs_le.mp happ
  have hreal : -(TBn an bn i : ℝ) ≤ (SD c mn i : ℝ) - OFF := by
    nlinarith [happ'.1, hmul, hTB]
  have : (-(TBn an bn i : ℤ) : ℝ) ≤ ((SD c mn i - (OFF : ℤ) : ℤ) : ℝ) := by
    push_cast
    push_cast at hreal
    linarith
  exact_mod_cast this

end Bounds

section Lists

variable {loa hia lob xg xp : ℕ}

lemma mem_push_self {s : ℕ × ℕ} {acc : List (ℕ × ℕ)} (h : keep loa hia lob s = true) :
    s ∈ push loa hia lob s acc := by
  simp [push, h]

lemma mem_push_of_mem {s t : ℕ × ℕ} {acc : List (ℕ × ℕ)} (h : t ∈ acc) :
    t ∈ push loa hia lob s acc := by
  unfold push
  split
  · exact List.mem_cons_of_mem _ h
  · exact h

/-- The three children of a surviving node belong to the next layer. -/
lemma mem_expand {L : List (ℕ × ℕ)} {t u : ℕ × ℕ} (ht : t ∈ L)
    (hu : u = (t.1 - xg, t.2 - xp) ∨ u = t ∨ u = (t.1 + xg, t.2 + xp))
    (hk : keep loa hia lob u = true) : u ∈ expand xg xp loa hia lob L := by
  induction L with
  | nil => simp at ht
  | cons s rest ih =>
      rcases List.mem_cons.mp ht with rfl | hrest
      · rcases hu with h | h | h
        · subst h; exact mem_push_self hk
        · subst h
          exact mem_push_of_mem (mem_push_self hk)
        · subst h
          exact mem_push_of_mem (mem_push_of_mem (mem_push_self hk))
      · exact mem_push_of_mem (mem_push_of_mem (mem_push_of_mem (ih hrest)))

end Lists

section Search

variable {an bn mn : ℕ} {c : ℕ → ℤ} {x : ℝ}

/-- `capOK` gives the threshold cap at every depth below the certified one. -/
lemma capOK_le {n : ℕ} (h : capOK an bn n = true) :
    ∀ i ≤ n, TAn an bn i ≤ TCAP ∧ TBn an bn i ≤ TCAP := by
  induction n with
  | zero =>
      intro i hi
      interval_cases i
      simpa [capOK, Bool.and_eq_true, decide_eq_true_eq] using h
  | succ n ih =>
      simp only [capOK, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      intro i hi
      rcases Nat.lt_or_ge i (n + 1) with hlt | hge
      · exact ih h1 i (by omega)
      · have : i = n + 1 := by omega
        subst this
        exact ⟨h2, h3⟩

/-- The node of a counterexample survives the pruning at every depth. -/
lemma keep_state (hab : an ≤ bn) (hb34 : 4 * bn ≤ 3 * Qn) (hm : 2 * mn = an + bn)
    (hc0 : c 0 = 1) (hc : ∀ i, |(c i : ℝ)| ≤ 1)
    (hxa : (an : ℝ) / Qn ≤ x) (hxb : x ≤ (bn : ℝ) / Qn)
    (hg : |gval c x| ≤ 1 / 1000) (hd : -(1 / 1000) ≤ gder c x)
    (hcap : ∀ j ≤ Dep, TAn an bn j ≤ TCAP ∧ TBn an bn j ≤ TCAP)
    (i : ℕ) (hi : i ≤ Dep) :
    keep (OFF - TAn an bn i) (OFF + TAn an bn i) (OFF - TBn an bn i)
      ((SV c mn i).toNat, (SD c mn i).toNat) = true := by
  have hV := abs_le.mp (SV_bound hab hb34 hm hc0 hc hxa hxb hg i hi)
  have hD := SD_bound hab hb34 hm hc hxa hxb hd i hi
  obtain ⟨hA, hB⟩ := hcap i hi
  have hAZ : (TAn an bn i : ℤ) ≤ (TCAP : ℤ) := by exact_mod_cast hA
  have hBZ : (TBn an bn i : ℤ) ≤ (TCAP : ℤ) := by exact_mod_cast hB
  have hOFF : OFF = 10000000000000000000000000 := OFF_val
  have hTC : TCAP = 100000000000000000000000 := TCAP_val
  simp only [keep, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> omega

/-- The node of a counterexample belongs to every layer of the search. -/
lemma state_mem_layer (hab : an ≤ bn) (hb34 : 4 * bn ≤ 3 * Qn) (hm : 2 * mn = an + bn)
    (hc0 : c 0 = 1) (hc : ∀ i, |(c i : ℝ)| ≤ 1)
    (hxa : (an : ℝ) / Qn ≤ x) (hxb : x ≤ (bn : ℝ) / Qn)
    (hg : |gval c x| ≤ 1 / 1000) (hd : -(1 / 1000) ≤ gder c x)
    (hcap : ∀ j ≤ Dep, TAn an bn j ≤ TCAP ∧ TBn an bn j ≤ TCAP)
    (i : ℕ) (hi : i ≤ Dep) :
    ((SV c mn i).toNat, (SD c mn i).toNat) ∈ layer an bn mn i := by
  have hQn : Qn = 1024000000 := rfl
  have hmb : mn ≤ Qn := by omega
  induction i with
  | zero =>
      have hk := keep_state (mn := mn) (x := x) hab hb34 hm hc0 hc hxa hxb hg hd hcap 0 (by omega)
      have e1 : SV c mn 0 = (OFF : ℤ) + (Scn : ℤ) := rfl
      have e2 : SD c mn 0 = (OFF : ℤ) := rfl
      have e3 : ((SV c mn 0).toNat, (SD c mn 0).toNat) = (OFF + Scn, OFF) := by
        rw [e1, e2, Prod.mk.injEq]
        exact ⟨by omega, by omega⟩
      rw [e3]
      rw [e3] at hk
      exact mem_push_self hk
  | succ i ih =>
      have hile : i ≤ Dep := by omega
      have hmem := ih hile
      have hk := keep_state (mn := mn) (x := x) hab hb34 hm hc0 hc hxa hxb hg hd hcap (i + 1) hi
      -- the coefficient is −1, 0 or 1
      have hci : |c (i + 1)| ≤ 1 := by
        have := hc (i + 1)
        exact_mod_cast this
      have hcases : c (i + 1) = -1 ∨ c (i + 1) = 0 ∨ c (i + 1) = 1 := by
        rcases abs_le.mp hci with ⟨h1, h2⟩
        omega
      -- bounds keeping the natural subtractions exact
      have hVlow := abs_le.mp (SV_bound hab hb34 hm hc0 hc hxa hxb hg i hile)
      have hDlow := SD_bound hab hb34 hm hc hxa hxb hd i hile
      obtain ⟨hA, hB⟩ := hcap i hile
      have hAZ : (TAn an bn i : ℤ) ≤ (TCAP : ℤ) := by exact_mod_cast hA
      have hBZ : (TBn an bn i : ℤ) ≤ (TCAP : ℤ) := by exact_mod_cast hB
      have hXG : XGS mn (i + 1) ≤ Scn := XGS_le_Scn hmb (i + 1)
      have hXGZ : (XGS mn (i + 1) : ℤ) ≤ (Scn : ℤ) := by exact_mod_cast hXG
      have hXP : XPS mn (i + 1) ≤ (i + 1) * Scn := by
        have h1 : XGS mn i ≤ Scn := XGS_le_Scn hmb i
        have : XPS mn (i + 1) = (i + 1) * XGS mn i := rfl
        rw [this]
        exact Nat.mul_le_mul_left _ h1
      have hXPZ : (XPS mn (i + 1) : ℤ) ≤ ((i : ℤ) + 1) * (Scn : ℤ) := by
        have : ((XPS mn (i + 1) : ℕ) : ℤ) ≤ (((i + 1) * Scn : ℕ) : ℤ) := by exact_mod_cast hXP
        push_cast at this
        linarith
      have hi48 : (i : ℤ) ≤ 48 := by
        have : i ≤ 48 := hile
        exact_mod_cast this
      have hOFF : OFF = 10000000000000000000000000 := OFF_val
      have hTC : TCAP = 100000000000000000000000 := TCAP_val
      have hSc : Scn = 1000000000000000000 := Scn_val
      have eSV : SV c mn (i + 1) = SV c mn i + c (i + 1) * (XGS mn (i + 1) : ℤ) := rfl
      have eSD : SD c mn (i + 1) = SD c mn i + c (i + 1) * (XPS mn (i + 1) : ℤ) := rfl
      have hlayer : layer an bn mn (i + 1)
          = expand (XGS mn (i + 1)) (XPS mn (i + 1))
              (OFF - TAn an bn (i + 1)) (OFF + TAn an bn (i + 1)) (OFF - TBn an bn (i + 1))
              (layer an bn mn i) := rfl
      rw [hlayer]
      refine mem_expand hmem ?_ hk
      rcases hcases with h | h | h
      · left
        rw [Prod.ext_iff]
        constructor <;> simp only [eSV, eSD, h] <;> omega
      · right; left
        rw [Prod.ext_iff]
        constructor <;> simp only [eSV, eSD, h] <;> omega
      · right; right
        rw [Prod.ext_iff]
        constructor <;> simp only [eSV, eSD, h] <;> omega

/-- **Soundness of the certificate for one cell.**  If the branch-and-bound
search empties for the cell `[an/Qn, bn/Qn]`, then every series with
coefficients in `{−1,0,1}` and constant term `1` is δ-transversal there. -/
theorem cell_sound (hab : an ≤ bn) (hb34 : 4 * bn ≤ 3 * Qn) (heven : (an + bn) % 2 = 0)
    (hcell : cellOK an bn = true)
    (hc0 : c 0 = 1) (hc : ∀ i, |(c i : ℝ)| ≤ 1)
    (hxa : (an : ℝ) / Qn ≤ x) (hxb : x ≤ (bn : ℝ) / Qn)
    (hg : |gval c x| ≤ 1 / 1000) : gder c x < -(1 / 1000) := by
  by_contra hcon
  push_neg at hcon
  have hd : -(1 / 1000 : ℝ) ≤ gder c x := hcon
  simp only [cellOK, Bool.and_eq_true] at hcell
  obtain ⟨hcap0, hempty⟩ := hcell
  have hcap := capOK_le hcap0
  set mn : ℕ := (an + bn) / 2 with hmn
  have hm : 2 * mn = an + bn := by omega
  have hmem := state_mem_layer (mn := mn) (x := x) hab hb34 hm hc0 hc hxa hxb hg hd
    (fun j hj => hcap j hj) Dep (le_refl _)
  rw [List.isEmpty_iff] at hempty
  rw [hempty] at hmem
  simp at hmem

end Search

end Transversality
end KnotGame
