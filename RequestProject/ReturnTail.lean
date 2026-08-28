import RequestProject.BranchingCount
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The return-time tail bound (round 7)

For `1 < lam < φ` and a window point `x ∈ (g, r)`, both branches are legal.  The
*good* child (T11c) returns to the window in a bounded number of steps; the
*discarded* child `dchild lam x` — the other branch — returns in a finite but
unbounded number of steps `retTime lam x`.  The note leaves open a bound on the
tail of `retTime`, measured there as `P(S > t) ≈ 1.3 · lam^{-t}` at `lam = 3/2`.

This file proves the deterministic (Lebesgue) form of that bound:

  `volume {x ∈ (g, r) | retTime lam x > t} ≤ 2 * g / lam ^ (t+1)`,

for every `lam ∈ (1, φ)`, with no hypothesis beyond `1 < lam` and
`lam² < lam + 1`.  Normalised by the length `r - g` of the window this reads

  `P(S > t) ≤ (2 * g / (lam * (r - g))) · lam^{-t}`,

which at `lam = 3/2` is `(4/3) · (2/3)^t` — the constant `4/3` matching the
measured `1.3`.

## The argument

A long return happens only very near an endpoint of the window.  If `x ≤ 1/2`
the discarded child is `lam*x - (lam-1) = lam*(x - g)`, whose distance from `0`
is `lam` times the distance from `x` to `g`; the forced orbit multiplies that
distance by `lam` at every step and, by the no-jumping lemma, enters the window
as soon as it passes `g`.  So a return time exceeding `t` forces
`x ≤ g + g/lam^(t+1)`.  The case `x > 1/2` is the mirror image, with `1 - lam*x
= lam*(r - x)`.

## Conventions (SCRUPLES)

* The *discarded* child at `x` is `f lam (other (cb lam x)) x`, the branch that
  the canonical selector `cb` of round 4 does **not** take; at `x = 1/2` (where
  `cb` chooses branch `0`) it is branch `1`.
* `retTime lam x` is the least `n` with `spine lam (dchild lam x) n` in the
  window — the number of *forced* steps after the branching, so `retTime = 0`
  means the discarded child is itself in the window.  It is finite for every
  window point (`retTime_spec`).
-/

namespace KnotGame
namespace ReturnTail

open KnotGame.Branching MeasureTheory

variable {lam : ℝ}

/-- The other branch. -/
def other (e : Fin 2) : Fin 2 := if e = 0 then 1 else 0

/-- The child of a window point that the canonical selector discards. -/
noncomputable def dchild (lam : ℝ) (x : ℝ) : ℝ := f lam (other (cb lam x)) x

/-- The number of forced steps the discarded child needs to re-enter the window. -/
noncomputable def retTime (lam : ℝ) (x : ℝ) : ℕ :=
  sInf {n : ℕ | spine lam (dchild lam x) n ∈ Window lam}

/-! ### Quick return from a point close to the window -/

/-- From below: if `lam^t * d` has passed `g`, the forced orbit of `d` has
entered the window by time `t`. -/
lemma quick_return_low (h1 : 1 < lam) (hphi : lam ^ 2 < lam + 1) {d : ℝ}
    (hdr : d < r lam) {t : ℕ} (hgt : g lam < lam ^ t * d) :
    ∃ n ≤ t, spine lam d n ∈ Window lam := by
  by_contra hcon
  push_neg at hcon
  have key : ∀ n ≤ t, spine lam d n = lam ^ n * d ∧ lam ^ n * d ≤ g lam := by
    intro n
    induction n with
    | zero =>
        intro _
        have hd : d ≤ g lam := by
          by_contra hd
          push_neg at hd
          exact hcon 0 (Nat.zero_le _) ⟨hd, hdr⟩
        simpa using hd
    | succ n ih =>
        intro hn
        obtain ⟨hsp, hle⟩ := ih (by omega)
        have hstep : spine lam d (n + 1) = lam ^ (n + 1) * d := by
          rw [spine_succ, hsp, cstep, cb_of_le_g h1 (lt_two_of_sq_lt h1 hphi) hle, f_zero]
          ring
        refine ⟨hstep, ?_⟩
        rcases le_or_gt (lam ^ (n + 1) * d) (g lam) with hle2 | hgt2
        · exact hle2
        · refine absurd ?_ (hcon (n + 1) hn)
          rw [hstep]
          refine ⟨hgt2, ?_⟩
          calc lam ^ (n + 1) * d = lam * (lam ^ n * d) := by ring
            _ < r lam := no_jump_low h1 hphi hle
  exact absurd (key t le_rfl).2 (not_le.mpr hgt)

/-- From above: if `lam^t * (1 - d)` has passed `g`, the forced orbit of `d` has
entered the window by time `t`. -/
lemma quick_return_high (h1 : 1 < lam) (hphi : lam ^ 2 < lam + 1) {d : ℝ}
    (hdg : g lam < d) {t : ℕ} (hgt : g lam < lam ^ t * (1 - d)) :
    ∃ n ≤ t, spine lam d n ∈ Window lam := by
  by_contra hcon
  push_neg at hcon
  have key : ∀ n ≤ t, spine lam d n = 1 - lam ^ n * (1 - d) ∧ r lam ≤ 1 - lam ^ n * (1 - d) := by
    intro n
    induction n with
    | zero =>
        intro _
        have hd : r lam ≤ d := by
          by_contra hd
          push_neg at hd
          exact hcon 0 (Nat.zero_le _) ⟨hdg, hd⟩
        simpa using hd
    | succ n ih =>
        intro hn
        obtain ⟨hsp, hle⟩ := ih (by omega)
        have hstep : spine lam d (n + 1) = 1 - lam ^ (n + 1) * (1 - d) := by
          rw [spine_succ, hsp, cstep, cb_of_r_le h1 (lt_two_of_sq_lt h1 hphi) hle, f_one]
          ring
        refine ⟨hstep, ?_⟩
        have hid : lam * (1 - lam ^ n * (1 - d)) - (lam - 1) = 1 - lam ^ (n + 1) * (1 - d) := by
          ring
        rcases le_or_gt (r lam) (1 - lam ^ (n + 1) * (1 - d)) with hge | hlt
        · exact hge
        · refine absurd ?_ (hcon (n + 1) hn)
          rw [hstep]
          exact ⟨by rw [← hid]; exact no_jump_high h1 hphi hle, hlt⟩
  have := (key t le_rfl).2
  have hr : r lam + g lam = 1 := by rw [add_comm]; exact g_add_r lam
  linarith

/-! ### Finiteness of the return time -/

lemma dchild_mem_Ioo (h1 : 1 < lam) (hphi : lam ^ 2 < lam + 1) {x : ℝ}
    (hx : x ∈ Window lam) : dchild lam x ∈ Set.Ioo (0:ℝ) 1 := by
  have h2 : lam < 2 := lt_two_of_sq_lt h1 hphi
  have hleg : BLegal lam (other (cb lam x)) x := BLegal_of_mem_Window hx _
  exact f_mem_Ioo h1 (Window_subset_Ioo h1 hx) hleg

lemma exists_return (h1 : 1 < lam) (hphi : lam ^ 2 < lam + 1) {x : ℝ}
    (hx : x ∈ Window lam) : ∃ n, spine lam (dchild lam x) n ∈ Window lam := by
  set d := dchild lam x with hd
  obtain ⟨hd0, hd1⟩ := dchild_mem_Ioo h1 hphi hx
  by_cases hdg : d ≤ g lam
  · obtain ⟨t, ht⟩ := pow_unbounded_of_one_lt (g lam / d) h1
    have hgt : g lam < lam ^ t * d := by
      rw [div_lt_iff₀ hd0] at ht
      linarith [ht]
    obtain ⟨n, -, hn⟩ := quick_return_low h1 hphi (lt_of_le_of_lt hdg (g_lt_r h1 (lt_two_of_sq_lt h1 hphi))) hgt
    exact ⟨n, hn⟩
  · push_neg at hdg
    obtain ⟨t, ht⟩ := pow_unbounded_of_one_lt (g lam / (1 - d)) h1
    have hpos : 0 < 1 - d := by linarith
    have hgt : g lam < lam ^ t * (1 - d) := by
      rw [div_lt_iff₀ hpos] at ht
      linarith [ht]
    obtain ⟨n, -, hn⟩ := quick_return_high h1 hphi hdg hgt
    exact ⟨n, hn⟩

lemma retTime_spec (h1 : 1 < lam) (hphi : lam ^ 2 < lam + 1) {x : ℝ} (hx : x ∈ Window lam) :
    spine lam (dchild lam x) (retTime lam x) ∈ Window lam :=
  Nat.sInf_mem (exists_return h1 hphi hx)

lemma lt_retTime_iff (h1 : 1 < lam) (hphi : lam ^ 2 < lam + 1) {x : ℝ} (hx : x ∈ Window lam)
    (t : ℕ) : t < retTime lam x ↔ ∀ n ≤ t, spine lam (dchild lam x) n ∉ Window lam := by
  constructor
  · intro h n hn hmem
    have hle : retTime lam x ≤ n := Nat.sInf_le hmem
    omega
  · intro h
    by_contra hle
    push_neg at hle
    exact h _ hle (retTime_spec h1 hphi hx)

/-! ### The tail bound -/

/-- **The return-time tail bound.**  Only a set of measure at most
`2 * g / lam ^ (t+1)` of window points has a discarded child needing more than
`t` forced steps to return. -/
theorem return_time_tail (h1 : 1 < lam) (hphi : lam ^ 2 < lam + 1) (t : ℕ) :
    volume {x | x ∈ Window lam ∧ t < retTime lam x} ≤
      ENNReal.ofReal (2 * g lam / lam ^ (t + 1)) := by
  have hlam : (0:ℝ) < lam := lt_trans zero_lt_one h1
  have h2 : lam < 2 := lt_two_of_sq_lt h1 hphi
  have hgpos : 0 < g lam := g_pos lam h1
  have hpow : 0 < lam ^ (t + 1) := pow_pos hlam _
  set u : ℝ := g lam / lam ^ (t + 1) with hu
  have hupos : 0 < u := div_pos hgpos hpow
  have hsub : {x | x ∈ Window lam ∧ t < retTime lam x} ⊆
      Set.Ioc (g lam) (g lam + u) ∪ Set.Ico (r lam - u) (r lam) := by
    rintro x ⟨hx, hbad⟩
    rw [lt_retTime_iff h1 hphi hx] at hbad
    rcases le_or_gt x ((g lam + r lam) / 2) with hhalf | hhalf
    · refine Or.inl ⟨hx.1, ?_⟩
      by_contra hxx
      push_neg at hxx
      have hcb : cb lam x = 0 := cb_eq_zero hhalf
      have hd : dchild lam x = lam * x - (lam - 1) := by
        rw [dchild, hcb]
        simp [other]
      have hdg : lam * x - (lam - 1) = lam * (x - g lam) := by
        rw [mul_sub, lam_mul_g h1]
      have hdlt : dchild lam x < r lam := by
        rw [hd]
        have hr : r lam * lam = 1 := r_mul_self h1
        nlinarith [hhalf, g_add_r lam, sq_nonneg (lam - 1)]
      have hgt : g lam < lam ^ t * dchild lam x := by
        rw [hd, hdg]
        have hstep : u < x - g lam := by linarith
        have : lam ^ t * (lam * u) ≤ lam ^ t * (lam * (x - g lam)) := by
          have := mul_le_mul_of_nonneg_left (le_of_lt hstep) (le_of_lt hlam)
          exact mul_le_mul_of_nonneg_left this (le_of_lt (pow_pos hlam t))
        have hcalc : lam ^ t * (lam * u) = g lam := by
          rw [hu]
          field_simp
          ring
        nlinarith [this, hcalc]
      obtain ⟨n, hn, hmem⟩ := quick_return_low h1 hphi hdlt hgt
      exact hbad n hn hmem
    · refine Or.inr ⟨?_, hx.2⟩
      by_contra hxx
      push_neg at hxx
      have hcb : cb lam x = 1 := cb_eq_one hhalf
      have hd : dchild lam x = lam * x := by
        rw [dchild, hcb]
        simp [other]
      have hdg : g lam < dchild lam x := by
        rw [hd, g_eq, r]
        have : (g lam + r lam) / 2 = 1 / 2 := mid_eq_half lam
        rw [this] at hhalf
        rw [show (1:ℝ) - lam⁻¹ = 1 - lam⁻¹ from rfl]
        have hinv : lam⁻¹ * lam = 1 := inv_mul_cancel₀ (ne_of_gt hlam)
        nlinarith [hhalf, sq_nonneg (lam - 1)]
      have hone : (1:ℝ) - dchild lam x = lam * (r lam - x) := by
        rw [hd, mul_sub, lam_mul_r h1]
      have hgt : g lam < lam ^ t * (1 - dchild lam x) := by
        rw [hone]
        have hstep : u < r lam - x := by linarith
        have : lam ^ t * (lam * u) ≤ lam ^ t * (lam * (r lam - x)) := by
          have := mul_le_mul_of_nonneg_left (le_of_lt hstep) (le_of_lt hlam)
          exact mul_le_mul_of_nonneg_left this (le_of_lt (pow_pos hlam t))
        have hcalc : lam ^ t * (lam * u) = g lam := by
          rw [hu]
          field_simp
          ring
        nlinarith [this, hcalc]
      obtain ⟨n, hn, hmem⟩ := quick_return_high h1 hphi hdg hgt
      exact hbad n hn hmem
  calc volume {x | x ∈ Window lam ∧ t < retTime lam x}
      ≤ volume (Set.Ioc (g lam) (g lam + u) ∪ Set.Ico (r lam - u) (r lam)) := measure_mono hsub
    _ ≤ volume (Set.Ioc (g lam) (g lam + u)) + volume (Set.Ico (r lam - u) (r lam)) :=
        measure_union_le _ _
    _ = ENNReal.ofReal u + ENNReal.ofReal u := by
        rw [Real.volume_Ioc, Real.volume_Ico]
        congr 1 <;> ring_nf
    _ = ENNReal.ofReal (2 * g lam / lam ^ (t + 1)) := by
        rw [← ENNReal.ofReal_add (le_of_lt hupos) (le_of_lt hupos)]
        congr 1
        rw [hu]
        ring

/-- The tail bound at `lam = 3/2`: `volume {S > t} ≤ (2/3)^(t+2)`, i.e.
`P(S > t) ≤ (4/3) · (2/3)^t` after dividing by the window length `1/3`. -/
theorem return_time_tail_three_halves (t : ℕ) :
    volume {x | x ∈ Window (3/2 : ℝ) ∧ t < retTime (3/2 : ℝ) x} ≤
      ENNReal.ofReal ((2/3 : ℝ) ^ (t + 2)) := by
  have h := return_time_tail (lam := (3/2 : ℝ)) (by norm_num) (by norm_num) t
  have hg : g (3/2 : ℝ) = 1/3 := by norm_num [g, r]
  have hval : 2 * g (3/2 : ℝ) / (3/2 : ℝ) ^ (t + 1) = (2/3 : ℝ) ^ (t + 2) := by
    rw [hg]
    rw [show (t + 2) = (t + 1) + 1 from rfl, pow_succ, show ((3:ℝ)/2) = ((2:ℝ)/3)⁻¹ by norm_num,
      inv_pow]
    field_simp
    ring
  rwa [hval] at h

/-- The same bound in the normalised ("probability") form of the note: at
`lam = 3/2`, the proportion of window points whose discarded child takes more
than `t` forced steps to return is at most `(4/3) * (2/3)^t`. -/
theorem return_time_tail_prob_three_halves (t : ℕ) :
    volume {x | x ∈ Window (3/2 : ℝ) ∧ t < retTime (3/2 : ℝ) x} ≤
      ENNReal.ofReal ((4/3 : ℝ) * (2/3 : ℝ) ^ t) * volume (Window (3/2 : ℝ)) := by
  have h := return_time_tail_three_halves t
  have hwin : volume (Window (3/2 : ℝ)) = ENNReal.ofReal (1/3 : ℝ) := by
    rw [Window, Real.volume_Ioo]
    norm_num [g, r]
  rw [hwin, ← ENNReal.ofReal_mul (by positivity)]
  refine h.trans (le_of_eq ?_)
  congr 1
  rw [pow_add]
  ring

end ReturnTail
end KnotGame
