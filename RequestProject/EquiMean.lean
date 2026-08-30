import RequestProject.Contraction
import RequestProject.BranchBridge

/-!
# T41 — equidistribution in mean (paper `thm:equimean`)

The adjoint of the counting operator `T` of `RequestProject.CountingOperator`
with respect to Lebesgue measure on `(0,1)` is the composition operator

  `(S h)(x) = h(λx)·[x < r] + h(λx − (λ−1))·[x > g]`,   `r = 1/λ`, `g = 1 − r`,

which is exactly the propagator of the endpoint counts of the **branch**
alphabet.  Proved here:

* `adjoint` — `∫₀¹ (S h) g dx = ∫₀¹ h (T g) dx`;
* `endpoint_propagator` — `(S^[m] h)(x) = ∑_{ε} h(Φ_ε(x))`, the sum being over
  the branch words `ε` of length `m` legal from `x`; i.e. `∫ h dμˣ_m = (S^m h)(x)`
  for the endpoint measure `μˣ_m` of those words;
* `equidistribution_in_mean` — `(λ/2)^m ∫₀¹ (S^m h) g dx → (∫₀¹ h dx)·c`, where
  `c` is the limit constant of `RequestProject.Contraction.tendsto_const` for the
  Lipschitz function `g`.

## Conventions (SCRUPLES)

* **The alphabet is the two-letter branch alphabet**, as the commission
  requires, through the bridge of `RequestProject.BranchBridge`:
  `branchWords`/`branchSurvivesWord` on the operator side, `rapp` for the action
  of a word.  The three-letter move alphabet carries the constant `3/λ` instead
  (round 13's correction to T38) and is not used here.
* **The endpoint measure `μˣ_m` is not constructed as a `Measure`.**  It is the
  sum of the Dirac masses at the endpoints `Φ_ε(x)`, counted with multiplicity,
  and `∫ h dμˣ_m` is therefore literally the finite sum
  `∑_{ε ∈ branchWords λ x m} h (rapp λ x ε)`; that finite sum is what
  `endpoint_propagator` computes.  No measure-theoretic content is lost: the
  statement is an identity between a finite sum and an iterate.
* **The limit constant is not identified with `∫ g dν_r`.**  As in T40 (and as
  round 13 did for the trapezoid) the Bernoulli convolution is not constructed
  in this project, so `equidistribution_in_mean` names the constant `c` supplied
  by `Contraction.tendsto_const`.  Under the invariance hypothesis of
  `Contraction.const_eq_integral_of_invariant` that constant *is* `∫ g dν`, which
  is the paper's statement; the identification is hypothetical, not proved.
* **Regularity hypotheses.**  `h` and `g` are assumed bounded and measurable
  (`BddMeas`); the paper says "continuous on `[0,1]`", and a continuous function
  on `[0,1]` extended boundedly to `ℝ` satisfies this.  Boundedness is genuinely
  used: `S h` is discontinuous (it has the two indicators), so continuity cannot
  be propagated along the induction, while boundedness and measurability can.
  For the limit statement `g` is in addition Lipschitz, which is what T40 needs.
-/

namespace KnotGame
namespace EquiMean

open MeasureTheory Set Filter Topology
open KnotGame.CountingOperator KnotGame.ExpCount

variable {lam : ℝ}

/-! ### Bounded measurable functions -/

/-- The regularity carried along the induction: bounded and measurable. -/
def BddMeas (C : ℝ) (h : ℝ → ℝ) : Prop := Measurable h ∧ ∀ x, |h x| ≤ C

lemma BddMeas.measurable {C : ℝ} {h : ℝ → ℝ} (hh : BddMeas C h) : Measurable h := hh.1

lemma BddMeas.bound {C : ℝ} {h : ℝ → ℝ} (hh : BddMeas C h) (x : ℝ) : |h x| ≤ C := hh.2 x

lemma BddMeas.nonneg {C : ℝ} {h : ℝ → ℝ} (hh : BddMeas C h) : 0 ≤ C :=
  le_trans (abs_nonneg _) (hh.2 0)

lemma BddMeas.integrableOn {C : ℝ} {h : ℝ → ℝ} (hh : BddMeas C h) {s : Set ℝ}
    (hs : volume s ≠ ⊤) : IntegrableOn h s := by
  refine Measure.integrableOn_of_bounded hs hh.measurable.aestronglyMeasurable (M := C) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs]
  exact hh.bound x

lemma BddMeas.mul {C D : ℝ} {h k : ℝ → ℝ} (hh : BddMeas C h) (hk : BddMeas D k) :
    BddMeas (C * D) (fun x => h x * k x) := by
  refine ⟨hh.measurable.mul hk.measurable, fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hh.bound x) (hk.bound x) (abs_nonneg _) hh.nonneg

/-! ### The composition operator -/

/-- The composition operator `(S h)(x) = h(λx)·[x < r] + h(λx − (λ−1))·[x > g]`,
the adjoint of `T` and the propagator of the endpoint counts. -/
noncomputable def S (lam : ℝ) (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  (if x < r lam then h (lam * x) else 0) + (if g lam < x then h (lam * x - (lam - 1)) else 0)

/-- `S` in the vocabulary of the branch maps: one term per legal branch. -/
lemma S_eq_branch (lam : ℝ) (h : ℝ → ℝ) (x : ℝ) :
    S lam h x =
      (if branchLegal lam 0 x then h (f lam 0 x) else 0)
      + (if branchLegal lam 1 x then h (f lam 1 x) else 0) := by
  classical
  simp [S]

lemma S_eq_fun (lam : ℝ) (h : ℝ → ℝ) : S lam h =
    fun x => (if x < r lam then h (lam * x) else 0)
      + (if g lam < x then h (lam * x - (lam - 1)) else 0) := rfl

lemma measurable_S {h : ℝ → ℝ} (hh : Measurable h) : Measurable (S lam h) := by
  classical
  have h1 : Measurable fun x : ℝ => h (lam * x) := hh.comp (by fun_prop)
  have h2 : Measurable fun x : ℝ => h (lam * x - (lam - 1)) := hh.comp (by fun_prop)
  rw [S_eq_fun]
  exact (Measurable.ite measurableSet_Iio h1 measurable_const).add
    (Measurable.ite measurableSet_Ioi h2 measurable_const)

lemma bddMeas_S {C : ℝ} {h : ℝ → ℝ} (hh : BddMeas C h) : BddMeas (2 * C) (S lam h) := by
  classical
  refine ⟨measurable_S hh.measurable, fun x => ?_⟩
  have b1 : |(if x < r lam then h (lam * x) else 0)| ≤ C := by
    split_ifs
    · exact hh.bound _
    · simpa using hh.nonneg
  have b2 : |(if g lam < x then h (lam * x - (lam - 1)) else 0)| ≤ C := by
    split_ifs
    · exact hh.bound _
    · simpa using hh.nonneg
  calc |S lam h x| ≤ |(if x < r lam then h (lam * x) else 0)|
        + |(if g lam < x then h (lam * x - (lam - 1)) else 0)| := abs_add_le _ _
    _ ≤ C + C := add_le_add b1 b2
    _ = 2 * C := by ring

lemma T_eq_fun (lam : ℝ) (h : ℝ → ℝ) : CountingOperator.T lam h =
    fun y => (1 / lam) * (h (y / lam) + h ((y + lam - 1) / lam)) := rfl

lemma bddMeas_T (hlam : 1 < lam) {C : ℝ} {h : ℝ → ℝ} (hh : BddMeas C h) :
    BddMeas ((2 / lam) * C) (CountingOperator.T lam h) := by
  have hlam0 : (0:ℝ) < lam := lt_trans zero_lt_one hlam
  refine ⟨?_, fun y => ?_⟩
  · have h1 : Measurable fun y : ℝ => h (y / lam) := hh.measurable.comp (by fun_prop)
    have h2 : Measurable fun y : ℝ => h ((y + lam - 1) / lam) := hh.measurable.comp (by fun_prop)
    rw [T_eq_fun]
    exact measurable_const.mul (h1.add h2)
  · have := abs_add_le (h (y / lam)) (h ((y + lam - 1) / lam))
    have hb1 := hh.bound (y / lam)
    have hb2 := hh.bound ((y + lam - 1) / lam)
    have hpos : |1 / lam| = 1 / lam := abs_of_pos (by positivity)
    rw [CountingOperator.T, abs_mul, hpos]
    have hle : |h (y / lam) + h ((y + lam - 1) / lam)| ≤ 2 * C := by linarith
    calc 1 / lam * |h (y / lam) + h ((y + lam - 1) / lam)| ≤ 1 / lam * (2 * C) := by
          exact mul_le_mul_of_nonneg_left hle (by positivity)
      _ = (2 / lam) * C := by field_simp

lemma bddMeas_iterate_T (hlam : 1 < lam) {C : ℝ} {h : ℝ → ℝ} (hh : BddMeas C h) :
    ∀ m : ℕ, BddMeas ((2 / lam) ^ m * C) ((CountingOperator.T lam)^[m] h)
  | 0 => by simpa using hh
  | (m + 1) => by
      have := bddMeas_T hlam (bddMeas_iterate_T hlam hh m)
      rw [Function.iterate_succ_apply']
      have he : (2 / lam) * ((2 / lam) ^ m * C) = (2 / lam) ^ (m + 1) * C := by ring
      rwa [he] at this

/-! ### (a) The adjoint relation -/

/-- **T41(a).**  `S` is the adjoint of `T` for Lebesgue measure on `(0,1)`. -/
theorem adjoint (hlam : 1 < lam) {Ch Cg : ℝ} {h k : ℝ → ℝ}
    (hh : BddMeas Ch h) (hk : BddMeas Cg k) :
    ∫ x in Ioo (0:ℝ) 1, S lam h x * k x
      = ∫ y in Ioo (0:ℝ) 1, h y * CountingOperator.T lam k y := by
  classical
  have hlam0 : (0:ℝ) < lam := lt_trans zero_lt_one hlam
  have hr0 : 0 < r lam := r_pos lam hlam
  have hr1 : r lam < 1 := r_lt_one lam hlam
  have hg0 : 0 < g lam := g_pos lam hlam
  have hg1 : g lam < 1 := g_lt_one lam hlam
  have hmul : lam * r lam = 1 := by rw [r]; field_simp
  have hmulg : lam * g lam + (1 - lam) = 0 := by rw [g, r]; field_simp; ring
  have hfin : volume (Ioo (0:ℝ) 1) ≠ ⊤ := by simp
  -- the two pieces, as functions on `(0,1)`
  set H₁ : ℝ → ℝ := fun y => h y * k (y / lam) with hH₁
  set H₂ : ℝ → ℝ := fun y => h y * k ((y + lam - 1) / lam) with hH₂
  have hH₁b : BddMeas (Ch * Cg) H₁ :=
    hh.mul ⟨hk.measurable.comp (by fun_prop), fun y => hk.bound _⟩
  have hH₂b : BddMeas (Ch * Cg) H₂ :=
    hh.mul ⟨hk.measurable.comp (by fun_prop), fun y => hk.bound _⟩
  -- pointwise decomposition of the left integrand
  have hpt : ∀ x : ℝ, S lam h x * k x
      = (Iio (r lam)).indicator (fun x => H₁ (lam * x)) x
        + (Ioi (g lam)).indicator (fun x => H₂ (lam * x + (1 - lam))) x := by
    intro x
    have e1 : H₁ (lam * x) = h (lam * x) * k x := by
      rw [hH₁]
      field_simp
    have e2 : H₂ (lam * x + (1 - lam)) = h (lam * x - (lam - 1)) * k x := by
      have ex : (lam * x + (1 - lam) + lam - 1) / lam = x := by field_simp; ring
      have ey : lam * x + (1 - lam) = lam * x - (lam - 1) := by ring
      show h (lam * x + (1 - lam)) * k ((lam * x + (1 - lam) + lam - 1) / lam)
        = h (lam * x - (lam - 1)) * k x
      rw [ex, ey]
    rw [S, Set.indicator_apply, Set.indicator_apply]
    simp only [mem_Iio, mem_Ioi, e1, e2]
    split_ifs <;> ring
  rw [setIntegral_congr_fun measurableSet_Ioo (fun x _ => hpt x)]
  have hi1 : IntegrableOn (fun x : ℝ => H₁ (lam * x)) (Ioo (0:ℝ) 1) := by
    refine Measure.integrableOn_of_bounded hfin
      ((hH₁b.measurable.comp (by fun_prop)).aestronglyMeasurable) (M := Ch * Cg) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs]
    exact hH₁b.bound _
  have hi2 : IntegrableOn (fun x : ℝ => H₂ (lam * x + (1 - lam))) (Ioo (0:ℝ) 1) := by
    refine Measure.integrableOn_of_bounded hfin
      ((hH₂b.measurable.comp (by fun_prop)).aestronglyMeasurable) (M := Ch * Cg) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs]
    exact hH₂b.bound _
  rw [integral_add (hi1.indicator measurableSet_Iio) (hi2.indicator measurableSet_Ioi)]
  rw [integral_indicator_Iio _ hr1.le, integral_indicator_Ioi _ hg0.le]
  rw [integral_Ioo_comp_mul hlam 0 (r lam) 0 1 hr0.le (by ring) hmul H₁,
    integral_Ioo_comp_affine hlam (1 - lam) (g lam) 1 0 1 hg1.le hmulg (by ring) H₂]
  have hsum : ∫ y in Ioo (0:ℝ) 1, h y * CountingOperator.T lam k y
      = (1 / lam) * ((∫ y in Ioo (0:ℝ) 1, H₁ y) + ∫ y in Ioo (0:ℝ) 1, H₂ y) := by
    have hpt2 : ∀ y : ℝ, h y * CountingOperator.T lam k y = (1 / lam) * (H₁ y + H₂ y) := by
      intro y
      rw [CountingOperator.T, hH₁, hH₂]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioo (fun y _ => hpt2 y),
      integral_const_mul, integral_add (hH₁b.integrableOn hfin) (hH₂b.integrableOn hfin)]
  rw [hsum]
  ring

/-! ### (b) The endpoint propagator -/

/-- **T41(b).**  `∫ h dμˣ_m = (S^m h)(x)`: the `m`-th iterate of `S` at `x` is
the sum of `h` over the endpoints of the branch words of length `m` legal from
`x`, counted with multiplicity. -/
theorem endpoint_propagator (lam : ℝ) (h : ℝ → ℝ) :
    ∀ (m : ℕ) (x : ℝ), (S lam)^[m] h x = ∑ w ∈ branchWords lam x m, h (rapp lam x w)
  | 0, x => by
      classical
      have hb : branchWords lam x 0 = {[]} := by
        ext w
        simp only [mem_branchWords, Finset.mem_singleton, List.length_eq_zero_iff]
        exact ⟨fun hw => hw.1, fun hw => ⟨hw, by rw [hw]; trivial⟩⟩
      simp [hb]
  | (m + 1), x => by
      classical
      have hdisj : (((Finset.univ.filter (fun i : Fin 2 => branchLegal lam i x)) :
          Finset (Fin 2)) : Set (Fin 2)).PairwiseDisjoint
            (fun i => (branchWords lam (f lam i x) m).image (List.cons i)) := by
        intro a _ b _ hab
        simp only [Function.onFun, Finset.disjoint_left, Finset.mem_image]
        rintro w ⟨u, -, rfl⟩ ⟨v, -, hv⟩
        obtain ⟨h1, -⟩ := List.cons_eq_cons.mp hv
        exact hab h1.symm
      rw [Function.iterate_succ_apply', S_eq_branch, branchWords_succ,
        Finset.sum_biUnion hdisj]
      have hterm : ∀ i : Fin 2,
          ∑ w ∈ (branchWords lam (f lam i x) m).image (List.cons i), h (rapp lam x w)
            = (S lam)^[m] h (f lam i x) := by
        intro i
        rw [Finset.sum_image (fun u _ v _ huv => (List.cons_eq_cons.mp huv).2)]
        rw [endpoint_propagator lam h m (f lam i x)]
        exact Finset.sum_congr rfl (fun w _ => by rw [rapp_cons])
      rw [Finset.sum_filter, Fin.sum_univ_two, hterm 0, hterm 1]

/-! ### (c) Equidistribution in mean -/

/-- The normalised iterates: `P^[m] = (λ/2)^m · T^[m]`. -/
lemma iterate_P_eq (hlam : 1 < lam) (k : ℝ → ℝ) :
    ∀ (m : ℕ) (y : ℝ),
      (Contraction.P lam)^[m] k y = (lam / 2) ^ m * ((CountingOperator.T lam)^[m] k y)
  | 0, y => by simp
  | (m + 1), y => by
      have hstep : ∀ z : ℝ, (Contraction.P lam)^[m + 1] k z
          = Contraction.P lam ((Contraction.P lam)^[m] k) z := by
        intro z; rw [Function.iterate_succ_apply']
      rw [hstep, Contraction.P_eq_smul_T hlam, Function.iterate_succ_apply']
      have hfun : (Contraction.P lam)^[m] k
          = fun z => (lam / 2) ^ m * ((CountingOperator.T lam)^[m] k z) := by
        funext z; exact iterate_P_eq hlam k m z
      rw [hfun]
      rw [CountingOperator.T, CountingOperator.T]
      ring

/-- **T41(c), equidistribution in mean.**  With `c` the constant to which the
normalised iterates `P^[m] g` converge uniformly on `[0,1]` (T40), the
normalised endpoint averages converge:
`(λ/2)^m ∫₀¹ (S^m h) g dx → (∫₀¹ h dx)·c`.  Under the identification of `c` with
`∫ g dν_r` — hypothetical in this project, see
`Contraction.const_eq_integral_of_invariant` — this is the paper's
`thm:equimean`. -/
theorem equidistribution_in_mean (hlam : 1 < lam) {Ch Cg K c : ℝ} {h k : ℝ → ℝ}
    (hh : BddMeas Ch h) (hk : BddMeas Cg k) (hlip : Contraction.LipBound K k)
    (hc : ∀ (m : ℕ), ∀ y ∈ Icc (0:ℝ) 1,
      |(Contraction.P lam)^[m] k y - c| ≤ (2 * K / (1 - r lam)) * (r lam) ^ m) :
    Tendsto (fun m : ℕ => (lam / 2) ^ m * ∫ x in Ioo (0:ℝ) 1, (S lam)^[m] h x * k x)
      atTop (𝓝 ((∫ x in Ioo (0:ℝ) 1, h x) * c)) := by
  have hlam0 : (0:ℝ) < lam := lt_trans zero_lt_one hlam
  have hfin : volume (Ioo (0:ℝ) 1) ≠ ⊤ := by simp
  have hr0 := Contraction.r_pos hlam
  have hr1 := Contraction.r_lt_one hlam
  have hKn : 0 ≤ K := hlip.nonneg
  have hden : 0 < 1 - r lam := by linarith
  -- move the iterates across the adjoint relation
  have hadj : ∀ (m : ℕ) {Ch' : ℝ} {h' : ℝ → ℝ}, BddMeas Ch' h' →
      ∫ x in Ioo (0:ℝ) 1, (S lam)^[m] h' x * k x
        = ∫ y in Ioo (0:ℝ) 1, h' y * ((CountingOperator.T lam)^[m] k) y := by
    intro m
    induction m with
    | zero => intro Ch' h' _; simp
    | succ m ih =>
        intro Ch' h' hh'
        have hSh : BddMeas (2 * Ch') (S lam h') := bddMeas_S hh'
        have h1 : ∫ x in Ioo (0:ℝ) 1, (S lam)^[m + 1] h' x * k x
            = ∫ x in Ioo (0:ℝ) 1, (S lam)^[m] (S lam h') x * k x := by
          simp only [Function.iterate_succ_apply]
        rw [h1, ih hSh]
        have hTk := bddMeas_iterate_T hlam hk m
        rw [Function.iterate_succ_apply']
        exact adjoint hlam hh' hTk
  -- the normalised integrand is `h` against `P^[m] k`
  have hnorm : ∀ m : ℕ,
      (lam / 2) ^ m * ∫ x in Ioo (0:ℝ) 1, (S lam)^[m] h x * k x
        = ∫ y in Ioo (0:ℝ) 1, h y * ((Contraction.P lam)^[m] k) y := by
    intro m
    rw [hadj m hh]
    have hpt : ∀ y : ℝ, h y * ((Contraction.P lam)^[m] k) y
        = (lam / 2) ^ m * (h y * ((CountingOperator.T lam)^[m] k) y) := by
      intro y
      rw [iterate_P_eq hlam k m y]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioo (fun y _ => hpt y), integral_const_mul]
  -- the error estimate
  have hkey : ∀ m : ℕ,
      |(∫ y in Ioo (0:ℝ) 1, h y * ((Contraction.P lam)^[m] k) y)
          - (∫ x in Ioo (0:ℝ) 1, h x) * c| ≤ Ch * ((2 * K / (1 - r lam)) * (r lam) ^ m) := by
    intro m
    have hPk : BddMeas ((lam / 2) ^ m * ((2 / lam) ^ m * Cg)) ((Contraction.P lam)^[m] k) := by
      have hTk := bddMeas_iterate_T hlam hk m
      refine ⟨?_, fun y => ?_⟩
      · have : (Contraction.P lam)^[m] k
            = fun y => (lam / 2) ^ m * ((CountingOperator.T lam)^[m] k y) := by
          funext y; exact iterate_P_eq hlam k m y
        rw [this]
        exact measurable_const.mul hTk.measurable
      · rw [iterate_P_eq hlam k m y, abs_mul]
        have hpow : |(lam / 2) ^ m| = (lam / 2) ^ m := abs_of_nonneg (by positivity)
        rw [hpow]
        exact mul_le_mul_of_nonneg_left (hTk.bound y) (by positivity)
    have hprod : IntegrableOn (fun y => h y * ((Contraction.P lam)^[m] k) y) (Ioo (0:ℝ) 1) :=
      (hh.mul hPk).integrableOn hfin
    have hhc : IntegrableOn (fun y => h y * c) (Ioo (0:ℝ) 1) :=
      (hh.mul ⟨measurable_const, fun _ => le_of_eq rfl⟩).integrableOn hfin
    have hsplit : (∫ y in Ioo (0:ℝ) 1, h y * ((Contraction.P lam)^[m] k) y)
        - (∫ x in Ioo (0:ℝ) 1, h x) * c
        = ∫ y in Ioo (0:ℝ) 1, (h y * (((Contraction.P lam)^[m] k) y - c)) := by
      have e : ∀ y : ℝ, h y * (((Contraction.P lam)^[m] k) y - c)
          = h y * ((Contraction.P lam)^[m] k) y - h y * c := by intro y; ring
      rw [setIntegral_congr_fun measurableSet_Ioo (fun y _ => e y),
        integral_sub hprod hhc]
      have : ∫ y in Ioo (0:ℝ) 1, h y * c = (∫ x in Ioo (0:ℝ) 1, h x) * c := by
        rw [integral_mul_const]
      rw [this]
    rw [hsplit]
    have hbnd : ∀ y ∈ Ioo (0:ℝ) 1,
        |h y * (((Contraction.P lam)^[m] k) y - c)|
          ≤ Ch * ((2 * K / (1 - r lam)) * (r lam) ^ m) := by
      intro y hy
      rw [abs_mul]
      have h1 : |h y| ≤ Ch := hh.bound y
      have h2 : |((Contraction.P lam)^[m] k) y - c| ≤ (2 * K / (1 - r lam)) * (r lam) ^ m :=
        hc m y ⟨le_of_lt hy.1, le_of_lt hy.2⟩
      exact mul_le_mul h1 h2 (abs_nonneg _) hh.nonneg
    have hsub : IntegrableOn (fun y => h y * (((Contraction.P lam)^[m] k) y - c))
        (Ioo (0:ℝ) 1) := by
      have : IntegrableOn (fun y => h y * ((Contraction.P lam)^[m] k) y - h y * c)
          (Ioo (0:ℝ) 1) := hprod.sub hhc
      refine this.congr_fun (fun y _ => by ring) measurableSet_Ioo
    calc |∫ y in Ioo (0:ℝ) 1, (h y * (((Contraction.P lam)^[m] k) y - c))|
        ≤ ∫ y in Ioo (0:ℝ) 1, |h y * (((Contraction.P lam)^[m] k) y - c)| := by
          simpa [Real.norm_eq_abs] using
            (norm_integral_le_integral_norm (μ := volume.restrict (Ioo (0:ℝ) 1))
              (fun y => h y * (((Contraction.P lam)^[m] k) y - c)))
      _ ≤ ∫ _y in Ioo (0:ℝ) 1, Ch * ((2 * K / (1 - r lam)) * (r lam) ^ m) := by
          refine setIntegral_mono_on hsub.abs (integrableOn_const hfin) measurableSet_Ioo ?_
          exact hbnd
      _ = Ch * ((2 * K / (1 - r lam)) * (r lam) ^ m) := by
          rw [setIntegral_const]
          simp
  -- conclude by squeezing
  have hlim : Tendsto (fun m : ℕ => Ch * ((2 * K / (1 - r lam)) * (r lam) ^ m)) atTop (𝓝 0) := by
    have : Tendsto (fun m : ℕ => (r lam) ^ m) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt hr0) hr1
    simpa using (this.const_mul (2 * K / (1 - r lam))).const_mul Ch
  have hconv : Tendsto
      (fun m : ℕ => ∫ y in Ioo (0:ℝ) 1, h y * ((Contraction.P lam)^[m] k) y) atTop
      (𝓝 ((∫ x in Ioo (0:ℝ) 1, h x) * c)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun m => dist_nonneg) (fun m => ?_) hlim
    rw [Real.dist_eq]
    exact hkey m
  refine hconv.congr (fun m => ?_)
  exact (hnorm m).symm

end EquiMean
end KnotGame
