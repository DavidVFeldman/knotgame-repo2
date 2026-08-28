import RequestProject.Density

/-!
# T26 — the quantitative density criterion (paper Theorem `thm:density`)

Round 5 certified the topological form of the criterion
(`infinitelyManyKnots_of_kindDense`): if the endpoints of kind words are dense
in `(0,1)`, then `N_λ = ∞`.  This file certifies the quantitative form.

The hypothesis is the paper's **(D_λ)**: there is a constant `C` such that
every subinterval of `(0,1)` of length `ε` contains the endpoint of a kind
word of length at most `C log(1/ε)` (`KindDenseQuant`).  It is stronger than
`KindDense`, to which it reduces by forgetting the length bound
(`kindDense_of_quant`), and — like it — is certified for no specific `λ`.

The conclusion adds an explicit bound on the depth `d_λ(k)` at which `k`
simultaneous knots first appear:

  `d_λ(k) ≤ B ^ k − 1`,  where `B = max 2 (1 + C (log λ + 1))`
  (`d_le_pow`),

so `d_λ` grows at most exponentially in `k`.  The mechanism is the paper's:
T14 (`exists_long_cell`) supplies a component of the survivor set `S(v)` of
length at least `r^{|v|}/(|v|+1)`, so (D_λ) supplies a kind word `u` with

  `|u| ≤ C (|v| log λ + log(|v|+1))`   (`exists_extension_len`),

and `v ↦ M u v` gains a knot while keeping all the earlier ones.  Iterating,

  `|v_{k+1}| ≤ (1 + C log λ) |v_k| + C log(|v_k|+1) + 1 ≤ 1 + B |v_k|`,

which is `qword_length_le`.

## Conventions (SCRUPLES)

* The construction is parameterised by an arbitrary extension function `ext`
  (`qword`), so that the nesting lemmas are proved once and used both for the
  bound and for the knot count; `Density.dword` is the same construction with a
  different (unquantified) choice of extension, and is left untouched.
* `d_λ` is the development's `KnotGame.d`, `sInf {n | k ≤ N λ n}`; the bound is
  stated as a real inequality `(d lam k : ℝ) ≤ B ^ k - 1`.
* The paper writes `O(log |v_k|)` for the second term; here it is the explicit
  `C log(|v_k|+1)`, which is what `exists_long_cell` yields.
* The hypothesis is used only through `exists_extension_len`; no `λ` is claimed
  to satisfy it.
-/

namespace KnotGame

open Real

variable {lam C : ℝ}

/-! ## The quantitative hypothesis -/

/-- **(D_λ)**.  Every subinterval of `(0,1)` of length `ε` contains the
endpoint of a kind word of length at most `C log(1/ε)`. -/
def KindDenseQuant (lam : ℝ) (C : ℝ) : Prop :=
  ∀ c d : ℝ, 0 ≤ c → c < d → d ≤ 1 →
    ∃ u : List Move, survivesWord lam (1/2) u ∧
      c < posAfter lam (1/2) u ∧ posAfter lam (1/2) u < d ∧
      (u.length : ℝ) ≤ C * Real.log (1 / (d - c))

/-- (D_λ) is stronger than the topological density hypothesis. -/
lemma kindDense_of_quant (H : KindDenseQuant lam C) : KindDense lam := by
  intro c d hc hcd hd
  obtain ⟨u, hu, h1, h2, -⟩ := H c d hc hcd hd
  exact ⟨u, hu, h1, h2⟩

/-! ## The quantitative extension step -/

/-- **The quantitative extension step.**  Under (D_λ) the kind word prepended
to `v` can be taken of length at most `C(|v| log λ + log(|v|+1))`. -/
lemma exists_extension_len (h : 1 < lam) (hC : 0 ≤ C) (H : KindDenseQuant lam C)
    (v : List Move) :
    ∃ u : List Move, survivesWord lam (1/2) (u ++ v) ∧
      (u.length : ℝ) ≤ C * ((v.length : ℝ) * Real.log lam + Real.log ((v.length : ℝ) + 1)) := by
  obtain ⟨p, hp, hlong, hall⟩ := exists_long_cell h v
  obtain ⟨hp0, hp12, hp1⟩ := (tidy_cells h v).bounds p hp
  obtain ⟨u, hu, hu1, hu2, hulen⟩ := H p.1 p.2 hp0 hp12 hp1
  refine ⟨u, by rw [survivesWord_append]; exact ⟨hu, (hall _ hu1 hu2).2.2⟩, ?_⟩
  refine le_trans hulen ?_
  have hr0 : 0 < r lam := r_pos lam h
  have hlam0 : (0:ℝ) < lam := lt_trans zero_lt_one h
  have hpow : 0 < (r lam) ^ v.length := pow_pos hr0 _
  have hden : (0:ℝ) < (v.length : ℝ) + 1 := by positivity
  have heps : 0 < (r lam) ^ v.length / ((v.length : ℝ) + 1) := by positivity
  have hd0 : 0 < p.2 - p.1 := by linarith
  -- `log (1/(p.2-p.1)) ≤ log ((|v|+1) / r^{|v|})`
  have hmono : Real.log (1 / (p.2 - p.1))
      ≤ Real.log (((v.length : ℝ) + 1) / (r lam) ^ v.length) := by
    have hle : 1 / (p.2 - p.1) ≤ ((v.length : ℝ) + 1) / (r lam) ^ v.length := by
      rw [div_le_div_iff₀ hd0 hpow]
      have : (r lam) ^ v.length ≤ ((v.length : ℝ) + 1) * (p.2 - p.1) := by
        rw [div_le_iff₀ hden] at hlong
        linarith
      linarith
    exact Real.log_le_log (by positivity) hle
  have hsplit : Real.log (((v.length : ℝ) + 1) / (r lam) ^ v.length)
      = (v.length : ℝ) * Real.log lam + Real.log ((v.length : ℝ) + 1) := by
    rw [Real.log_div (ne_of_gt hden) (ne_of_gt hpow), Real.log_pow]
    have : r lam = lam⁻¹ := rfl
    rw [this, Real.log_inv]
    ring
  rw [hsplit] at hmono
  exact mul_le_mul_of_nonneg_left hmono hC

/-! ## The nested family -/

/-- The nested family built from an extension function: `qword ext (k+1)` is
`M` followed by `ext (qword ext k)` and `qword ext k`. -/
def qword (ext : List Move → List Move) : ℕ → List Move
  | 0 => []
  | k + 1 => Move.M :: (ext (qword ext k) ++ qword ext k)

lemma qword_succ (ext : List Move → List Move) (k : ℕ) :
    qword ext (k + 1) = Move.M :: (ext (qword ext k) ++ qword ext k) := rfl

/-- Each member of the family is a suffix of all the later ones. -/
lemma qword_suffix (ext : List Move → List Move) :
    ∀ {m k : ℕ}, m ≤ k → ∃ p, qword ext k = p ++ qword ext m := by
  intro m k
  induction k with
  | zero => intro hk; exact ⟨[], by rw [Nat.le_zero.mp hk]; simp⟩
  | succ k ih =>
      intro hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hk) with hlt | rfl
      · obtain ⟨p, hp⟩ := ih (Nat.lt_succ_iff.mp hlt)
        exact ⟨Move.M :: (ext (qword ext k) ++ p), by rw [qword_succ, hp]; simp⟩
      · exact ⟨[], by simp⟩

lemma qword_length_lt (ext : List Move → List Move) (k : ℕ) :
    (qword ext k).length < (qword ext (k + 1)).length := by
  rw [qword_succ]
  simp only [List.length_cons, List.length_append]
  omega

lemma qword_length_strictMono (ext : List Move → List Move) :
    StrictMono fun k => (qword ext k).length :=
  strictMono_nat_of_lt_succ (qword_length_lt ext)

/-- Prepending the `M` creates a knot of age `|qword (k+1)| − 1`. -/
lemma hasKnotAge_qword_succ {ext : List Move → List Move}
    (hext : ∀ v, survivesWord lam (1/2) (ext v ++ v)) (k : ℕ) :
    HasKnotAge lam (qword ext (k + 1)) ((qword ext (k + 1)).length - 1) := by
  have hlen : (qword ext (k + 1)).length - 1 = (ext (qword ext k) ++ qword ext k).length := by
    rw [qword_succ]; simp
  rw [hlen, qword_succ]
  exact ⟨_, knotAt_cons_M (hext (qword ext k))⟩

lemma hasKnotAge_qword {ext : List Move → List Move}
    (hext : ∀ v, survivesWord lam (1/2) (ext v ++ v)) {i k : ℕ} (hik : i < k) :
    HasKnotAge lam (qword ext k) ((qword ext (i + 1)).length - 1) := by
  obtain ⟨p, hp⟩ := qword_suffix ext (m := i + 1) (k := k) hik
  rw [hp]
  exact hasKnotAge_append p (hasKnotAge_qword_succ hext i)

/-- The `k`-th member of the family carries at least `k` knots. -/
lemma le_N_qword_length (h : 1 < lam) {ext : List Move → List Move}
    (hext : ∀ v, survivesWord lam (1/2) (ext v ++ v)) (k : ℕ) :
    k ≤ N lam (qword ext k).length := by
  classical
  set A : Finset ℕ := (Finset.range k).image (fun i => (qword ext (i + 1)).length - 1) with hA
  have hinj : ∀ i ∈ Finset.range k, ∀ j ∈ Finset.range k,
      (qword ext (i + 1)).length - 1 = (qword ext (j + 1)).length - 1 → i = j := by
    intro i _ j _ hij
    have hi : 0 < (qword ext (i + 1)).length := by rw [qword_succ]; simp
    have hj : 0 < (qword ext (j + 1)).length := by rw [qword_succ]; simp
    have : (qword ext (i + 1)).length = (qword ext (j + 1)).length := by omega
    have := (qword_length_strictMono ext).injective this
    omega
  have hcard : A.card = k := by
    rw [hA, Finset.card_image_of_injOn (fun i hi j hj => hinj i hi j hj), Finset.card_range]
  have hages : ∀ a ∈ A, HasKnotAge lam (qword ext k) a := by
    intro a ha
    rw [hA, Finset.mem_image] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    exact hasKnotAge_qword hext (Finset.mem_range.mp hi)
  calc k = A.card := hcard.symm
    _ ≤ (run lam (qword ext k)).card := card_run_ge_of_ages h (qword ext k) A hages
    _ = births lam (qword ext k) := card_run h (qword ext k)
    _ ≤ N lam (qword ext k).length := births_le_N h (qword ext k)

/-! ## The exponential bound -/

/-- The growth constant of the recursion. -/
noncomputable def growth (lam C : ℝ) : ℝ := max 2 (1 + C * (Real.log lam + 1))

lemma two_le_growth (lam C : ℝ) : 2 ≤ growth lam C := le_max_left _ _

/-- The length recursion `|v_{k+1}| ≤ 1 + B |v_k|`. -/
lemma qword_length_step (h : 1 < lam) (hC : 0 ≤ C) {ext : List Move → List Move}
    (hlen : ∀ v : List Move, (ext v).length
      ≤ C * ((v.length : ℝ) * Real.log lam + Real.log ((v.length : ℝ) + 1))) (k : ℕ) :
    ((qword ext (k + 1)).length : ℝ) ≤ 1 + growth lam C * (qword ext k).length := by
  set L : ℝ := ((qword ext k).length : ℝ) with hL
  have hL0 : 0 ≤ L := by positivity
  have hlog : Real.log (L + 1) ≤ L := by
    have := Real.log_le_sub_one_of_pos (x := L + 1) (by linarith)
    linarith
  have hloglam : 0 ≤ Real.log lam := Real.log_nonneg (le_of_lt h)
  have h1 : ((qword ext (k + 1)).length : ℝ) = 1 + ((ext (qword ext k)).length : ℝ) + L := by
    rw [qword_succ]
    push_cast [List.length_cons, List.length_append]
    ring
  have h2 : ((ext (qword ext k)).length : ℝ) ≤ C * (L * Real.log lam + Real.log (L + 1)) :=
    hlen (qword ext k)
  have h3 : C * (L * Real.log lam + Real.log (L + 1)) ≤ C * (L * Real.log lam + L) := by
    have := mul_le_mul_of_nonneg_left hlog hC
    nlinarith
  have h4 : C * (L * Real.log lam + L) + L ≤ growth lam C * L := by
    have hge : 1 + C * (Real.log lam + 1) ≤ growth lam C := le_max_right _ _
    nlinarith
  linarith

/-- **The exponential bound on the lengths**: `|v_k| ≤ B ^ k − 1`. -/
lemma qword_length_le (h : 1 < lam) (hC : 0 ≤ C) {ext : List Move → List Move}
    (hlen : ∀ v : List Move, (ext v).length
      ≤ C * ((v.length : ℝ) * Real.log lam + Real.log ((v.length : ℝ) + 1))) :
    ∀ k : ℕ, ((qword ext k).length : ℝ) ≤ growth lam C ^ k - 1 := by
  intro k
  induction k with
  | zero => simp [qword]
  | succ k ih =>
      have hB : 2 ≤ growth lam C := two_le_growth lam C
      have hpow : (0:ℝ) < growth lam C ^ k := by positivity
      have hstep := qword_length_step h hC hlen k
      have : growth lam C * ((qword ext k).length : ℝ) ≤ growth lam C * (growth lam C ^ k - 1) :=
        mul_le_mul_of_nonneg_left ih (by linarith)
      have hexp : growth lam C * (growth lam C ^ k - 1) = growth lam C ^ (k + 1) - growth lam C := by
        rw [pow_succ]; ring
      linarith [hexp ▸ this]

/-! ## The theorem -/

/-- **T26** (paper Theorem `thm:density`).  Under (D_λ) the knot counts are
unbounded and, in addition, `d_λ(k)` is at most exponential in `k`:
`d_λ(k) ≤ B ^ k − 1` with `B = max 2 (1 + C (log λ + 1))`. -/
theorem d_le_pow (h : 1 < lam) (hC : 0 ≤ C) (H : KindDenseQuant lam C) (k : ℕ) :
    ((d lam k : ℕ) : ℝ) ≤ growth lam C ^ k - 1 := by
  classical
  set ext : List Move → List Move :=
    fun v => Classical.choose (exists_extension_len h hC H v) with hext_def
  have hext : ∀ v, survivesWord lam (1/2) (ext v ++ v) :=
    fun v => (Classical.choose_spec (exists_extension_len h hC H v)).1
  have hlen : ∀ v : List Move, ((ext v).length : ℝ)
      ≤ C * ((v.length : ℝ) * Real.log lam + Real.log ((v.length : ℝ) + 1)) :=
    fun v => (Classical.choose_spec (exists_extension_len h hC H v)).2
  have hk : k ≤ N lam (qword ext k).length := le_N_qword_length h hext k
  have hd : d lam k ≤ (qword ext k).length := Nat.sInf_le hk
  have hcast : ((d lam k : ℕ) : ℝ) ≤ ((qword ext k).length : ℝ) := by exact_mod_cast hd
  exact le_trans hcast (qword_length_le h hC hlen k)

/-- **T26, the unboundedness conclusion.**  (D_λ) implies `N_λ = ∞`, through
the topological criterion. -/
theorem N_unbounded_of_kindDenseQuant (h : 1 < lam) (H : KindDenseQuant lam C) :
    ∀ K : ℕ, ∃ n : ℕ, K ≤ N lam n :=
  N_unbounded_of_kindDense h (kindDense_of_quant H)

end KnotGame
