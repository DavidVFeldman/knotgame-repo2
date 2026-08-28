import RequestProject.BranchingCount

/-!
# From a doubling property to an exponential count (round 7)

`K lam m` (see `RequestProject.BranchingCount`) counts the length-`m` branch
words along which `1/2` survives.  Round 4 certified the unconditional *linear*
bound `m/(B+1) ≤ K lam m`.  This file isolates the mechanism that upgrades it to
an exponential one:

  if some closed interval `[a,b] ⊆ (0,1)` containing `1/2` has the property
  that every one of its points admits **two distinct** legal branch words of a
  fixed length `T` whose images again lie in `[a,b]` (`Doubling lam a b T`),
  then `2 ^ (m / T) ≤ K lam m` (`two_pow_le_K_of_doubling`).

Two elementary facts do the work.

* *Absorption.*  Both branch maps preserve `(-∞,0]` and preserve `[1,∞)`, so a
  branch word is legal from `x ∈ (0,1)` **iff** its final image lies in `(0,1)`
  (`bSurvives_of_image_mem`).  Only the image has to be controlled.
* *Renewal.*  The two words of the doubling property prefix the surviving words
  of their images, and the resulting families are disjoint because the words
  differ.  This is the deterministic form of the renewal inequality
  (`two_mul_kappa_le`): inside `[a,b]` the count at least doubles every `T`
  steps.

The certificates that supply `Doubling` at particular parameters are in
`RequestProject.ExpCert`; see `RequestProject.ExpLower` (at `lam = 3/2`) and
`RequestProject.ExpWindow` (uniformly over a parameter window).

## Conventions (SCRUPLES)

* Words are lists of branches applied left to right, as in `bSurvives`.
* `Doubling` asks only that the images lie in `[a,b]`; legality of the two words
  is *derived* from absorption, not assumed.
* The bound is `2 ^ (m / T)` with natural division: it counts only the branchings
  completed in the first `T * (m / T)` steps.
-/

namespace KnotGame
namespace ExpCount

open KnotGame.Branching
open scoped Classical

variable {lam a b : ℝ} {T : ℕ}

/-! ### Applying a branch word -/

/-- Applying a branch word to a point. -/
noncomputable def rapp (lam : ℝ) (x : ℝ) (w : List (Fin 2)) : ℝ :=
  w.foldl (fun y e => f lam e y) x

@[simp] lemma rapp_nil (lam x : ℝ) : rapp lam x [] = x := rfl

@[simp] lemma rapp_cons (lam x : ℝ) (e : Fin 2) (w : List (Fin 2)) :
    rapp lam x (e :: w) = rapp lam (f lam e x) w := rfl

lemma rapp_append (lam x : ℝ) (u v : List (Fin 2)) :
    rapp lam x (u ++ v) = rapp lam (rapp lam x u) v := by
  simp [rapp, List.foldl_append]

/-- Each branch map is increasing, hence so is the action of a word. -/
lemma rapp_mono (h1 : 1 < lam) (w : List (Fin 2)) {x y : ℝ} (h : x ≤ y) :
    rapp lam x w ≤ rapp lam y w := by
  induction w generalizing x y with
  | nil => simpa using h
  | cons e w ih =>
      refine ih ?_
      rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl <;>
        · simp only [f_zero, f_one]
          nlinarith

/-! ### Absorption -/

lemma rapp_nonpos (h1 : 1 < lam) {x : ℝ} (hx : x ≤ 0) (w : List (Fin 2)) :
    rapp lam x w ≤ 0 := by
  induction w generalizing x with
  | nil => simpa using hx
  | cons e w ih =>
      refine ih ?_
      rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl <;>
        · simp only [f_zero, f_one]
          nlinarith

lemma one_le_rapp (h1 : 1 < lam) {x : ℝ} (hx : 1 ≤ x) (w : List (Fin 2)) :
    1 ≤ rapp lam x w := by
  induction w generalizing x with
  | nil => simpa using hx
  | cons e w ih =>
      refine ih ?_
      rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl <;>
        · simp only [f_zero, f_one]
          nlinarith

/-- A branch is legal at `x ∈ (0,1)` exactly when its image lies in `(0,1)`. -/
lemma bLegal_iff (h1 : 1 < lam) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (e : Fin 2) :
    BLegal lam e x ↔ (0 < f lam e x ∧ f lam e x < 1) := by
  have hlam : (0:ℝ) < lam := lt_trans zero_lt_one h1
  rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl
  · rw [BLegal_zero, f_zero]
    constructor
    · intro h
      refine ⟨by positivity, ?_⟩
      have : lam * x < lam * r lam := mul_lt_mul_of_pos_left h hlam
      rwa [lam_mul_r h1] at this
    · rintro ⟨-, h⟩
      have hr : lam * r lam = 1 := lam_mul_r h1
      nlinarith
  · rw [BLegal_one, f_one]
    constructor
    · intro h
      have : lam * g lam < lam * x := mul_lt_mul_of_pos_left h hlam
      rw [lam_mul_g h1] at this
      exact ⟨by linarith, by nlinarith⟩
    · rintro ⟨h, -⟩
      have hg : lam * g lam = lam - 1 := lam_mul_g h1
      nlinarith

/-- **Absorption.**  A word is legal from a point of `(0,1)` as soon as its image
lies in `(0,1)`. -/
lemma bSurvives_of_image_mem (h1 : 1 < lam) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    {w : List (Fin 2)} (h0 : 0 < rapp lam x w) (h1' : rapp lam x w < 1) :
    bSurvives lam x w := by
  induction w generalizing x with
  | nil => trivial
  | cons e w ih =>
      rw [rapp_cons] at h0 h1'
      have hy0 : 0 < f lam e x := by
        by_contra hle
        push_neg at hle
        exact absurd h0 (not_lt.mpr (rapp_nonpos h1 hle w))
      have hy1 : f lam e x < 1 := by
        by_contra hge
        push_neg at hge
        exact absurd h1' (not_lt.mpr (one_le_rapp h1 hge w))
      exact ⟨(bLegal_iff h1 hx0 hx1 e).2 ⟨hy0, hy1⟩, ih hy0 hy1 h0 h1'⟩

/-- Survival along a concatenation. -/
lemma bSurvives_append {x : ℝ} {u v : List (Fin 2)} :
    bSurvives lam x (u ++ v) ↔ bSurvives lam x u ∧ bSurvives lam (rapp lam x u) v := by
  induction u generalizing x with
  | nil => simp [bSurvives]
  | cons e u ih =>
      show (BLegal lam e x ∧ bSurvives lam (f lam e x) (u ++ v)) ↔ _
      rw [ih, rapp_cons]
      show _ ↔ (BLegal lam e x ∧ _) ∧ _
      tauto

/-- A surviving word keeps the point inside `(0,1)`. -/
lemma rapp_mem_Ioo (h1 : 1 < lam) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) {w : List (Fin 2)}
    (hw : bSurvives lam x w) : 0 < rapp lam x w ∧ rapp lam x w < 1 := by
  induction w generalizing x with
  | nil => exact ⟨hx0, hx1⟩
  | cons e w ih =>
      obtain ⟨hleg, hrest⟩ := hw
      have := (bLegal_iff h1 hx0 hx1 e).1 hleg
      exact ih this.1 this.2 hrest

/-! ### Counting -/

/-- All branch words of a given length. -/
def allWords (n : ℕ) : Finset (List (Fin 2)) :=
  (Finset.univ : Finset (Fin n → Fin 2)).image (fun w => List.ofFn w)

lemma mem_allWords {n : ℕ} {w : List (Fin 2)} : w ∈ allWords n ↔ w.length = n := by
  constructor
  · intro hw
    simp only [allWords, Finset.mem_image, Finset.mem_univ, true_and] at hw
    obtain ⟨g, rfl⟩ := hw
    simp
  · intro h
    subst h
    exact Finset.mem_image.2 ⟨fun i => w.get i, Finset.mem_univ _, by simp⟩

/-- The words of length `n` along which `x` survives. -/
noncomputable def SW (lam x : ℝ) (n : ℕ) : Finset (List (Fin 2)) :=
  (allWords n).filter (fun w => bSurvives lam x w)

/-- The number of words of length `n` along which `x` survives. -/
noncomputable def Kx (lam x : ℝ) (n : ℕ) : ℕ := (SW lam x n).card

lemma mem_SW {x : ℝ} {n : ℕ} {w : List (Fin 2)} :
    w ∈ SW lam x n ↔ w.length = n ∧ bSurvives lam x w := by
  simp [SW, mem_allWords]

lemma Kx_zero (lam x : ℝ) : Kx lam x 0 = 1 := by
  have h : SW lam x 0 = {([] : List (Fin 2))} := by
    ext w
    rw [mem_SW, Finset.mem_singleton]
    constructor
    · rintro ⟨hl, -⟩
      exact List.eq_nil_of_length_eq_zero hl
    · rintro rfl
      exact ⟨rfl, trivial⟩
  rw [Kx, h, Finset.card_singleton]

/-- The least number of surviving words of length `n` over `[a,b]`. -/
noncomputable def kappa (lam a b : ℝ) (n : ℕ) : ℕ :=
  sInf {k | ∃ x : ℝ, a ≤ x ∧ x ≤ b ∧ Kx lam x n = k}

lemma kappa_le {x : ℝ} (hx0 : a ≤ x) (hx1 : x ≤ b) (n : ℕ) : kappa lam a b n ≤ Kx lam x n :=
  Nat.sInf_le ⟨x, hx0, hx1, rfl⟩

lemma le_kappa (hab : a ≤ b) {c n : ℕ} (h : ∀ x : ℝ, a ≤ x → x ≤ b → c ≤ Kx lam x n) :
    c ≤ kappa lam a b n := by
  refine le_csInf ⟨Kx lam a n, ⟨a, le_rfl, hab, rfl⟩⟩ ?_
  rintro k ⟨x, h1, h2, rfl⟩
  exact h x h1 h2

/-! ### The doubling property and the exponential bound -/

/-- **Doubling on `[a,b]`.**  Every point of `[a,b]` admits two distinct branch
words of length `T` whose images again lie in `[a,b]`. -/
def Doubling (lam a b : ℝ) (T : ℕ) : Prop :=
  ∀ x : ℝ, a ≤ x → x ≤ b → ∃ u v : List (Fin 2), u ≠ v ∧ u.length = T ∧ v.length = T ∧
    a ≤ rapp lam x u ∧ rapp lam x u ≤ b ∧ a ≤ rapp lam x v ∧ rapp lam x v ≤ b

/-- Prefixing a surviving word of length `T`. -/
lemma image_append_subset {x : ℝ} {w : List (Fin 2)} (hw : bSurvives lam x w)
    (hlen : w.length = T) (n : ℕ) :
    (SW lam (rapp lam x w) n).image (fun z => w ++ z) ⊆ SW lam x (n + T) := by
  intro z hz
  simp only [Finset.mem_image] at hz
  obtain ⟨z', hz', rfl⟩ := hz
  rw [mem_SW] at hz' ⊢
  refine ⟨?_, bSurvives_append.2 ⟨hw, hz'.2⟩⟩
  rw [List.length_append, hlen, hz'.1]
  omega

/-- **The renewal step.**  Inside `[a,b]` the count at least doubles every `T`
steps. -/
lemma two_mul_kappa_le (h1 : 1 < lam) (ha : 0 < a) (hb : b < 1) (hdb : Doubling lam a b T)
    (n : ℕ) {x : ℝ} (hx0 : a ≤ x) (hx1 : x ≤ b) :
    2 * kappa lam a b n ≤ Kx lam x (n + T) := by
  obtain ⟨u, v, hne, hlu, hlv, hu1, hu2, hv1, hv2⟩ := hdb x hx0 hx1
  have hx0' : (0:ℝ) < x := lt_of_lt_of_le ha hx0
  have hx1' : x < 1 := lt_of_le_of_lt hx1 hb
  have hsu : bSurvives lam x u :=
    bSurvives_of_image_mem h1 hx0' hx1' (by linarith) (by linarith)
  have hsv : bSurvives lam x v :=
    bSurvives_of_image_mem h1 hx0' hx1' (by linarith) (by linarith)
  have hiu : Function.Injective (fun z : List (Fin 2) => u ++ z) :=
    fun z1 z2 h => List.append_cancel_left h
  have hiv : Function.Injective (fun z : List (Fin 2) => v ++ z) :=
    fun z1 z2 h => List.append_cancel_left h
  have hdisj : Disjoint ((SW lam (rapp lam x u) n).image (fun z => u ++ z))
      ((SW lam (rapp lam x v) n).image (fun z => v ++ z)) := by
    rw [Finset.disjoint_left]
    rintro c hc hc'
    simp only [Finset.mem_image] at hc hc'
    obtain ⟨z1, -, rfl⟩ := hc
    obtain ⟨z2, -, h2⟩ := hc'
    have := congrArg (List.take T) h2
    rw [List.take_left' hlv, List.take_left' hlu] at this
    exact hne this.symm
  have hsub : ((SW lam (rapp lam x u) n).image (fun z => u ++ z)) ∪
      ((SW lam (rapp lam x v) n).image (fun z => v ++ z)) ⊆ SW lam x (n + T) :=
    Finset.union_subset (image_append_subset hsu hlu n) (image_append_subset hsv hlv n)
  calc 2 * kappa lam a b n = kappa lam a b n + kappa lam a b n := by ring
    _ ≤ Kx lam (rapp lam x u) n + Kx lam (rapp lam x v) n :=
        Nat.add_le_add (kappa_le hu1 hu2 n) (kappa_le hv1 hv2 n)
    _ = ((SW lam (rapp lam x u) n).image (fun z => u ++ z)).card +
          ((SW lam (rapp lam x v) n).image (fun z => v ++ z)).card := by
        rw [Finset.card_image_of_injective _ hiu, Finset.card_image_of_injective _ hiv]; rfl
    _ = (((SW lam (rapp lam x u) n).image (fun z => u ++ z)) ∪
          ((SW lam (rapp lam x v) n).image (fun z => v ++ z))).card :=
        (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ Kx lam x (n + T) := Finset.card_le_card hsub

lemma two_pow_le_kappa (h1 : 1 < lam) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hdb : Doubling lam a b T) (j : ℕ) : 2 ^ j ≤ kappa lam a b (T * j) := by
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
        _ ≤ Kx lam x (T * j + T) := two_mul_kappa_le h1 ha hb hdb (T * j) hx1 hx2

/-- From any point of `(0,1)` the canonical ("good child") branch supplies a
surviving word of every length. -/
lemma exists_surviving_word (h1 : 1 < lam) (h2 : lam < 2) {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1)
    (k : ℕ) : ∃ z : List (Fin 2), z.length = k ∧ bSurvives lam y z := by
  induction k generalizing y with
  | zero => exact ⟨[], rfl, trivial⟩
  | succ k ih =>
      have hleg : BLegal lam (cb lam y) y := cb_legal h1 h2 y
      have hmem : f lam (cb lam y) y ∈ Set.Ioo (0:ℝ) 1 := f_mem_Ioo h1 ⟨hy0, hy1⟩ hleg
      obtain ⟨z, hz, hzs⟩ := ih hmem.1 hmem.2
      exact ⟨cb lam y :: z, by simp [hz], ⟨hleg, hzs⟩⟩

/-- Padding: the count is monotone in the length. -/
lemma Kx_mono (h1 : 1 < lam) (h2 : lam < 2) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) {n m : ℕ}
    (h : n ≤ m) : Kx lam x n ≤ Kx lam x m := by
  have hex : ∀ w : List (Fin 2), ∃ z : List (Fin 2),
      w ∈ SW lam x n → (z.length = m - n ∧ bSurvives lam (rapp lam x w) z) := by
    intro w
    by_cases hw : w ∈ SW lam x n
    · rw [mem_SW] at hw
      obtain ⟨h0, h1'⟩ := rapp_mem_Ioo h1 hx0 hx1 hw.2
      obtain ⟨z, hz⟩ := exists_surviving_word h1 h2 h0 h1' (m - n)
      exact ⟨z, fun _ => hz⟩
    · exact ⟨[], fun hc => absurd hc hw⟩
  choose pad hpad using hex
  refine Finset.card_le_card_of_injOn (fun w => w ++ pad w) ?_ ?_
  · intro w hw
    simp only [Finset.mem_coe] at hw ⊢
    obtain ⟨hlen, hsurv⟩ := mem_SW.1 hw
    obtain ⟨hplen, hpsurv⟩ := hpad w hw
    rw [mem_SW]
    refine ⟨?_, bSurvives_append.2 ⟨hsurv, hpsurv⟩⟩
    rw [List.length_append, hlen, hplen]
    omega
  · intro w1 hw1 w2 hw2 heq
    simp only [Finset.mem_coe] at hw1 hw2
    have h1' := (mem_SW.1 hw1).1
    have h2' := (mem_SW.1 hw2).1
    have := congrArg (List.take n) heq
    rwa [List.take_left' h1', List.take_left' h2'] at this

lemma Kx_eq_K (lam : ℝ) (m : ℕ) : Kx lam (1/2 : ℝ) m = K lam m := by
  rw [K_eq_card_bSurvives, Kx, SW, allWords, Finset.filter_image,
    Finset.card_image_of_injective _ (List.ofFn_injective)]

/-- **From doubling to an exponential count.**  If every point of a closed
interval `[a,b] ⊆ (0,1)` containing `1/2` has two distinct legal continuations of
length `T` returning to `[a,b]`, then `K lam m ≥ 2 ^ (m / T)`. -/
theorem two_pow_le_K_of_doubling (h1 : 1 < lam) (h2 : lam < 2) (ha : 0 < a) (hb : b < 1)
    (ha2 : a ≤ 1/2) (hb2 : (1/2 : ℝ) ≤ b) (hdb : Doubling lam a b T) (m : ℕ) :
    2 ^ (m / T) ≤ K lam m := by
  have hab : a ≤ b := le_trans ha2 hb2
  rw [← Kx_eq_K]
  calc 2 ^ (m / T) ≤ kappa lam a b (T * (m / T)) := two_pow_le_kappa h1 ha hb hab hdb _
    _ ≤ Kx lam (1/2 : ℝ) (T * (m / T)) := kappa_le ha2 hb2 _
    _ ≤ Kx lam (1/2 : ℝ) m := by
        refine Kx_mono h1 h2 (by linarith) (by linarith) ?_
        calc T * (m / T) = m / T * T := Nat.mul_comm _ _
          _ ≤ m := Nat.div_mul_le_self m T

end ExpCount
end KnotGame
