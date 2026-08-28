import RequestProject.Branching

/-!
# A continuum of kind sequences (round 4, T12a)

An explicit injection of the Cantor space `ℕ → Bool` into the infinite branch
itineraries along which the point `1/2` survives forever, valid for every
`lam ∈ (1,2)` with `lam² < lam + 1` (i.e. `lam < φ`).

The construction is the one of the commission: run the dynamics from `1/2`;
at a **window visit** consume the next bit of `b` and follow the corresponding
child, and at every other point follow the (unique) forced branch.  The
bookkeeping is carried by `bitState`, whose second component is the index of the
next unread bit.

## Conventions (SCRUPLES)

* Outside the window the *forced* branch is produced by `Branching.cb`, which
  agrees with the forced branch there (`cb_of_le_g`, `cb_of_r_le`); no separate
  definition is introduced.
* Injectivity needs every bit to be read, i.e. infinitely many window visits.
  This is `exists_window_ge`, which uses only `1 < lam < 2`, `lam² < lam + 1`
  and the *finiteness* of the return time; the quantitative bound `B` of T11d is
  not needed.  Consequently T12a is proved for every `lam < φ`, not only on the
  anchor window `[lam₀, lam₁]` of the commission.
-/

namespace KnotGame
namespace Branching

open Set
open scoped Classical

variable {lam : ℝ}

/-! ### Infinite itineraries -/

/-- The orbit of `x` along the infinite branch itinerary `e`. -/
noncomputable def itinOrbit (lam : ℝ) (x : ℝ) (e : ℕ → Fin 2) : ℕ → ℝ
  | 0 => x
  | n + 1 => f lam (e n) (itinOrbit lam x e n)

@[simp] lemma itinOrbit_zero (lam x : ℝ) (e : ℕ → Fin 2) : itinOrbit lam x e 0 = x := rfl

@[simp] lemma itinOrbit_succ (lam x : ℝ) (e : ℕ → Fin 2) (n : ℕ) :
    itinOrbit lam x e (n + 1) = f lam (e n) (itinOrbit lam x e n) := rfl

/-- `e` is a *survival itinerary* of `x`: every branch it prescribes is legal at
the point reached so far. -/
def Surviving (lam : ℝ) (x : ℝ) (e : ℕ → Fin 2) : Prop :=
  ∀ n, BLegal lam (e n) (itinOrbit lam x e n)

/-- Two itineraries agreeing before time `n` give the same point at time `n`. -/
lemma itinOrbit_congr (lam x : ℝ) {e e' : ℕ → Fin 2} {n : ℕ}
    (h : ∀ j < n, e j = e' j) : itinOrbit lam x e n = itinOrbit lam x e' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [itinOrbit_succ, itinOrbit_succ, ih (fun j hj => h j (by omega)), h n (by omega)]

/-- A geometric progression with positive ratio `> 1` is unbounded. -/
lemma not_forall_pow_mul_le (h1 : 1 < lam) {y c : ℝ} (hy : 0 < y)
    (hall : ∀ i : ℕ, lam ^ i * y ≤ c) : False := by
  obtain ⟨i, hi⟩ := pow_unbounded_of_one_lt (c / y) h1
  have := hall i
  rw [div_lt_iff₀ hy] at hi
  linarith

/-! ### The bit-driven dynamics -/

/-- The branch taken at the state `s = (x, k)`: the `k`-th bit's child if `x` is a
window point, the forced branch otherwise. -/
noncomputable def bitBranch (lam : ℝ) (b : ℕ → Bool) (s : ℝ × ℕ) : Fin 2 :=
  if s.1 ∈ Window lam then (if b s.2 then 1 else 0) else cb lam s.1

/-- The state after `n` steps: the current point, and the index of the next
unread bit. -/
noncomputable def bitState (lam : ℝ) (b : ℕ → Bool) (x : ℝ) : ℕ → ℝ × ℕ
  | 0 => (x, 0)
  | n + 1 =>
      (f lam (bitBranch lam b (bitState lam b x n)) (bitState lam b x n).1,
        (bitState lam b x n).2 + (if (bitState lam b x n).1 ∈ Window lam then 1 else 0))

@[simp] lemma bitState_zero (lam : ℝ) (b : ℕ → Bool) (x : ℝ) : bitState lam b x 0 = (x, 0) := rfl

lemma bitState_succ (lam : ℝ) (b : ℕ → Bool) (x : ℝ) (n : ℕ) :
    bitState lam b x (n + 1) =
      (f lam (bitBranch lam b (bitState lam b x n)) (bitState lam b x n).1,
        (bitState lam b x n).2 + (if (bitState lam b x n).1 ∈ Window lam then 1 else 0)) := rfl

lemma bitState_fst_succ (lam : ℝ) (b : ℕ → Bool) (x : ℝ) (n : ℕ) :
    (bitState lam b x (n + 1)).1
      = f lam (bitBranch lam b (bitState lam b x n)) (bitState lam b x n).1 := rfl

lemma bitState_snd_succ (lam : ℝ) (b : ℕ → Bool) (x : ℝ) (n : ℕ) :
    (bitState lam b x (n + 1)).2
      = (bitState lam b x n).2 + (if (bitState lam b x n).1 ∈ Window lam then 1 else 0) := rfl

/-- The itinerary produced by the bit stream `b`, started at `1/2`. -/
noncomputable def theta (lam : ℝ) (b : ℕ → Bool) (n : ℕ) : Fin 2 :=
  bitBranch lam b (bitState lam b (1/2) n)

/-- Whatever the state, the branch chosen is legal. -/
lemma bitBranch_legal (h1 : 1 < lam) (h2 : lam < 2) (b : ℕ → Bool) (s : ℝ × ℕ) :
    BLegal lam (bitBranch lam b s) s.1 := by
  unfold bitBranch
  by_cases hw : s.1 ∈ Window lam
  · rw [if_pos hw]
    exact BLegal_of_mem_Window hw _
  · rw [if_neg hw]
    exact cb_legal h1 h2 s.1

/-- The point never leaves `(0,1)`. -/
lemma bitState_mem_Ioo (h1 : 1 < lam) (h2 : lam < 2) (b : ℕ → Bool) {x : ℝ}
    (hx : x ∈ Set.Ioo (0:ℝ) 1) (n : ℕ) : (bitState lam b x n).1 ∈ Set.Ioo (0:ℝ) 1 := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
      rw [bitState_fst_succ]
      exact f_mem_Ioo h1 ih (bitBranch_legal h1 h2 b _)

/-- The orbit of `theta lam b` is the first component of the state. -/
lemma itinOrbit_theta (lam : ℝ) (b : ℕ → Bool) (n : ℕ) :
    itinOrbit lam (1/2) (theta lam b) n = (bitState lam b (1/2) n).1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [itinOrbit_succ, ih, bitState_fst_succ, theta]

/-- **The itineraries produced are survival itineraries of `1/2`.** -/
theorem theta_surviving (h1 : 1 < lam) (h2 : lam < 2) (b : ℕ → Bool) :
    Surviving lam (1/2) (theta lam b) := by
  intro n
  rw [itinOrbit_theta, theta]
  exact bitBranch_legal h1 h2 b _

/-! ### Every bit gets read -/

/-- While the forced dynamics from `(0, g]` misses the window it stays in
`(0, g]`, and it is multiplication by `lam^i`. -/
lemma forced_low_iterates (h1 : 1 < lam) (h2 : lam < 2) (hphi : lam ^ 2 < lam + 1)
    (b : ℕ → Bool) {x : ℝ} {n : ℕ} (hmiss : ∀ m, n ≤ m → (bitState lam b x m).1 ∉ Window lam)
    (hle : (bitState lam b x n).1 ≤ g lam) (i : ℕ) :
    (bitState lam b x (n + i)).1 = lam ^ i * (bitState lam b x n).1 ∧
      (bitState lam b x (n + i)).1 ≤ g lam := by
  induction i with
  | zero => simpa using hle
  | succ i ih =>
      obtain ⟨heq, hg⟩ := ih
      have hb : bitBranch lam b (bitState lam b x (n + i)) = 0 := by
        unfold bitBranch
        rw [if_neg (hmiss (n + i) (by omega))]
        exact cb_of_le_g h1 h2 hg
      have hstep : (bitState lam b x (n + i + 1)).1 = lam * (bitState lam b x (n + i)).1 := by
        rw [bitState_fst_succ, hb]; simp
      have hlt : (bitState lam b x (n + i + 1)).1 < r lam := by
        rw [hstep]; exact no_jump_low h1 hphi hg
      have hnw := hmiss (n + i + 1) (by omega)
      refine ⟨?_, ?_⟩
      · rw [show n + (i + 1) = n + i + 1 from rfl, hstep, heq]; ring
      · rw [show n + (i + 1) = n + i + 1 from rfl]
        by_contra hcon
        exact hnw (mem_Window.mpr ⟨not_le.mp hcon, hlt⟩)

/-- While the forced dynamics from `[r, 1)` misses the window it stays in
`[r, 1)`, and its distance to `1` is multiplied by `lam` at each step. -/
lemma forced_high_iterates (h1 : 1 < lam) (h2 : lam < 2) (hphi : lam ^ 2 < lam + 1)
    (b : ℕ → Bool) {x : ℝ} {n : ℕ} (hmiss : ∀ m, n ≤ m → (bitState lam b x m).1 ∉ Window lam)
    (hge : r lam ≤ (bitState lam b x n).1) (i : ℕ) :
    1 - (bitState lam b x (n + i)).1 = lam ^ i * (1 - (bitState lam b x n).1) ∧
      r lam ≤ (bitState lam b x (n + i)).1 := by
  induction i with
  | zero => simpa using hge
  | succ i ih =>
      obtain ⟨heq, hr⟩ := ih
      have hb : bitBranch lam b (bitState lam b x (n + i)) = 1 := by
        unfold bitBranch
        rw [if_neg (hmiss (n + i) (by omega))]
        exact cb_of_r_le h1 h2 hr
      have hstep : (bitState lam b x (n + i + 1)).1
          = lam * (bitState lam b x (n + i)).1 - (lam - 1) := by
        rw [bitState_fst_succ, hb]; simp
      have hgt : g lam < (bitState lam b x (n + i + 1)).1 := by
        rw [hstep]; exact no_jump_high h1 hphi hr
      have hnw := hmiss (n + i + 1) (by omega)
      refine ⟨?_, ?_⟩
      · rw [show n + (i + 1) = n + i + 1 from rfl, hstep, pow_succ]
        linear_combination lam * heq
      · rw [show n + (i + 1) = n + i + 1 from rfl]
        by_contra hcon
        exact hnw (mem_Window.mpr ⟨hgt, not_le.mp hcon⟩)

/-- **The window is visited at arbitrarily late times.** -/
lemma exists_window_ge (h1 : 1 < lam) (h2 : lam < 2) (hphi : lam ^ 2 < lam + 1)
    (b : ℕ → Bool) {x : ℝ} (hx : x ∈ Set.Ioo (0:ℝ) 1) (n : ℕ) :
    ∃ m, n ≤ m ∧ (bitState lam b x m).1 ∈ Window lam := by
  by_contra hcon
  push_neg at hcon
  have hmiss : ∀ m, n ≤ m → (bitState lam b x m).1 ∉ Window lam := fun m hm => hcon m hm
  have hy := bitState_mem_Ioo h1 h2 b hx n
  have hout : (bitState lam b x n).1 ≤ g lam ∨ r lam ≤ (bitState lam b x n).1 := by
    rcases lt_or_ge (g lam) (bitState lam b x n).1 with hgy | hgy
    · rcases lt_or_ge (bitState lam b x n).1 (r lam) with hyr | hyr
      · exact absurd (mem_Window.mpr ⟨hgy, hyr⟩) (hmiss n le_rfl)
      · exact Or.inr hyr
    · exact Or.inl hgy
  rcases hout with hlow | hhigh
  · refine not_forall_pow_mul_le h1 hy.1 (c := g lam) (fun i => ?_)
    obtain ⟨heq, hg⟩ := forced_low_iterates h1 h2 hphi b hmiss hlow i
    rw [← heq]; exact hg
  · refine not_forall_pow_mul_le h1 (y := 1 - (bitState lam b x n).1) (c := g lam)
      (by linarith [hy.2]) (fun i => ?_)
    obtain ⟨heq, hr⟩ := forced_high_iterates h1 h2 hphi b hmiss hhigh i
    have hgr : g lam + r lam = 1 := g_add_r lam
    rw [← heq]; linarith

/-- The bit index is non-decreasing. -/
lemma bitState_snd_mono (lam : ℝ) (b : ℕ → Bool) (x : ℝ) :
    Monotone (fun n => (bitState lam b x n).2) := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  simp only [bitState_snd_succ]
  split_ifs <;> omega

/-- The bit index is unbounded. -/
lemma bitState_snd_unbounded (h1 : 1 < lam) (h2 : lam < 2) (hphi : lam ^ 2 < lam + 1)
    (b : ℕ → Bool) {x : ℝ} (hx : x ∈ Set.Ioo (0:ℝ) 1) (k : ℕ) :
    ∃ n, k < (bitState lam b x n).2 := by
  induction k with
  | zero =>
      obtain ⟨m, _, hm⟩ := exists_window_ge h1 h2 hphi b hx 0
      refine ⟨m + 1, ?_⟩
      rw [bitState_snd_succ, if_pos hm]
      omega
  | succ k ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨m, hnm, hm⟩ := exists_window_ge h1 h2 hphi b hx n
      refine ⟨m + 1, ?_⟩
      have hmono : (bitState lam b x n).2 ≤ (bitState lam b x m).2 :=
        bitState_snd_mono lam b x hnm
      rw [bitState_snd_succ, if_pos hm]
      omega

/-- **Every bit index occurs at a window visit.** -/
lemma exists_window_index (h1 : 1 < lam) (h2 : lam < 2) (hphi : lam ^ 2 < lam + 1)
    (b : ℕ → Bool) {x : ℝ} (hx : x ∈ Set.Ioo (0:ℝ) 1) (k : ℕ) :
    ∃ n, (bitState lam b x n).1 ∈ Window lam ∧ (bitState lam b x n).2 = k := by
  have hex : ∃ n, k < (bitState lam b x n).2 := bitState_snd_unbounded h1 h2 hphi b hx k
  classical
  have hspec : k < (bitState lam b x (Nat.find hex)).2 := Nat.find_spec hex
  have hNpos : Nat.find hex ≠ 0 := by
    intro h
    rw [h] at hspec
    simp at hspec
  obtain ⟨p, hp⟩ : ∃ p, Nat.find hex = p + 1 := ⟨Nat.find hex - 1, by omega⟩
  rw [hp] at hspec
  have hmin : ¬ (k < (bitState lam b x p).2) := Nat.find_min hex (by omega)
  rw [bitState_snd_succ] at hspec
  have hwin : (bitState lam b x p).1 ∈ Window lam := by
    by_contra hcon
    rw [if_neg hcon] at hspec
    omega
  rw [if_pos hwin] at hspec
  exact ⟨p, hwin, by omega⟩

/-! ### Injectivity -/

/-- Equal itineraries force equal states. -/
lemma bitState_eq_of_theta_eq {b b' : ℕ → Bool} (heq : theta lam b = theta lam b') (n : ℕ) :
    bitState lam b (1/2) n = bitState lam b' (1/2) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hbr : bitBranch lam b (bitState lam b (1/2) n)
          = bitBranch lam b' (bitState lam b' (1/2) n) := congrFun heq n
      rw [bitState_succ, bitState_succ, hbr, ih]

/-- **T12a (continuum).**  For `1 < lam < 2` with `lam² < lam + 1`, the map
`theta lam` is an injection of the Cantor space into the itineraries of `1/2`,
and every itinerary in its image is a survival itinerary. -/
theorem theta_injective (h1 : 1 < lam) (h2 : lam < 2) (hphi : lam ^ 2 < lam + 1) :
    Function.Injective (theta lam) := by
  intro b b' heq
  funext k
  obtain ⟨n, hwin, hidx⟩ :=
    exists_window_index h1 h2 hphi b (by norm_num : (1/2 : ℝ) ∈ Set.Ioo (0:ℝ) 1) k
  have hst := bitState_eq_of_theta_eq heq n
  have h1' : theta lam b n = if b k then (1 : Fin 2) else 0 := by
    rw [theta, bitBranch, if_pos hwin, hidx]
  have h2' : theta lam b' n = if b' k then (1 : Fin 2) else 0 := by
    rw [theta, bitBranch, ← hst, if_pos hwin, hidx]
  have := h1'.symm.trans ((congrFun heq n).trans h2')
  revert this
  cases b k <;> cases b' k <;> simp

/-- **T12a, packaged.**  A continuum of survival itineraries of `1/2`. -/
theorem continuum_of_survival_itineraries (h1 : 1 < lam) (h2 : lam < 2)
    (hphi : lam ^ 2 < lam + 1) :
    ∃ Θ : (ℕ → Bool) → (ℕ → Fin 2),
      Function.Injective Θ ∧ ∀ b, Surviving lam (1/2) (Θ b) :=
  ⟨theta lam, theta_injective h1 h2 hphi, theta_surviving h1 h2⟩

end Branching
end KnotGame
