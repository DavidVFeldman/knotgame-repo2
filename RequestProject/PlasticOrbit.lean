import RequestProject.Plastic
import RequestProject.Gaps

/-!
# The effective bound at the plastic number (round 2, Target T7)

Round 1 reported the full Proposition 3.4 (the `25 525` reachable
configurations and `sup N = 7`) as infeasible for the kernel; see
`PLASTIC-REPORT.md`.  The *scheduling* route of round 2 needs strictly less: it
needs the `153`-point orbit of `1/2` and a lower bound for its smallest gap, and
that turns out to be within reach.  (Round 6 does certify the full proposition,
by a different route; see `PROP9-PLASTIC.md` and `PlasticConfig.lean`.  This
file remains the source of the orbit list everything there is built on.)

Every orbit point is of the form `(a + b*rho + c*rho^2)/2` with `a b c : ℤ`,
because `rho^3 = rho + 1` makes multiplication by `rho` an integral operation on
the coordinate triple:

  `rho * (a + b*rho + c*rho^2) = c + (a+c)*rho + b*rho^2`.

So the orbit is carried by an explicit list of `153` integer triples, and each
of the three finite verifications below is a computation on integers:

* `chk_range`   — every listed point lies in `(0,1)`;
* `chk_closed`  — the list is closed under the two branch maps, in the sense
  that an image which lies in `(0,1)` is again on the list;
* `chk_chain`   — the list is increasing with consecutive gaps at least
  `delta = 239/100000`.

Sign decisions are made through the certified rational enclosure
`1324717957/10^9 ≤ rho ≤ 1324717958/10^9`, turned into integer arithmetic by
`Mn` (an approximate value scaled by `10^18`) and `En` (a rigorous error bound).

Finally `rho ^ 22 = 86 + 151*rho + 114*rho^2` (an exact consequence of
`rho^3 = rho+1`) gives `rho ^ 22 * delta ≥ 1`, so the window `W = 22` satisfies
the hypothesis of `KnotGame.N_le_of_separated` and

  `N rho n ≤ 22 + ⌈22/2⌉ + 1 = 34`.

The true value is `7`; `34` is the effective bound the gap argument yields, and
is what this file proves.  The exact value is `Plastic.sup_N_rho`, in
`PlasticConfig.lean`.
-/

namespace KnotGame
namespace Plastic

set_option maxRecDepth 100000

/-! ### A tight rational enclosure of the plastic number -/

/-- `1324717957/10^9 ≤ rho`. -/
lemma rho_lb : (1324717957 : ℝ) ≤ 1000000000 * rho := by
  by_contra hc
  push_neg at hc
  have h1 : rho < 1324717957 / 1000000000 := by linarith
  have h3 := rho_gt
  have hpos : (0:ℝ) < (1324717957 / 1000000000) ^ 2
      + (1324717957 / 1000000000) * rho + rho ^ 2 - 1 := by nlinarith
  have hmono : rho ^ 3 - rho - 1
      < (1324717957 / 1000000000 : ℝ) ^ 3 - (1324717957 / 1000000000) - 1 := by
    nlinarith [mul_pos (sub_pos.mpr h1) hpos]
  have hq : (1324717957 / 1000000000 : ℝ) ^ 3 - (1324717957 / 1000000000) - 1 < 0 := by
    norm_num
  linarith [rho_cubic]

/-- `rho ≤ 1324717958/10^9`. -/
lemma rho_ub : (1000000000 : ℝ) * rho ≤ 1324717958 := by
  by_contra hc
  push_neg at hc
  have h1 : (1324717958 / 1000000000 : ℝ) < rho := by linarith
  have h3 := rho_gt
  have hpos : (0:ℝ) < (1324717958 / 1000000000) ^ 2
      + (1324717958 / 1000000000) * rho + rho ^ 2 - 1 := by nlinarith
  have hmono : (1324717958 / 1000000000 : ℝ) ^ 3 - (1324717958 / 1000000000) - 1
      < rho ^ 3 - rho - 1 := by
    nlinarith [mul_pos (sub_pos.mpr h1) hpos]
  have hq : (0:ℝ) < (1324717958 / 1000000000 : ℝ) ^ 3 - (1324717958 / 1000000000) - 1 := by
    norm_num
  linarith [rho_cubic]

/-! ### Orbit points as integer triples -/

/-- An element of `ℚ(rho)` with denominator `2`, stored as the triple of
integer coordinates `(a, b, c)` of `(a + b*rho + c*rho^2)/2`. -/
abbrev Tri := ℤ × ℤ × ℤ

/-- The numerator `a + b*rho + c*rho^2` of a triple. -/
noncomputable def traw (t : Tri) : ℝ :=
  (t.1 : ℝ) + (t.2.1 : ℝ) * rho + (t.2.2 : ℝ) * rho ^ 2

/-- The real number `(a + b*rho + c*rho^2)/2` represented by a triple. -/
noncomputable def tval (t : Tri) : ℝ := traw t / 2

/-- The lower branch map `x ↦ rho * x` in coordinates. -/
def tf0 (t : Tri) : Tri := (t.2.2, t.1 + t.2.2, t.2.1)

/-- The upper branch map `x ↦ rho * x - (rho - 1)` in coordinates. -/
def tf1 (t : Tri) : Tri := (t.2.2 + 2, t.1 + t.2.2 - 2, t.2.1)

lemma rho_cube : rho ^ 3 = rho + 1 := by linarith [rho_cubic]

lemma tval_tf0 (t : Tri) : tval (tf0 t) = rho * tval t := by
  simp only [tval, traw, tf0]
  push_cast
  linear_combination (-(t.2.2 : ℝ) / 2) * rho_cube

lemma tval_tf1 (t : Tri) : tval (tf1 t) = rho * tval t - (rho - 1) := by
  simp only [tval, traw, tf1]
  push_cast
  linear_combination (-(t.2.2 : ℝ) / 2) * rho_cube

/-! ### Certified integer enclosure of `10^18 * traw` -/

/-- The scaled approximate value `10^18 * (a + b*rho + c*rho^2)` computed with
`rho ≈ 1324717957/10^9`. -/
def Mn (t : Tri) : ℤ :=
  t.1 * 1000000000000000000 + t.2.1 * 1324717957000000000 + t.2.2 * 1754877665598253849

/-- A rigorous bound for the error committed by `Mn`. -/
def En (t : Tri) : ℤ := |t.2.1| * 1000000000 + |t.2.2| * 2649435915

lemma En_nonneg (t : Tri) : 0 ≤ En t := by
  have h1 : (0:ℤ) ≤ |t.2.1| := abs_nonneg _
  have h2 : (0:ℤ) ≤ |t.2.2| := abs_nonneg _
  simp only [En]
  positivity

/-- The enclosure: `10^18 * traw t` differs from `Mn t` by at most `En t`. -/
lemma abs_traw_sub_Mn (t : Tri) :
    |(1000000000000000000 : ℝ) * traw t - (Mn t : ℝ)| ≤ (En t : ℝ) := by
  have hr0 : (0:ℝ) < rho := lt_trans zero_lt_one one_lt_rho
  have hsq1 : (1324717957 : ℝ) * 1324717957 ≤ (1000000000 * rho) * (1000000000 * rho) :=
    mul_self_le_mul_self (by norm_num) rho_lb
  have hsq2 : (1000000000 * rho) * (1000000000 * rho) ≤ (1324717958 : ℝ) * 1324717958 :=
    mul_self_le_mul_self (by positivity) rho_ub
  have h1 : (0:ℝ) ≤ 1000000000000000000 * rho - 1324717957000000000 := by nlinarith [rho_lb]
  have h2 : (1000000000000000000 : ℝ) * rho - 1324717957000000000 ≤ 1000000000 := by
    nlinarith [rho_ub]
  have h3 : (0:ℝ) ≤ 1000000000000000000 * rho ^ 2 - 1754877665598253849 := by nlinarith
  have h4 : (1000000000000000000 : ℝ) * rho ^ 2 - 1754877665598253849 ≤ 2649435915 := by
    nlinarith
  have key : (1000000000000000000 : ℝ) * traw t - (Mn t : ℝ)
      = (t.2.1 : ℝ) * (1000000000000000000 * rho - 1324717957000000000)
        + (t.2.2 : ℝ) * (1000000000000000000 * rho ^ 2 - 1754877665598253849) := by
    simp only [traw, Mn]
    push_cast
    ring
  rw [key]
  refine le_trans (abs_add_le _ _) ?_
  rw [abs_mul, abs_mul, abs_of_nonneg h1, abs_of_nonneg h3]
  have e1 : |(t.2.1 : ℝ)| * ((1000000000000000000 : ℝ) * rho - 1324717957000000000)
      ≤ |(t.2.1 : ℝ)| * 1000000000 := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  have e2 : |(t.2.2 : ℝ)| * ((1000000000000000000 : ℝ) * rho ^ 2 - 1754877665598253849)
      ≤ |(t.2.2 : ℝ)| * 2649435915 := mul_le_mul_of_nonneg_left h4 (abs_nonneg _)
  have : ((En t : ℤ) : ℝ) = |(t.2.1 : ℝ)| * 1000000000 + |(t.2.2 : ℝ)| * 2649435915 := by
    simp only [En]
    push_cast
    ring
  rw [this]
  linarith

lemma Mn_sub_En_le (t : Tri) :
    ((Mn t - En t : ℤ) : ℝ) ≤ (1000000000000000000 : ℝ) * traw t := by
  have := (abs_le.mp (abs_traw_sub_Mn t)).1
  push_cast
  linarith

lemma le_Mn_add_En (t : Tri) :
    (1000000000000000000 : ℝ) * traw t ≤ ((Mn t + En t : ℤ) : ℝ) := by
  have := (abs_le.mp (abs_traw_sub_Mn t)).2
  push_cast
  linarith

lemma tval_pos_of {t : Tri} (h : 0 < Mn t - En t) : 0 < tval t := by
  have h1 := Mn_sub_En_le t
  have h2 : (0:ℝ) < ((Mn t - En t : ℤ) : ℝ) := by exact_mod_cast h
  have : (0:ℝ) < 1000000000000000000 * traw t := lt_of_lt_of_le h2 h1
  simp only [tval]
  linarith

lemma tval_lt_one_of {t : Tri} (h : Mn t + En t < 2000000000000000000) : tval t < 1 := by
  have h1 := le_Mn_add_En t
  have h2 : ((Mn t + En t : ℤ) : ℝ) < 2000000000000000000 := by exact_mod_cast h
  have : (1000000000000000000 : ℝ) * traw t < 2000000000000000000 := lt_of_le_of_lt h1 h2
  simp only [tval]
  linarith

lemma tval_nonpos_of {t : Tri} (h : Mn t + En t ≤ 0) : tval t ≤ 0 := by
  have h1 := le_Mn_add_En t
  have h2 : ((Mn t + En t : ℤ) : ℝ) ≤ 0 := by exact_mod_cast h
  have : (1000000000000000000 : ℝ) * traw t ≤ 0 := le_trans h1 h2
  simp only [tval]
  linarith

lemma one_le_tval_of {t : Tri} (h : 2000000000000000000 ≤ Mn t - En t) : 1 ≤ tval t := by
  have h1 := Mn_sub_En_le t
  have h2 : (2000000000000000000 : ℝ) ≤ ((Mn t - En t : ℤ) : ℝ) := by exact_mod_cast h
  have : (2000000000000000000 : ℝ) ≤ 1000000000000000000 * traw t := le_trans h2 h1
  simp only [tval]
  linarith

/-! ### The orbit list and its three finite verifications -/

/-- The `153` points of the orbit of `1/2` at the plastic number, in increasing
order, given by their coordinates over `ℤ[rho]` with denominator `2`. -/
def orbitList : List Tri :=
  [
    (4, (-3), 0), (0, 4, (-3)), ((-3), (-3), 4), (4, 1, (-3)),
    (1, (-6), 4), ((-3), 1, 1), (8, (-2), (-3)), (4, 5, (-6)),
    (1, (-2), 1), ((-3), 5, (-2)), ((-6), (-2), 5), (5, (-5), 1),
    (1, 2, (-2)), ((-2), (-5), 5), (5, (-1), (-2)), (1, 6, (-5)),
    ((-2), (-1), 2), (5, 3, (-5)), ((-2), 3, (-1)), ((-5), (-4), 6),
    (2, 0, (-1)), ((-5), 0, 3), (6, (-3), (-1)), ((-1), (-3), 3),
    (6, 1, (-4)), (3, (-6), 3), ((-1), 1, 0), (3, (-2), 0),
    ((-1), 5, (-3)), (3, 2, (-3)), (0, (-5), 4), ((-4), 2, 1),
    (7, (-1), (-3)), (3, 6, (-6)), (0, (-1), 1), (7, 3, (-6)),
    (4, (-4), 1), (0, 3, (-2)), ((-3), (-4), 5), ((-3), 0, 2),
    (4, 4, (-5)), (1, (-3), 2), ((-3), 4, (-1)), (8, 1, (-5)),
    ((-6), (-3), 6), (1, 1, (-1)), ((-6), 1, 3), (5, (-2), (-1)),
    (1, 5, (-4)), ((-2), (-2), 3), (5, 2, (-4)), (2, (-5), 3),
    (2, (-1), 0), ((-5), (-1), 4), (2, 3, (-3)), ((-1), (-4), 4),
    ((-5), 3, 1), (6, 0, (-3)), ((-1), 0, 1), (3, (-3), 1),
    ((-1), 4, (-2)), ((-4), (-3), 5), (3, 1, (-2)), (0, (-6), 5),
    ((-4), 1, 2), (7, (-2), (-2)), (3, 5, (-5)), (7, 2, (-5)),
    (4, (-5), 2), (0, 2, (-1)), ((-3), (-5), 6), (4, (-1), (-1)),
    ((-3), (-1), 3), (4, 3, (-4)), (1, (-4), 3), ((-3), 3, 0),
    (1, 0, 0), (5, (-3), 0), (1, 4, (-3)), ((-2), (-3), 4),
    (5, 1, (-3)), ((-2), 1, 1), (5, 5, (-6)), (2, (-2), 1),
    ((-2), 5, (-2)), ((-5), (-2), 5), ((-1), (-5), 5), ((-5), 2, 2),
    (6, (-1), (-2)), (2, 6, (-5)), ((-1), (-1), 2), (6, 3, (-5)),
    (3, (-4), 2), ((-1), 3, (-1)), (3, 0, (-1)), ((-4), 0, 3),
    (7, (-3), (-1)), (3, 4, (-4)), (0, (-3), 3), (7, 1, (-4)),
    (0, 1, 0), (0, 5, (-3)), ((-3), (-2), 4), (4, 2, (-3)),
    (1, (-5), 4), ((-3), 2, 1), (8, (-1), (-3)), (1, (-1), 1),
    (8, 3, (-6)), ((-6), (-1), 5), (5, (-4), 1), (1, 3, (-2)),
    ((-2), (-4), 5), (5, 0, (-2)), (5, 4, (-5)), (2, (-3), 2),
    ((-2), 4, (-1)), ((-5), (-3), 6), (2, 1, (-1)), ((-1), (-6), 6),
    ((-5), 1, 3), (6, (-2), (-1)), (2, 5, (-4)), ((-1), (-2), 3),
    (3, (-5), 3), ((-1), 2, 0), (3, (-1), 0), ((-1), 6, (-3)),
    ((-4), (-1), 4), (3, 3, (-3)), ((-4), 3, 1), (7, 0, (-3)),
    (0, 0, 1), (7, 4, (-6)), (4, (-3), 1), ((-3), (-3), 5),
    (4, 1, (-2)), (1, (-6), 5), ((-3), 1, 2), (4, 5, (-5)),
    (1, (-2), 2), ((-3), 5, (-1)), (8, 2, (-5)), (5, (-5), 2),
    (1, 2, (-1)), ((-2), (-5), 6), ((-6), 2, 3), (5, (-1), (-1)),
    (1, 6, (-4)), ((-2), (-1), 3), (5, 3, (-4)), (2, (-4), 3),
    ((-2), 3, 0)
  ]

/-- The image of a listed point either stays on the list or leaves `(0,1)`. -/
def okP (u : Tri) : Prop :=
  u ∈ orbitList ∨ Mn u + En u ≤ 0 ∨ 2000000000000000000 ≤ Mn u - En u

instance (u : Tri) : Decidable (okP u) := by unfold okP; infer_instance

/-- The integer certificate that two consecutive listed points are at least
`239/100000` apart. -/
def gapP (u v : Tri) : Prop :=
  478000000000000000000 ≤ 100000 * ((Mn v - En v) - (Mn u + En u))

instance : DecidableRel gapP := fun u v => by unfold gapP; infer_instance

theorem orbitList_length : orbitList.length = 153 := by decide

theorem chk_range : ∀ t ∈ orbitList, 0 < Mn t - En t ∧ Mn t + En t < 2000000000000000000 := by
  decide

theorem chk_closed : ∀ t ∈ orbitList, okP (tf0 t) ∧ okP (tf1 t) := by decide

theorem chk_chain : List.IsChain gapP orbitList := by decide

theorem half_mem_orbitList : ((1 : ℤ), (0 : ℤ), (0 : ℤ)) ∈ orbitList := by decide

/-! ### The separation constant -/

/-- The certified lower bound for the smallest gap of the plastic orbit
(the true value is about `0.0023912`). -/
noncomputable def deltaRho : ℝ := 239 / 100000

lemma deltaRho_pos : 0 < deltaRho := by norm_num [deltaRho]

lemma gapP_sound {u v : Tri} (h : gapP u v) : tval u + deltaRho ≤ tval v := by
  have h1 := le_Mn_add_En u
  have h2 := Mn_sub_En_le v
  have h3 : (478000000000000000000 : ℝ)
      ≤ 100000 * (((Mn v - En v : ℤ) : ℝ) - ((Mn u + En u : ℤ) : ℝ)) := by
    have : ((478000000000000000000 : ℤ) : ℝ)
        ≤ ((100000 * ((Mn v - En v) - (Mn u + En u)) : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at this ⊢
    linarith
  simp only [tval, deltaRho]
  linarith

/-- The separation relation on triples used for the pairwise bound. -/
def Sep (u v : Tri) : Prop := tval u + deltaRho ≤ tval v

instance : Trans Sep Sep Sep :=
  ⟨fun h₁ h₂ => by
    simp only [Sep] at *
    have := deltaRho_pos
    linarith⟩

theorem orbitList_pairwise :
    List.Pairwise (fun u v : Tri => deltaRho ≤ |tval u - tval v|) orbitList := by
  have hchain : List.IsChain Sep orbitList :=
    chk_chain.imp (fun {u v} h => gapP_sound h)
  have hpw : List.Pairwise Sep orbitList := List.isChain_iff_pairwise.mp hchain
  refine hpw.imp ?_
  intro u v h
  simp only [Sep] at h
  have hd := deltaRho_pos
  rw [abs_sub_comm, abs_of_nonneg (by linarith : (0:ℝ) ≤ tval v - tval u)]
  linarith

/-! ### The orbit is contained in the listed set -/

/-- The set of real numbers carried by `orbitList`. -/
def OrbSet : Set ℝ := {x : ℝ | ∃ t ∈ orbitList, tval t = x}

lemma half_mem_OrbSet : (1/2 : ℝ) ∈ OrbSet := by
  refine ⟨(1, 0, 0), half_mem_orbitList, ?_⟩
  simp [tval, traw]

lemma OrbSet_subset_Ioo : ∀ x ∈ OrbSet, x ∈ Set.Ioo (0:ℝ) 1 := by
  rintro x ⟨t, ht, rfl⟩
  obtain ⟨h1, h2⟩ := chk_range t ht
  exact ⟨tval_pos_of h1, tval_lt_one_of h2⟩

lemma OrbSet_closed :
    ∀ x ∈ OrbSet, ∀ m : Move, survives rho m x → act rho m x ∈ OrbSet := by
  rintro x ⟨t, ht, rfl⟩ m hm
  have hIoo : act rho m (tval t) ∈ Set.Ioo (0:ℝ) 1 :=
    act_mem_Ioo one_lt_rho (OrbSet_subset_Ioo _ ⟨t, ht, rfl⟩) hm
  have halt : act rho m (tval t) = tval (tf0 t) ∨ act rho m (tval t) = tval (tf1 t) := by
    unfold act
    rcases Fin.exists_fin_two.mp ⟨branch rho m (tval t), rfl⟩ with hb | hb
    · left; rw [hb, f_zero, tval_tf0]
    · right; rw [hb, f_one, tval_tf1]
  obtain ⟨hc0, hc1⟩ := chk_closed t ht
  rcases halt with hz | hz
  · rcases hc0 with hmem | hle | hge
    · exact ⟨tf0 t, hmem, hz.symm⟩
    · exact absurd (hz ▸ hIoo.1) (not_lt.mpr (tval_nonpos_of hle))
    · exact absurd (hz ▸ hIoo.2) (not_lt.mpr (one_le_tval_of hge))
  · rcases hc1 with hmem | hle | hge
    · exact ⟨tf1 t, hmem, hz.symm⟩
    · exact absurd (hz ▸ hIoo.1) (not_lt.mpr (tval_nonpos_of hle))
    · exact absurd (hz ▸ hIoo.2) (not_lt.mpr (one_le_tval_of hge))

/-- Every knot of every reachable configuration at the plastic number lies on
the `153`-point orbit list. -/
theorem run_subset_OrbSet (w : List Move) : ∀ y ∈ run rho w, y ∈ OrbSet :=
  run_subset OrbSet half_mem_OrbSet OrbSet_closed w

/-- Two distinct coexisting knots at the plastic number are at distance at
least `239/100000`. -/
theorem run_sep (w : List Move) :
    ∀ x ∈ run rho w, ∀ y ∈ run rho w, x ≠ y → deltaRho ≤ |x - y| := by
  intro x hx y hy hxy
  obtain ⟨t, ht, rfl⟩ := run_subset_OrbSet w x hx
  obtain ⟨s, hs, rfl⟩ := run_subset_OrbSet w y hy
  have hts : t ≠ s := fun hc => hxy (by rw [hc])
  exact orbitList_pairwise.forall (fun a b hab => by rwa [abs_sub_comm]) ht hs hts

/-! ### The window `W = 22` -/

/-- `rho ^ 22 = 86 + 151*rho + 114*rho^2`, an exact consequence of
`rho ^ 3 = rho + 1`. -/
lemma rho_pow_22 : rho ^ 22 = 86 + 151 * rho + 114 * rho ^ 2 := by
  linear_combination (rho ^ 19 + rho ^ 17 + rho ^ 16 + rho ^ 15 + 2 * rho ^ 14 + 2 * rho ^ 13
    + 3 * rho ^ 12 + 4 * rho ^ 11 + 5 * rho ^ 10 + 7 * rho ^ 9 + 9 * rho ^ 8 + 12 * rho ^ 7
    + 16 * rho ^ 6 + 21 * rho ^ 5 + 28 * rho ^ 4 + 37 * rho ^ 3 + 49 * rho ^ 2 + 65 * rho
    + 86) * rho_cube

/-- The window hypothesis of the scheduling theorem at `W = 22`. -/
lemma window_bound_rho : 1 ≤ rho ^ 22 * deltaRho := by
  rw [rho_pow_22, deltaRho]
  nlinarith [rho_lb, rho_gt]

/-- **T7 (plastic number, effective bound).**  At `lam = rho` the scheduling
theorem with `delta = 239/100000` and `W = 22` gives `N rho n ≤ 34` for
every `n`. -/
theorem N_rho_le_34 (n : ℕ) : N rho n ≤ 34 := by
  have := N_le_of_separated (lam := rho) one_lt_rho (delta := deltaRho) 22
    window_bound_rho run_sep n
  norm_num at this
  exact this

/-- The effective bound in run form: every run at the plastic number has at
most `34` simultaneous knots. -/
theorem card_run_rho_le_34 (w : List Move) : (run rho w).card ≤ 34 := by
  have := scheduling_bound (lam := rho) one_lt_rho (delta := deltaRho) 22
    window_bound_rho w (fun u _ _ => run_sep u)
  norm_num at this
  exact this

end Plastic
end KnotGame
