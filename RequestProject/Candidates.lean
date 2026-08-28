import RequestProject.SurvivorSet

/-!
# T20 — the candidate-cell identity (paper Remark `rem:candidates`)

A *candidate* for a word `w` is an intended itinerary through `w`: at each `M`
of `w`, a declaration of which branch the entering point will take (`false` for
the lower branch, i.e. the point stays below `r/2`, `true` for the upper one).
`FollowsItin lam w t x` says that `x` survives `w` and realises the itinerary
`t`.

* `followsItin_partition` — the general lemma: the candidate cells partition the
  survivor set `S(w)`; every `x ∈ (0,1)` surviving `w` realises exactly one
  itinerary, of length `countM w`.
* `followsItin_eq_Ioo` — at `λ = 3/2` each cell is the open interval computed by
  the exact integer recursion `cellZ` (endpoints over the denominator
  `2·3^{|w|}`), so in particular it is empty exactly when the computed
  endpoints are out of order.
* `candidate_count`, `candidate_total_length` — the instance of the remark: for
  the `19`-move run `w = MLMLMMMMMLMRLRMLMLM` attaining five knots at
  `λ = 3/2` there are `2^11 = 2048` candidates, of which exactly six are
  nonempty, and their lengths sum to exactly `(2/3)^19 = 524288/1162261467`.
  The two finite facts are decided by the kernel on exact integer arithmetic.
-/

namespace KnotGame

/-! ## Candidates in general -/

/-- `FollowsItin lam w t x`: the point `x` runs through the word `w` following
the itinerary `t` — one Boolean per `M` of `w`, `false` for the lower branch
(`x < r/2`) and `true` for the upper one (`1 - r/2 < x`) — and ends inside
`(0,1)`. -/
def FollowsItin (lam : ℝ) : List Move → List Bool → ℝ → Prop
  | [], [], x => 0 < x ∧ x < 1
  | [], _ :: _, _ => False
  | Move.L :: v, t, x => g lam < x ∧ FollowsItin lam v t (act lam Move.L x)
  | Move.R :: v, t, x => x < r lam ∧ FollowsItin lam v t (act lam Move.R x)
  | Move.M :: _, [], _ => False
  | Move.M :: v, b :: t, x =>
      (if b then 1 - r lam / 2 < x else x < r lam / 2) ∧
        FollowsItin lam v t (act lam Move.M x)

variable {lam : ℝ}

@[simp] lemma followsItin_nil_nil (x : ℝ) :
    FollowsItin lam [] [] x ↔ (0 < x ∧ x < 1) := Iff.rfl

@[simp] lemma followsItin_nil_cons (b : Bool) (t : List Bool) (x : ℝ) :
    ¬ FollowsItin lam [] (b :: t) x := id

@[simp] lemma followsItin_L (v : List Move) (t : List Bool) (x : ℝ) :
    FollowsItin lam (Move.L :: v) t x ↔
      (g lam < x ∧ FollowsItin lam v t (act lam Move.L x)) := Iff.rfl

@[simp] lemma followsItin_R (v : List Move) (t : List Bool) (x : ℝ) :
    FollowsItin lam (Move.R :: v) t x ↔
      (x < r lam ∧ FollowsItin lam v t (act lam Move.R x)) := Iff.rfl

@[simp] lemma followsItin_M_nil (v : List Move) (x : ℝ) :
    ¬ FollowsItin lam (Move.M :: v) [] x := id

@[simp] lemma followsItin_M_cons (v : List Move) (b : Bool) (t : List Bool) (x : ℝ) :
    FollowsItin lam (Move.M :: v) (b :: t) x ↔
      ((if b then 1 - r lam / 2 < x else x < r lam / 2) ∧
        FollowsItin lam v t (act lam Move.M x)) := Iff.rfl

/-- An itinerary has one letter per `M`. -/
lemma followsItin_length : ∀ (w : List Move) (t : List Bool) (x : ℝ),
    FollowsItin lam w t x → t.length = countM w
  | [], [], _, _ => by simp [countM]
  | [], _ :: _, _, hf => absurd hf (by simp)
  | Move.L :: v, t, x, hf => by
      rw [countM_cons]; simpa using followsItin_length v t _ hf.2
  | Move.R :: v, t, x, hf => by
      rw [countM_cons]; simpa using followsItin_length v t _ hf.2
  | Move.M :: _, [], _, hf => absurd hf (by simp)
  | Move.M :: v, b :: t, x, hf => by
      rw [countM_cons, if_pos rfl, ← followsItin_length v t _ hf.2]
      simp

/-- Following an itinerary through `w` is in particular surviving `w`. -/
lemma survivesWord_of_followsItin : ∀ (w : List Move) (t : List Bool) (x : ℝ),
    FollowsItin lam w t x → survivesWord lam x w
  | [], _, _, _ => trivial
  | Move.L :: v, t, x, hf =>
      ⟨hf.1, survivesWord_of_followsItin v t _ hf.2⟩
  | Move.R :: v, t, x, hf =>
      ⟨hf.1, survivesWord_of_followsItin v t _ hf.2⟩
  | Move.M :: _, [], _, hf => absurd hf (by simp)
  | Move.M :: v, b :: t, x, hf => by
      refine ⟨?_, survivesWord_of_followsItin v t _ hf.2⟩
      have h1 := hf.1
      cases b with
      | false => exact Or.inl (by simpa using h1)
      | true => exact Or.inr (by simpa using h1)

/-- A point following an itinerary lies in `(0,1)`. -/
lemma mem_Ioo_of_followsItin (h : 1 < lam) : ∀ (w : List Move) (t : List Bool) (x : ℝ),
    FollowsItin lam w t x → 0 < x ∧ x < 1
  | [], [], _, hf => hf
  | [], _ :: _, _, hf => absurd hf (by simp)
  | Move.L :: v, t, x, hf => by
      have hlam : (0:ℝ) < lam := lt_trans zero_lt_one h
      have hr1 : r lam < 1 := r_lt_one lam h
      have h0 : g lam < x := hf.1
      obtain ⟨ha0, ha1⟩ := mem_Ioo_of_followsItin h v t _ hf.2
      rw [act_L] at ha0 ha1
      refine ⟨?_, ?_⟩
      · have : (0:ℝ) < g lam := g_pos lam h
        linarith
      · nlinarith
  | Move.R :: v, t, x, hf => by
      have hlam : (0:ℝ) < lam := lt_trans zero_lt_one h
      have hr1 : r lam < 1 := r_lt_one lam h
      have h0 : x < r lam := hf.1
      obtain ⟨ha0, ha1⟩ := mem_Ioo_of_followsItin h v t _ hf.2
      rw [act_R] at ha0 ha1
      exact ⟨by nlinarith, by linarith⟩
  | Move.M :: _, [], _, hf => absurd hf (by simp)
  | Move.M :: v, b :: t, x, hf => by
      have hlam : (0:ℝ) < lam := lt_trans zero_lt_one h
      have hr0 : 0 < r lam := r_pos lam h
      have hr1 : r lam < 1 := r_lt_one lam h
      obtain ⟨ha0, ha1⟩ := mem_Ioo_of_followsItin h v t _ hf.2
      have h1 := hf.1
      cases b with
      | false =>
          have hx : x < r lam / 2 := by simpa using h1
          rw [act_M_of_lt lam x hx] at ha0 ha1
          exact ⟨by nlinarith, by linarith⟩
      | true =>
          have hx : 1 - r lam / 2 < x := by simpa using h1
          rw [act_M_of_gt lam x (by push_neg; linarith)] at ha0 ha1
          exact ⟨by linarith, by nlinarith⟩

/-- Every survivor realises some itinerary. -/
lemma exists_followsItin (h : 1 < lam) : ∀ (w : List Move) (x : ℝ),
    0 < x → x < 1 → survivesWord lam x w → ∃ t, FollowsItin lam w t x
  | [], x, hx0, hx1, _ => ⟨[], hx0, hx1⟩
  | Move.L :: v, x, hx0, hx1, hs => by
      obtain ⟨hy0, hy1⟩ := act_mem_Ioo h ⟨hx0, hx1⟩ hs.1
      obtain ⟨t, ht⟩ := exists_followsItin h v _ hy0 hy1 hs.2
      exact ⟨t, hs.1, ht⟩
  | Move.R :: v, x, hx0, hx1, hs => by
      obtain ⟨hy0, hy1⟩ := act_mem_Ioo h ⟨hx0, hx1⟩ hs.1
      obtain ⟨t, ht⟩ := exists_followsItin h v _ hy0 hy1 hs.2
      exact ⟨t, hs.1, ht⟩
  | Move.M :: v, x, hx0, hx1, hs => by
      obtain ⟨hy0, hy1⟩ := act_mem_Ioo h ⟨hx0, hx1⟩ hs.1
      obtain ⟨t, ht⟩ := exists_followsItin h v _ hy0 hy1 hs.2
      rcases (show x < r lam / 2 ∨ 1 - r lam / 2 < x from hs.1) with hx | hx
      · exact ⟨false :: t, by simpa using ⟨hx, ht⟩⟩
      · exact ⟨true :: t, by simpa using ⟨hx, ht⟩⟩

/-- The itinerary realised by a point is unique: the candidate cells are
pairwise disjoint. -/
lemma followsItin_unique (h : 1 < lam) : ∀ (w : List Move) (t t' : List Bool) (x : ℝ),
    FollowsItin lam w t x → FollowsItin lam w t' x → t = t'
  | [], [], [], _, _, _ => rfl
  | [], [], _ :: _, _, _, hf' => absurd hf' (by simp)
  | [], _ :: _, _, _, hf, _ => absurd hf (by simp)
  | Move.L :: v, t, t', x, hf, hf' => followsItin_unique h v t t' _ hf.2 hf'.2
  | Move.R :: v, t, t', x, hf, hf' => followsItin_unique h v t t' _ hf.2 hf'.2
  | Move.M :: _, [], _, _, hf, _ => absurd hf (by simp)
  | Move.M :: _, _ :: _, [], _, _, hf' => absurd hf' (by simp)
  | Move.M :: v, b :: t, b' :: t', x, hf, hf' => by
      have hb : b = b' := by
        have hhalf := half_lt_one_sub_half h
        cases b with
        | false =>
            cases b' with
            | false => rfl
            | true =>
                exfalso
                have h1 : x < r lam / 2 := by simpa using hf.1
                have h2 : 1 - r lam / 2 < x := by simpa using hf'.1
                linarith
        | true =>
            cases b' with
            | false =>
                exfalso
                have h1 : 1 - r lam / 2 < x := by simpa using hf.1
                have h2 : x < r lam / 2 := by simpa using hf'.1
                linarith
            | true => rfl
      subst hb
      rw [followsItin_unique h v t t' _ hf.2 hf'.2]

/-- **T20, the general lemma** (paper Remark `rem:candidates`).  The candidate
cells partition the survivor set: a point of `(0,1)` survives `w` exactly when
it realises one — and then exactly one — itinerary through `w`. -/
theorem followsItin_partition (h : 1 < lam) (w : List Move) (x : ℝ) :
    (0 < x ∧ x < 1 ∧ survivesWord lam x w) ↔ ∃! t, FollowsItin lam w t x := by
  constructor
  · rintro ⟨hx0, hx1, hs⟩
    obtain ⟨t, ht⟩ := exists_followsItin h w x hx0 hx1 hs
    exact ⟨t, ht, fun t' ht' => followsItin_unique h w t' t x ht' ht⟩
  · rintro ⟨t, ht, -⟩
    obtain ⟨hx0, hx1⟩ := mem_Ioo_of_followsItin h w t x ht
    exact ⟨hx0, hx1, survivesWord_of_followsItin w t x ht⟩


/-! ## The cells at `λ = 3/2`, in exact integer arithmetic

At `λ = 3/2` one has `r = 2/3`, `g = 1/3`, and the three branch maps are
`x ↦ (3/2)x` and `x ↦ (3/2)x - 1/2`.  Pulling the target interval `(0,1)` back
through the word therefore keeps all endpoints in `(1/(2·3^k))ℤ`, and the whole
computation can be carried out in `ℤ`.  `cellZ w t` returns the two endpoints
of the candidate cell of `w` and `t` over the common denominator `2·3^{|w|}`;
the cell is empty exactly when the endpoints are out of order. -/

/-- The candidate cell of `w` and `t` at `λ = 3/2`, as a pair of integers over
the denominator `2·3^{|w|}`. -/
def cellZ : List Move → List Bool → ℤ × ℤ
  | [], [] => (0, 2)
  | [], _ :: _ => (0, 0)
  | Move.L :: v, t =>
      (2 * (cellZ v t).1 + 2 * 3 ^ v.length, 2 * (cellZ v t).2 + 2 * 3 ^ v.length)
  | Move.R :: v, t => (2 * (cellZ v t).1, 2 * (cellZ v t).2)
  | Move.M :: _, [] => (0, 0)
  | Move.M :: v, false :: t => (2 * (cellZ v t).1, 2 * min (cellZ v t).2 (3 ^ v.length))
  | Move.M :: v, true :: t =>
      (2 * max (cellZ v t).1 (3 ^ v.length) + 2 * 3 ^ v.length,
        2 * (cellZ v t).2 + 2 * 3 ^ v.length)

lemma cellZ_bounds : ∀ (w : List Move) (t : List Bool),
    0 ≤ (cellZ w t).1 ∧ (cellZ w t).2 ≤ 2 * 3 ^ w.length
  | [], [] => by norm_num [cellZ]
  | [], _ :: _ => by norm_num [cellZ]
  | Move.L :: v, t => by
      obtain ⟨h1, h2⟩ := cellZ_bounds v t
      have he : (0:ℤ) < 3 ^ v.length := pow_pos (by norm_num) _
      simp only [cellZ, List.length_cons, pow_succ]
      omega
  | Move.R :: v, t => by
      obtain ⟨h1, h2⟩ := cellZ_bounds v t
      have he : (0:ℤ) < 3 ^ v.length := pow_pos (by norm_num) _
      simp only [cellZ, List.length_cons, pow_succ]
      omega
  | Move.M :: v, [] => by
      have he : (0:ℤ) < 3 ^ v.length := pow_pos (by norm_num) _
      simp only [cellZ, List.length_cons, pow_succ]
      omega
  | Move.M :: v, false :: t => by
      obtain ⟨h1, h2⟩ := cellZ_bounds v t
      have he : (0:ℤ) < 3 ^ v.length := pow_pos (by norm_num) _
      simp only [cellZ, List.length_cons, pow_succ]
      omega
  | Move.M :: v, true :: t => by
      obtain ⟨h1, h2⟩ := cellZ_bounds v t
      have he : (0:ℤ) < 3 ^ v.length := pow_pos (by norm_num) _
      simp only [cellZ, List.length_cons, pow_succ]
      omega

lemma r_three_halves : r (3/2 : ℝ) = 2/3 := by norm_num [r]

lemma g_three_halves : g (3/2 : ℝ) = 1/3 := by norm_num [g, r]

/-- **The cells are the computed intervals.**  At `λ = 3/2`, a point realises
the itinerary `t` through `w` exactly when it lies strictly between the two
endpoints returned by `cellZ w t` (written here over the common denominator
`2·3^{|w|}`). -/
lemma followsItin_iff_cellZ : ∀ (w : List Move) (t : List Bool) (x : ℝ),
    FollowsItin (3/2) w t x ↔
      (((cellZ w t).1 : ℝ) < 2 * 3 ^ w.length * x ∧
        2 * 3 ^ w.length * x < ((cellZ w t).2 : ℝ))
  | [], [], x => by
      simp only [cellZ, followsItin_nil_nil, List.length_nil, pow_zero]
      norm_num
  | [], _ :: _, x => by
      simp only [cellZ, List.length_nil, pow_zero]
      norm_num
      intro h1
      linarith
  | Move.L :: v, t, x => by
      have he : (0:ℝ) < 3 ^ v.length := by positivity
      obtain ⟨hA, hB⟩ := cellZ_bounds v t
      have hA' : (0:ℝ) ≤ ((cellZ v t).1 : ℝ) := by exact_mod_cast hA
      have hB' : ((cellZ v t).2 : ℝ) ≤ 2 * 3 ^ v.length := by
        have : ((cellZ v t).2 : ℝ) ≤ ((2 * 3 ^ v.length : ℤ) : ℝ) := by exact_mod_cast hB
        push_cast at this; linarith
      have ih := followsItin_iff_cellZ v t (act (3/2:ℝ) Move.L x)
      rw [act_L] at ih
      rw [followsItin_L, g_three_halves, act_L, ih]
      simp only [cellZ, List.length_cons, pow_succ]
      push_cast
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨by linarith, by linarith⟩
      · rintro ⟨h1, h2⟩
        have hx : (1:ℝ)/3 < x := by
          have hmul : (3:ℝ) ^ v.length * 1 < 3 ^ v.length * (3 * x) := by linarith
          have := lt_of_mul_lt_mul_left hmul he.le
          linarith
        exact ⟨hx, by linarith, by linarith⟩
  | Move.R :: v, t, x => by
      have he : (0:ℝ) < 3 ^ v.length := by positivity
      obtain ⟨hA, hB⟩ := cellZ_bounds v t
      have hA' : (0:ℝ) ≤ ((cellZ v t).1 : ℝ) := by exact_mod_cast hA
      have hB' : ((cellZ v t).2 : ℝ) ≤ 2 * 3 ^ v.length := by
        have : ((cellZ v t).2 : ℝ) ≤ ((2 * 3 ^ v.length : ℤ) : ℝ) := by exact_mod_cast hB
        push_cast at this; linarith
      have ih := followsItin_iff_cellZ v t (act (3/2:ℝ) Move.R x)
      rw [act_R] at ih
      rw [followsItin_R, r_three_halves, act_R, ih]
      simp only [cellZ, List.length_cons, pow_succ]
      push_cast
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨by linarith, by linarith⟩
      · rintro ⟨h1, h2⟩
        have hx : x < 2/3 := by
          have hmul : (3:ℝ) ^ v.length * (3 * x) < 3 ^ v.length * 2 := by linarith
          have := lt_of_mul_lt_mul_left hmul he.le
          linarith
        exact ⟨hx, by linarith, by linarith⟩
  | Move.M :: v, [], x => by
      have he : (0:ℝ) < 3 ^ v.length := by positivity
      simp only [cellZ, List.length_cons, pow_succ, followsItin_M_nil, false_iff]
      push_cast
      rintro ⟨h1, h2⟩
      linarith
  | Move.M :: v, false :: t, x => by
      have he : (0:ℝ) < 3 ^ v.length := by positivity
      obtain ⟨hA, hB⟩ := cellZ_bounds v t
      have hA' : (0:ℝ) ≤ ((cellZ v t).1 : ℝ) := by exact_mod_cast hA
      have key : ∀ y : ℝ, y < 1/3 →
          (FollowsItin (3/2:ℝ) v t (act (3/2:ℝ) Move.M y) ↔
            (((cellZ v t).1 : ℝ) < 2 * 3 ^ v.length * (3/2 * y) ∧
              2 * 3 ^ v.length * (3/2 * y) < ((cellZ v t).2 : ℝ))) := by
        intro y hy
        rw [act_M_of_lt (3/2:ℝ) y (by rw [r_three_halves]; linarith),
          followsItin_iff_cellZ v t]
      rw [followsItin_M_cons]
      simp only [cellZ, List.length_cons, pow_succ, Bool.false_eq_true, if_false]
      push_cast
      rw [r_three_halves]
      constructor
      · rintro ⟨h1, h2⟩
        have hx : x < 1/3 := by linarith
        have hex : (3:ℝ) ^ v.length * x < 3 ^ v.length * (1/3) :=
          mul_lt_mul_of_pos_left hx he
        rw [key x hx] at h2
        obtain ⟨h2a, h2b⟩ := h2
        refine ⟨by linarith, ?_⟩
        rcases le_total ((cellZ v t).2 : ℝ) ((3:ℝ) ^ v.length) with hle | hle
        · rw [min_eq_left hle]; linarith
        · rw [min_eq_right hle]; linarith
      · rintro ⟨h1, h2⟩
        have h2e : 2 * (3:ℝ) ^ v.length * 3 * x < 2 * 3 ^ v.length := by
          rcases le_total ((cellZ v t).2 : ℝ) ((3:ℝ) ^ v.length) with hle | hle
          · rw [min_eq_left hle] at h2
            have hB' : ((cellZ v t).2 : ℝ) ≤ 3 ^ v.length := hle
            linarith
          · rw [min_eq_right hle] at h2; linarith
        have hx : x < 1/3 := by
          have hmul : (3:ℝ) ^ v.length * (3 * x) < 3 ^ v.length * 1 := by linarith
          have := lt_of_mul_lt_mul_left hmul he.le
          linarith
        refine ⟨by linarith, ?_⟩
        rw [key x hx]
        refine ⟨by linarith, ?_⟩
        rcases le_total ((cellZ v t).2 : ℝ) ((3:ℝ) ^ v.length) with hle | hle
        · rw [min_eq_left hle] at h2; linarith
        · rw [min_eq_right hle] at h2; linarith
  | Move.M :: v, true :: t, x => by
      have he : (0:ℝ) < 3 ^ v.length := by positivity
      obtain ⟨hA, hB⟩ := cellZ_bounds v t
      have hB' : ((cellZ v t).2 : ℝ) ≤ 2 * 3 ^ v.length := by
        have : ((cellZ v t).2 : ℝ) ≤ ((2 * 3 ^ v.length : ℤ) : ℝ) := by exact_mod_cast hB
        push_cast at this; linarith
      have key : ∀ y : ℝ, 2/3 < y →
          (FollowsItin (3/2:ℝ) v t (act (3/2:ℝ) Move.M y) ↔
            (((cellZ v t).1 : ℝ) < 2 * 3 ^ v.length * (3/2 * y - 1/2) ∧
              2 * 3 ^ v.length * (3/2 * y - 1/2) < ((cellZ v t).2 : ℝ))) := by
        intro y hy
        have hnot : ¬ y < r (3/2:ℝ) / 2 := by rw [r_three_halves]; push_neg; linarith
        rw [act_M_of_gt (3/2:ℝ) y hnot, followsItin_iff_cellZ v t]
        norm_num
      rw [followsItin_M_cons]
      simp only [cellZ, List.length_cons, pow_succ, if_true]
      push_cast
      rw [r_three_halves]
      constructor
      · rintro ⟨h1, h2⟩
        have hx : 2/3 < x := by linarith
        have hex : (3:ℝ) ^ v.length * (2/3) < 3 ^ v.length * x :=
          mul_lt_mul_of_pos_left hx he
        rw [key x hx] at h2
        obtain ⟨h2a, h2b⟩ := h2
        refine ⟨?_, by linarith⟩
        rcases le_total ((cellZ v t).1 : ℝ) ((3:ℝ) ^ v.length) with hle | hle
        · rw [max_eq_right hle]; linarith
        · rw [max_eq_left hle]; linarith
      · rintro ⟨h1, h2⟩
        have h1e : 2 * (3:ℝ) ^ v.length + 2 * 3 ^ v.length < 2 * 3 ^ v.length * 3 * x := by
          rcases le_total ((cellZ v t).1 : ℝ) ((3:ℝ) ^ v.length) with hle | hle
          · rw [max_eq_right hle] at h1; linarith
          · rw [max_eq_left hle] at h1
            have : ((3:ℝ) ^ v.length) ≤ ((cellZ v t).1 : ℝ) := hle
            linarith
        have hx : 2/3 < x := by
          have hmul : (3:ℝ) ^ v.length * 2 < 3 ^ v.length * (3 * x) := by linarith
          have := lt_of_mul_lt_mul_left hmul he.le
          linarith
        refine ⟨by linarith, ?_⟩
        rw [key x hx]
        refine ⟨?_, by linarith⟩
        rcases le_total ((cellZ v t).1 : ℝ) ((3:ℝ) ^ v.length) with hle | hle
        · rw [max_eq_right hle] at h1; linarith
        · rw [max_eq_left hle] at h1; linarith

end KnotGame
