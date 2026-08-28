import RequestProject.Suffix

/-!
# Section 6: periodic runs and Littlewood polynomials (Work Order 9)

Proposition 6.1 (the Littlewood identity), Corollary 6.3 (no return to `1/2`
under a periodic run) and Proposition 6.5 (a kind periodic sequence forces
`N = ∞`).
-/

namespace KnotGame

variable {lam : ℝ}

lemma f_eq_sub (lam : ℝ) (e : Fin 2) (y : ℝ) :
    f lam e y = lam * y - ((e : ℕ) : ℝ) * (lam - 1) := by
  fin_cases e <;> simp [f]

/-- The orbit of `x` along a branch itinerary: `x_{n+1} = f_{ε_n}(x_n)`. -/
noncomputable def orbit (lam : ℝ) (eps : ℕ → Fin 2) (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 => f lam (eps n) (orbit lam eps x n)

/-- The closed form of the composite map along an itinerary. -/
lemma orbit_eq (lam : ℝ) (eps : ℕ → Fin 2) (x : ℝ) (q : ℕ) :
    orbit lam eps x q
      = lam ^ q * x - (lam - 1) * ∑ i ∈ Finset.range q, ((eps (q - 1 - i) : ℕ) : ℝ) * lam ^ i := by
  induction q with
  | zero => simp [orbit]
  | succ q ih =>
      rw [orbit, ih, f_eq_sub, Finset.sum_range_succ']
      have hidx : ∀ i ∈ Finset.range q,
          ((eps (q + 1 - 1 - (i + 1)) : ℕ) : ℝ) * lam ^ (i + 1)
            = (((eps (q - 1 - i) : ℕ) : ℝ) * lam ^ i) * lam := by
        intro i _
        have : q + 1 - 1 - (i + 1) = q - 1 - i := by omega
        rw [this]; ring
      rw [Finset.sum_congr rfl hidx, ← Finset.sum_mul]
      simp only [Nat.add_sub_cancel, Nat.sub_zero, pow_zero, mul_one, pow_succ]
      ring

/-- **Proposition 6.1.** The orbit of `1/2` along the itinerary `(ε_1,…,ε_q)`
satisfies `x_q = 1/2` if and only if `lam` is a root of the Littlewood
polynomial of degree `q-1` whose signs record the (reversed) itinerary. -/
theorem littlewood (h : 1 < lam) (eps : ℕ → Fin 2) (q : ℕ) :
    orbit lam eps (1/2) q = 1/2 ↔
      ∑ i ∈ Finset.range q, (1 - 2 * ((eps (q - 1 - i) : ℕ) : ℝ)) * lam ^ i = 0 := by
  have hne : lam - 1 ≠ 0 := by linarith
  have hgeom : (∑ i ∈ Finset.range q, lam ^ i) * (lam - 1) = lam ^ q - 1 := geom_sum_mul lam q
  rw [orbit_eq]
  set S := ∑ i ∈ Finset.range q, ((eps (q - 1 - i) : ℕ) : ℝ) * lam ^ i with hS
  have hsplit : ∑ i ∈ Finset.range q, (1 - 2 * ((eps (q - 1 - i) : ℕ) : ℝ)) * lam ^ i
      = (∑ i ∈ Finset.range q, lam ^ i) - 2 * S := by
    rw [hS, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (by intro i _; ring)
  rw [hsplit]
  constructor
  · intro hx
    have h1 : lam ^ q - 1 = 2 * (lam - 1) * S := by linarith
    have h2 : (∑ i ∈ Finset.range q, lam ^ i) * (lam - 1) = (2 * S) * (lam - 1) := by
      rw [hgeom, h1]; ring
    have h3 : (∑ i ∈ Finset.range q, lam ^ i) = 2 * S := mul_right_cancel₀ hne h2
    rw [h3]; ring
  · intro hx
    have h3 : (∑ i ∈ Finset.range q, lam ^ i) = 2 * S := by linarith
    have h1 : lam ^ q - 1 = 2 * S * (lam - 1) := by rw [← hgeom, h3]
    linarith

/-- The word consisting of the first `n` letters of an infinite sequence. -/
def prefixWord (v : ℕ → Move) (n : ℕ) : List Move := (List.range n).map v

@[simp] lemma prefixWord_length (v : ℕ → Move) (n : ℕ) : (prefixWord v n).length = n := by
  simp [prefixWord]

lemma prefixWord_succ (v : ℕ → Move) (n : ℕ) :
    prefixWord v (n + 1) = prefixWord v n ++ [v n] := by
  simp [prefixWord, List.range_succ]

/-- A periodic sequence is unchanged by shifting a multiple of the period. -/
lemma periodic_add_mul {v : ℕ → Move} {p : ℕ} (hper : Function.Periodic v p) (a k : ℕ) :
    v (a + p * k) = v a := by
  induction k with
  | zero => simp
  | succ k ih =>
      have : a + p * (k + 1) = (a + p * k) + p := by ring
      rw [this, hper, ih]

/-- Splitting off the first period of a periodic sequence. -/
lemma prefixWord_period_append {v : ℕ → Move} {p : ℕ} (hper : Function.Periodic v p) (n : ℕ) :
    prefixWord v (p + n) = prefixWord v p ++ prefixWord v n := by
  simp only [prefixWord, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  have : v (p + i) = v i := by
    have := periodic_add_mul hper i 1
    simpa [Nat.add_comm, Nat.mul_one] using this
  simpa using this

/-- **Corollary 6.3.** Under a periodic run whose phase `p` carries `M`, the
orbit of a knot born at that phase never returns to `1/2` at a time divisible by
the period.

The divisibility hypothesis `p ∣ q` is the phase-alignment step of the paper's
proof; see the census for a discussion. -/
theorem no_return_to_half (h : 1 < lam) {v : ℕ → Move} {p q : ℕ} (hp : 0 < p)
    (hq : 0 < q) (hper : Function.Periodic v p) (hM : v (p - 1) = Move.M)
    (hpq : p ∣ q) (hs : survivesWord lam (1/2) (prefixWord v q)) :
    posAfter lam (1/2) (prefixWord v q) ≠ 1/2 := by
  obtain ⟨k, rfl⟩ := hpq
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp at hq
    · exact hk
  -- the last letter of the run is `M`
  have hlast : v (p * k - 1) = Move.M := by
    have hidx : p * k - 1 = (p - 1) + p * (k - 1) := by
      cases k with
      | zero => omega
      | succ k' => cases p with
        | zero => omega
        | succ p' => simp; ring_nf; omega
    rw [hidx, periodic_add_mul hper, hM]
  obtain ⟨n, hn⟩ : ∃ n, p * k = n + 1 := ⟨p * k - 1, by omega⟩
  rw [hn] at hs ⊢
  rw [prefixWord_succ] at hs ⊢
  rw [survivesWord_append] at hs
  rw [posAfter_append]
  have hn' : v n = Move.M := by rw [← hlast]; congr 1; omega
  rw [hn'] at hs ⊢
  simp only [posAfter_cons, posAfter_nil, survivesWord_cons, survivesWord_nil, and_true] at hs ⊢
  exact act_M_ne_half h hs.2

/-- An infinite sequence is **kind** for `lam` if the orbit of `1/2` under it
meets no deleted interval. -/
def Kind (lam : ℝ) (v : ℕ → Move) : Prop := ∀ n, survivesWord lam (1/2) (prefixWord v n)

/-- Each further period contributes at least one immortal knot. -/
lemma births_period_succ {v : ℕ → Move} {p : ℕ} (hp : 0 < p)
    (hper : Function.Periodic v p) (hM : v (p - 1) = Move.M) (hk : Kind lam v) (k : ℕ) :
    births lam (prefixWord v (p * k)) + 1 ≤ births lam (prefixWord v (p * (k + 1))) := by
  have hpk : p * (k + 1) = p + p * k := by ring
  rw [hpk, prefixWord_period_append hper]
  obtain ⟨n, hn⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  have hvn : v n = Move.M := by rw [← hM, hn]; congr 1
  have hsplit : prefixWord v p = prefixWord v n ++ [Move.M] := by
    rw [hn, prefixWord_succ, hvn]
  rw [hsplit, List.append_assoc]
  refine le_trans ?_ (births_le_append (prefixWord v n) _)
  rw [List.singleton_append, births_cons, if_pos ⟨rfl, hk (p * k)⟩]

/-- **Proposition 6.5.** If `v` is kind and periodic with `v_p = M`, then
`N_lam` is unbounded.  No hypothesis on the orbit is needed. -/
theorem N_unbounded_of_kind (h : 1 < lam) {v : ℕ → Move} {p : ℕ} (hp : 0 < p)
    (hper : Function.Periodic v p) (hM : v (p - 1) = Move.M) (hk : Kind lam v) :
    ∀ k : ℕ, ∃ n, k ≤ N lam n := by
  have key : ∀ k : ℕ, k ≤ births lam (prefixWord v (p * k)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have := births_period_succ hp hper hM hk k
        omega
  intro k
  refine ⟨p * k, ?_⟩
  have h1 := births_le_N h (prefixWord v (p * k))
  rw [prefixWord_length] at h1
  exact le_trans (key k) h1

end KnotGame
