import RequestProject.Compactness

/-!
# T18 — the topological density criterion (paper Theorem `thm:density0`)

The paper's Theorem `thm:density0` reads: *if the endpoints of kind words are
dense in `(0,1)`, then some run carries infinitely many simultaneous knots; in
particular `N_λ = ∞`.*

A **kind word** is a word `u` that `1/2` survives; its **endpoint** is
`Φ_u(1/2) = posAfter lam (1/2) u`.  The density hypothesis is `KindDense`
below.

**This is a conditional theorem.**  The hypothesis `KindDense lam` is *not*
certified here for any specific `λ`, and no proof of it is known for any single
non-Pisot parameter (paper Question `q:ae`); at every Pisot `λ` it is false,
because the kind orbit of `1/2` is then finite.  Everything in this file is an
implication with `KindDense lam` as an explicit hypothesis.

The proof is the paper's: T14 (`exists_long_cell`) provides an open target
inside the survivor set of the word built so far, the hypothesis provides a
kind word landing in that target, T15 (`knotAt_cons_M`, `knotAt_append`) gains
one knot while every earlier knot keeps its age, and T17
(`infinitelyManyKnots_of_boundedAgeWitnesses`) assembles the single run.
-/

namespace KnotGame

variable {lam : ℝ}

/-! ## The hypothesis -/

/-- **Density of kind endpoints in `(0,1)`.**  Every nonempty open
subinterval of `(0,1)` contains `Φ_u(1/2)` for some kind word `u` (a word that
`1/2` survives).  This is the hypothesis of paper Theorem `thm:density0`; it is
certified for no specific `λ`. -/
def KindDense (lam : ℝ) : Prop :=
  ∀ c d : ℝ, 0 ≤ c → c < d → d ≤ 1 →
    ∃ u : List Move, survivesWord lam (1/2) u ∧
      c < posAfter lam (1/2) u ∧ posAfter lam (1/2) u < d

/-! ## Knots survive prefixing -/

/-- Prepending letters changes neither the age nor the position of a knot:
a knot of `v` is still a knot of `p ++ v`.  (This is the half of T15 that makes
the construction below nest.) -/
lemma knotAt_append (p : List Move) {v : List Move} {a : ℕ} {x : ℝ}
    (hk : KnotAt lam v a x) : KnotAt lam (p ++ v) a x := by
  obtain ⟨q, s, rfl, h1, h2, h3⟩ := hk
  exact ⟨p ++ q, s, by simp, h1, h2, h3⟩

lemma hasKnotAge_append (p : List Move) {v : List Move} {a : ℕ}
    (hk : HasKnotAge lam v a) : HasKnotAge lam (p ++ v) a :=
  hk.imp fun _ hx => knotAt_append p hx

/-! ## One extension step -/

/-- **The extension step.**  Under density, every word `v` can be preceded by a
kind word `u` in such a way that `1/2` survives all of `u ++ v`.  The target is
the long cell of `S(v)` supplied by T14. -/
lemma exists_extension (h : 1 < lam) (H : KindDense lam) (v : List Move) :
    ∃ u : List Move, survivesWord lam (1/2) (u ++ v) := by
  obtain ⟨p, hp, -, hall⟩ := exists_long_cell h v
  obtain ⟨hp0, hp12, hp1⟩ := (tidy_cells h v).bounds p hp
  obtain ⟨u, hu, hu1, hu2⟩ := H p.1 p.2 hp0 hp12 hp1
  refine ⟨u, ?_⟩
  rw [survivesWord_append]
  exact ⟨hu, (hall _ hu1 hu2).2.2⟩

/-- The witness words: `dword h H k` carries `k` knots.  Each is obtained from
its predecessor by prepending a kind word (from `exists_extension`) and then an
`M`, so that the predecessor is a suffix and all of its knots persist. -/
noncomputable def dword (h : 1 < lam) (H : KindDense lam) : ℕ → List Move
  | 0 => []
  | k + 1 => Move.M :: (Classical.choose (exists_extension h H (dword h H k)) ++ dword h H k)

lemma dword_succ (h : 1 < lam) (H : KindDense lam) (k : ℕ) :
    dword h H (k + 1) =
      Move.M :: (Classical.choose (exists_extension h H (dword h H k)) ++ dword h H k) := by
  rw [dword]

/-- Each witness word is a suffix of all the later ones. -/
lemma dword_suffix (h : 1 < lam) (H : KindDense lam) :
    ∀ {m k : ℕ}, m ≤ k → ∃ p, dword h H k = p ++ dword h H m := by
  intro m k
  induction k with
  | zero => intro hk; exact ⟨[], by rw [Nat.le_zero.mp hk]; simp⟩
  | succ k ih =>
      intro hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hk) with hlt | rfl
      · obtain ⟨p, hp⟩ := ih (Nat.lt_succ_iff.mp hlt)
        exact ⟨Move.M :: (Classical.choose (exists_extension h H (dword h H k)) ++ p), by
          rw [dword_succ, hp]; simp⟩
      · exact ⟨[], by simp⟩

/-- The witness words grow strictly in length. -/
lemma dword_length_lt (h : 1 < lam) (H : KindDense lam) (k : ℕ) :
    (dword h H k).length < (dword h H (k + 1)).length := by
  rw [dword_succ]
  simp only [List.length_cons, List.length_append]
  omega

lemma dword_length_strictMono (h : 1 < lam) (H : KindDense lam) :
    StrictMono fun k => (dword h H k).length :=
  strictMono_nat_of_lt_succ (dword_length_lt h H)

/-- Prepending the `M` creates one new knot, of age `|dword (k+1)| - 1`. -/
lemma hasKnotAge_dword_succ (h : 1 < lam) (H : KindDense lam) (k : ℕ) :
    HasKnotAge lam (dword h H (k + 1)) ((dword h H (k + 1)).length - 1) := by
  have hs := Classical.choose_spec (exists_extension h H (dword h H k))
  have hd := dword_succ h H k
  have hlen : (dword h H (k + 1)).length - 1 =
      (Classical.choose (exists_extension h H (dword h H k)) ++ dword h H k).length := by
    rw [hd]; simp
  rw [hlen, hd]
  exact ⟨_, knotAt_cons_M hs⟩

/-- Every witness word carries all the knots created before it. -/
lemma hasKnotAge_dword (h : 1 < lam) (H : KindDense lam) {i k : ℕ} (hik : i < k) :
    HasKnotAge lam (dword h H k) ((dword h H (i + 1)).length - 1) := by
  obtain ⟨p, hp⟩ := dword_suffix h H (m := i + 1) (k := k) hik
  rw [hp]
  exact hasKnotAge_append p (hasKnotAge_dword_succ h H i)

/-! ## The theorem -/

/-- **T18** (paper Theorem `thm:density0`).  If the endpoints of kind words are
dense in `(0,1)`, then some left-infinite run carries infinitely many
simultaneous knots — condition (i) of the compactness criterion T17.

The hypothesis `KindDense lam` is certified for no specific `λ`; this is a
conditional theorem. -/
theorem infinitelyManyKnots_of_kindDense (h : 1 < lam) (H : KindDense lam) :
    InfinitelyManyKnots lam := by
  refine infinitelyManyKnots_of_boundedAgeWitnesses
    ⟨fun i => (dword h H (i + 1)).length - 1, dword h H,
      fun _ i => (dword h H (i + 1)).length - 1, fun k => ⟨?_, ?_, ?_⟩⟩
  · exact fun i hik => hasKnotAge_dword h H hik
  · rintro i j hij -
    have hlt : (dword h H (i + 1)).length < (dword h H (j + 1)).length :=
      dword_length_strictMono h H (show i + 1 < j + 1 by omega)
    have hi : 0 < (dword h H (i + 1)).length := by rw [dword_succ]; simp
    simp only
    omega
  · exact fun i _ => le_refl _

/-- **T18, the stated conclusion.**  Under the density hypothesis the knot
counts `N_λ(n)` are unbounded, i.e. `N_λ = ∞`. -/
theorem N_unbounded_of_kindDense (h : 1 < lam) (H : KindDense lam) :
    ∀ K : ℕ, ∃ n : ℕ, K ≤ N lam n :=
  N_unbounded_of_infinitelyManyKnots h (infinitelyManyKnots_of_kindDense h H)

end KnotGame
