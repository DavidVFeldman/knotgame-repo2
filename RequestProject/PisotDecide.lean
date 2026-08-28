import RequestProject.Gaps
import RequestProject.RecordDepths

/-!
# Decidability at a Pisot parameter (paper `cor:decide`)

Corollary 7 of *Knot counts in an interval deletion game* (`cor:decide`) reads:
for a Pisot parameter the reachable configurations form a finite set, `N_λ` is
eventually constant, and `sup_n N_λ(n)` is computable by a finite search.  The
census of round 1 recorded it as deferred — only the finiteness of the orbit
(`orb_finite`, paper `thm:pisot`) was certified.  This file supplies it.

Every knot of every reachable configuration lies in the orbit of `1/2`
(`run_subset_Orb`, an instance of the invariance principle `run_subset`), so at
a Pisot parameter every reachable configuration is a subset of one fixed finite
set:

* `reachable_finite` — the set of reachable configurations is finite;
* `N_le_card_orb` — `N_λ(n)` is bounded by the size of the orbit, uniformly
  in `n`;
* `N_eventually_constant` — `N_λ` is eventually constant, being monotone and
  bounded;
* `sup_N_isGreatest` — the supremum of `N_λ` is attained at a finite level
  `n₀`, which is the sense in which a finite search computes it.
-/

namespace KnotGame

variable {lam : ℝ}

/-! ## Reachable configurations live in the orbit -/

lemma half_mem_Orb : (1/2 : ℝ) ∈ Orb lam := ⟨[], trivial, rfl⟩

lemma orb_closed_act {x : ℝ} (hx : x ∈ Orb lam) {m : Move} (hs : survives lam m x) :
    act lam m x ∈ Orb lam := by
  obtain ⟨w, hw, rfl⟩ := hx
  refine ⟨w ++ [m], ?_, ?_⟩
  · rw [survivesWord_append]
    exact ⟨hw, ⟨hs, trivial⟩⟩
  · rw [posAfter_append]
    rfl

/-- Every knot of every reachable configuration lies in the orbit of `1/2`. -/
theorem run_subset_Orb (w : List Move) : ∀ y ∈ run lam w, y ∈ Orb lam :=
  run_subset (Orb lam) half_mem_Orb (fun _ hx _ hs => orb_closed_act hx hs) w

/-- The set of configurations reachable by some run. -/
def reachable (lam : ℝ) : Set (Finset ℝ) := {S | ∃ w : List Move, run lam w = S}

/-! ## `cor:decide` -/

/-- **`cor:decide`, first clause.**  At a Pisot parameter only finitely many
configurations are reachable. -/
theorem reachable_finite (h : IsPisot lam) : (reachable lam).Finite := by
  classical
  have hfin := orb_finite h
  have hsub : reachable lam ⊆ ↑(hfin.toFinset.powerset) := by
    rintro S ⟨w, rfl⟩
    simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset]
    intro y hy
    exact (Set.Finite.mem_toFinset hfin).2 (run_subset_Orb w y hy)
  exact Set.Finite.subset (hfin.toFinset.powerset : Finset (Finset ℝ)).finite_toSet hsub

/-- At a Pisot parameter the knot count is bounded by the size of the orbit. -/
theorem N_le_card_orb (h : IsPisot lam) (n : ℕ) : N lam n ≤ (orb_finite h).toFinset.card := by
  classical
  refine Finset.sup_le ?_
  intro v _
  refine Finset.card_le_card ?_
  intro y hy
  exact (Set.Finite.mem_toFinset _).2 (run_subset_Orb _ y hy)

/-- **`cor:decide`, second clause.**  At a Pisot parameter `N_λ` is eventually
constant. -/
theorem N_eventually_constant (h : IsPisot lam) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → N lam n = N lam n₀ := by
  have h1 : 1 < lam := h.1
  have hbdd : BddAbove (Set.range (N lam)) := by
    refine ⟨(orb_finite h).toFinset.card, ?_⟩
    rintro y ⟨n, rfl⟩
    exact N_le_card_orb h n
  have hne : (Set.range (N lam)).Nonempty := ⟨N lam 0, ⟨0, rfl⟩⟩
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, N lam n₀ = sSup (Set.range (N lam)) := Nat.sSup_mem hne hbdd
  refine ⟨n₀, fun n hn => ?_⟩
  have hle : N lam n ≤ sSup (Set.range (N lam)) := le_csSup hbdd ⟨n, rfl⟩
  have hge : N lam n₀ ≤ N lam n := N_le_of_le h1 hn
  omega

/-- **`cor:decide`, third clause.**  At a Pisot parameter the supremum of `N_λ`
is attained at a finite level: a search to that level computes it. -/
theorem sup_N_isGreatest (h : IsPisot lam) :
    ∃ n₀ : ℕ, IsGreatest (Set.range (N lam)) (N lam n₀) := by
  have hbdd : BddAbove (Set.range (N lam)) := by
    refine ⟨(orb_finite h).toFinset.card, ?_⟩
    rintro y ⟨n, rfl⟩
    exact N_le_card_orb h n
  have hne : (Set.range (N lam)).Nonempty := ⟨N lam 0, ⟨0, rfl⟩⟩
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, N lam n₀ = sSup (Set.range (N lam)) := Nat.sSup_mem hne hbdd
  refine ⟨n₀, ⟨n₀, rfl⟩, ?_⟩
  rintro y ⟨n, rfl⟩
  rw [hn₀]
  exact le_csSup hbdd ⟨n, rfl⟩

end KnotGame
