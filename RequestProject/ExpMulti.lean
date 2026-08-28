import RequestProject.ExpCount

/-!
# Higher multiplicity: from `k` returning words to `k ^ (m / T) ≤ K lam m` (round 7)

`RequestProject.ExpCount` doubles the count every `T` steps from *two* returning
words.  Nothing in that argument is special to two: if every point of a closed
interval `J ⊆ (0,1)` admits `k` **distinct** branch words of a common length `T`
whose images again lie in `J`, the count is multiplied by `k` every `T` steps,
and the exponential bound improves from `2 ^ (m/T)` to `k ^ (m/T)`.

This matters quantitatively.  At `lam = 3/2` the measured growth of `K` is
`(2/lam)^m = (4/3)^m ≈ 1.333^m`; two words of length `5` give only
`2^(1/5) ≈ 1.149` per step, while `15` words of length `12` give
`15^(1/12) ≈ 1.253` (see `RequestProject.ExpSharp`).

## Conventions (SCRUPLES)

* The `k` words are packaged as a `Finset` with `k ≤ card`, so distinctness is
  automatic and the counting is a `Finset.card_biUnion`.
* As in `ExpCount`, only the *images* are constrained: legality of the words is
  derived from absorption.
* `MDoubling lam a b T 2` is the same hypothesis as `Doubling lam a b T` up to
  packaging; the two are kept separate so that the round's earlier results are
  unaffected.
-/

namespace KnotGame
namespace ExpMulti

open KnotGame.Branching KnotGame.ExpCount
open scoped Classical

variable {lam a b : ℝ} {T k : ℕ}

/-- **Multiplicity `k` on `[a,b]`.**  Every point of `[a,b]` admits at least `k`
distinct branch words of length `T` whose images again lie in `[a,b]`. -/
def MDoubling (lam a b : ℝ) (T k : ℕ) : Prop :=
  ∀ x : ℝ, a ≤ x → x ≤ b → ∃ ws : Finset (List (Fin 2)), k ≤ ws.card ∧
    ∀ w ∈ ws, w.length = T ∧ a ≤ rapp lam x w ∧ rapp lam x w ≤ b

/-- **The renewal step at multiplicity `k`.**  Inside `[a,b]` the count is
multiplied by at least `k` every `T` steps. -/
lemma mul_kappa_le (h1 : 1 < lam) (ha : 0 < a) (hb : b < 1) (hmd : MDoubling lam a b T k)
    (n : ℕ) {x : ℝ} (hx0 : a ≤ x) (hx1 : x ≤ b) :
    k * kappa lam a b n ≤ Kx lam x (n + T) := by
  obtain ⟨ws, hcard, hws⟩ := hmd x hx0 hx1
  have hx0' : (0:ℝ) < x := lt_of_lt_of_le ha hx0
  have hx1' : x < 1 := lt_of_le_of_lt hx1 hb
  set A : List (Fin 2) → Finset (List (Fin 2)) :=
    fun w => (SW lam (rapp lam x w) n).image (fun z => w ++ z) with hA
  have hsurv : ∀ w ∈ ws, bSurvives lam x w := by
    intro w hw
    obtain ⟨-, h1', h2'⟩ := hws w hw
    exact bSurvives_of_image_mem h1 hx0' hx1' (by linarith) (by linarith)
  have hdisj : (↑ws : Set (List (Fin 2))).PairwiseDisjoint A := by
    intro u hu v hv huv
    simp only [Finset.mem_coe] at hu hv
    refine Finset.disjoint_left.2 ?_
    rintro c hc hc'
    simp only [hA, Finset.mem_image] at hc hc'
    obtain ⟨z1, -, rfl⟩ := hc
    obtain ⟨z2, -, h2⟩ := hc'
    have hlu := (hws u hu).1
    have hlv := (hws v hv).1
    have := congrArg (List.take T) h2
    rw [List.take_left' hlv, List.take_left' hlu] at this
    exact huv this.symm
  have hcards : ∀ w ∈ ws, kappa lam a b n ≤ (A w).card := by
    intro w hw
    obtain ⟨-, h1', h2'⟩ := hws w hw
    have hinj : Function.Injective (fun z : List (Fin 2) => w ++ z) :=
      fun z1 z2 h => List.append_cancel_left h
    rw [hA, Finset.card_image_of_injective _ hinj]
    exact kappa_le h1' h2' n
  have hsub : ws.biUnion A ⊆ SW lam x (n + T) := by
    refine Finset.biUnion_subset.2 (fun w hw => ?_)
    exact image_append_subset (hsurv w hw) (hws w hw).1 n
  calc k * kappa lam a b n ≤ ws.card * kappa lam a b n :=
        Nat.mul_le_mul_right _ hcard
    _ ≤ ∑ w ∈ ws, (A w).card := by
        simpa [smul_eq_mul] using Finset.card_nsmul_le_sum ws (fun w => (A w).card)
          (kappa lam a b n) hcards
    _ = (ws.biUnion A).card := (Finset.card_biUnion hdisj).symm
    _ ≤ Kx lam x (n + T) := Finset.card_le_card hsub

lemma pow_le_kappa (h1 : 1 < lam) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hmd : MDoubling lam a b T k) (j : ℕ) : k ^ j ≤ kappa lam a b (T * j) := by
  induction j with
  | zero =>
      refine le_kappa hab (fun x _ _ => ?_)
      rw [Nat.mul_zero, pow_zero, Kx_zero]
  | succ j ih =>
      have h5 : T * (j + 1) = T * j + T := by ring
      rw [h5]
      refine le_kappa hab (fun x hx1 hx2 => ?_)
      calc k ^ (j + 1) = k * k ^ j := by ring
        _ ≤ k * kappa lam a b (T * j) := Nat.mul_le_mul_left k ih
        _ ≤ Kx lam x (T * j + T) := mul_kappa_le h1 ha hb hmd (T * j) hx1 hx2

/-- **From multiplicity `k` to an exponential count.**  If every point of a
closed interval `[a,b] ⊆ (0,1)` containing `1/2` has `k` distinct legal
continuations of length `T` returning to `[a,b]`, then `K lam m ≥ k ^ (m / T)`. -/
theorem pow_le_K_of_mdoubling (h1 : 1 < lam) (h2 : lam < 2) (ha : 0 < a) (hb : b < 1)
    (ha2 : a ≤ 1/2) (hb2 : (1/2 : ℝ) ≤ b) (hmd : MDoubling lam a b T k) (m : ℕ) :
    k ^ (m / T) ≤ K lam m := by
  have hab : a ≤ b := le_trans ha2 hb2
  rw [← Kx_eq_K]
  calc k ^ (m / T) ≤ kappa lam a b (T * (m / T)) := pow_le_kappa h1 ha hb hab hmd _
    _ ≤ Kx lam (1/2 : ℝ) (T * (m / T)) := kappa_le ha2 hb2 _
    _ ≤ Kx lam (1/2 : ℝ) m := by
        refine Kx_mono h1 h2 (by linarith) (by linarith) ?_
        calc T * (m / T) = m / T * T := Nat.mul_comm _ _
          _ ≤ m := Nat.div_mul_le_self m T

end ExpMulti
end KnotGame
