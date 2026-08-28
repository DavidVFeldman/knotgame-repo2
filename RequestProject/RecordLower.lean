import RequestProject.Gaps

/-!
# The universal lower bounds on the record lengths (`prop:lowerbound`, `cor:recursive`)

The paper's Proposition `prop:lowerbound` reads `d_λ(k) ≥ 2k − 1` for every `λ`
and every `k`, and its Corollary `cor:recursive` reads
`d_λ(k+1) ≥ d_λ(k) + 2`.  Both rest on the birth-spacing lemma of round 2
(`two_mul_births_le_length_succ`): a knot born at time `t` is destroyed if the
move at `t+1` is `M`, so surviving births are at least two apart.

The corollary is proved through the *chopping lemma*
`births_le_births_take_add_one`: deleting the last two letters of a word costs
at most one surviving birth, since the two deleted positions cannot both carry
one and a birth at an earlier position survives the truncation (survival is
prefix-closed, `survivesWord_take`).

## Conventions (SCRUPLES)

* `d λ k = sInf {n | k ≤ N λ n}` returns `0` when no run ever attains `k`
  knots, so the paper's inequalities need the attainability hypothesis
  `∃ n, k ≤ N λ n`; without it `d λ k = 0` and both statements are false as
  literally stated (take `λ ≥ 2` and `k = 3`).  The hypothesis is exactly the
  paper's standing assumption that `d_λ(k)` *is* the length of a record run.
* `prop:lowerbound` is stated as `2 * k ≤ d λ k + 1`, which is `d ≥ 2k − 1`
  without truncated subtraction.  The hypothesis-free form
  `two_mul_le_of_le_N` — any `n` with `k ≤ N λ n` satisfies `2k ≤ n + 1` — is
  what the argument actually uses.
* `cor:recursive` needs `k ≥ 1`: at `k = 0` it is false, since `d λ 0 = 0`
  while `d λ 1 = 1` whenever a birth is possible at all.
-/

namespace KnotGame

variable {lam : ℝ}

/-! ## Survival is closed under taking prefixes -/

/-- If a knot survives a whole word it survives every prefix of it. -/
lemma survivesWord_take (x : ℝ) : ∀ (w : List Move) (j : ℕ),
    survivesWord lam x w → survivesWord lam x (w.take j)
  | _, 0, _ => by simp
  | [], _ + 1, _ => by simp
  | m :: w, j + 1, hs => by
      refine ⟨hs.1, ?_⟩
      exact survivesWord_take (act lam m x) w j hs.2

/-! ## Chopping the last two letters costs at most one birth -/

/-- A word of length at most two carries at most one surviving birth. -/
lemma births_le_one_of_length_le_two (h : 1 < lam) {w : List Move}
    (hw : w.length ≤ 2) : births lam w ≤ 1 := by
  have := two_mul_births_le_length_succ h w.length w rfl
  omega

/-- **The chopping lemma.**  Deleting the last two letters of a word destroys at
most one surviving birth: the two deleted positions cannot both carry one, since
surviving births are at least two apart, and a birth at an earlier position
survives the truncation because survival is prefix-closed. -/
lemma births_le_births_take_add_one (h : 1 < lam) :
    ∀ (n : ℕ) (w : List Move), w.length = n →
      births lam w ≤ births lam (w.take (w.length - 2)) + 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w hw
    match w with
    | [] => simp
    | [a] => simpa using births_le_one_of_length_le_two h (w := [a]) (by simp)
    | [a, b] => simpa using births_le_one_of_length_le_two h (w := [a, b]) (by simp)
    | a :: b :: c :: rest =>
        set u : List Move := b :: c :: rest with hu
        have hlen : (a :: u).length = u.length + 1 := by simp
        have hu2 : 2 ≤ u.length := by simp [hu]
        have hstep : (a :: u).take ((a :: u).length - 2) = a :: u.take (u.length - 2) := by
          rw [hlen]
          have : u.length + 1 - 2 = (u.length - 2) + 1 := by omega
          rw [this, List.take_succ_cons]
        have hind : births lam u ≤ births lam (u.take (u.length - 2)) + 1 :=
          ih u.length (by simp [hu] at hw ⊢; omega) u rfl
        have hmono : (if a = Move.M ∧ survivesWord lam (1/2) u then 1 else 0) ≤
            (if a = Move.M ∧ survivesWord lam (1/2) (u.take (u.length - 2)) then 1 else 0) := by
          by_cases hc : a = Move.M ∧ survivesWord lam (1/2) u
          · rw [if_pos hc, if_pos ⟨hc.1, survivesWord_take (1/2) u (u.length - 2) hc.2⟩]
          · rw [if_neg hc]; exact Nat.zero_le _
        have hL : births lam (a :: u) =
            births lam u + (if a = Move.M ∧ survivesWord lam (1/2) u then 1 else 0) :=
          births_cons (lam := lam) a u
        have hR : births lam (a :: u.take (u.length - 2)) =
            births lam (u.take (u.length - 2)) +
              (if a = Move.M ∧ survivesWord lam (1/2) (u.take (u.length - 2)) then 1 else 0) :=
          births_cons (lam := lam) a _
        rw [hstep, hL, hR]
        omega

/-! ## `prop:lowerbound` -/

/-- **`prop:lowerbound`, hypothesis-free form.**  If some run of length `n`
attains `k` knots then `2k ≤ n + 1`. -/
theorem two_mul_le_of_le_N (h : 1 < lam) {k n : ℕ} (hk : k ≤ N lam n) :
    2 * k ≤ n + 1 := by
  classical
  obtain ⟨v, -, hv⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin n → Move))
    ⟨fun _ => Move.L, Finset.mem_univ _⟩
    (fun v : Fin n → Move => (run lam (List.ofFn v)).card)
  have hcard : (run lam (List.ofFn v)).card = births lam (List.ofFn v) := card_run h _
  have hlen : (List.ofFn v).length = n := by simp
  have hb := two_mul_births_le_length_succ h (List.ofFn v).length (List.ofFn v) rfl
  rw [hlen] at hb
  have hN : N lam n = (run lam (List.ofFn v)).card := hv
  omega

/-- **`prop:lowerbound`** (paper: `d_λ(k) ≥ 2k − 1`), stated without truncated
subtraction and with the attainability hypothesis the definition of `d`
requires. -/
theorem d_ge_two_mul_sub_one (h : 1 < lam) {k : ℕ} (hk : ∃ n, k ≤ N lam n) :
    2 * k ≤ d lam k + 1 :=
  two_mul_le_of_le_N h (Nat.sInf_mem hk)

/-! ## `cor:recursive` -/

/-- **`cor:recursive`** (paper: `d_λ(k+1) ≥ d_λ(k) + 2`).  A record run for
`k + 1` knots already carries `k` of them two steps earlier. -/
theorem d_succ_ge_add_two (h : 1 < lam) {k : ℕ} (hk : 1 ≤ k)
    (hne : ∃ n, k + 1 ≤ N lam n) :
    d lam k + 2 ≤ d lam (k + 1) := by
  classical
  set n : ℕ := d lam (k + 1) with hn
  have hmem : k + 1 ≤ N lam n := Nat.sInf_mem hne
  have hn3 : 2 * (k + 1) ≤ n + 1 := two_mul_le_of_le_N h hmem
  obtain ⟨v, -, hv⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin n → Move))
    ⟨fun _ => Move.L, Finset.mem_univ _⟩
    (fun v : Fin n → Move => (run lam (List.ofFn v)).card)
  set w : List Move := List.ofFn v with hw
  have hlen : w.length = n := by simp [hw]
  have hcard : (run lam w).card = births lam w := card_run h _
  have hbig : k + 1 ≤ births lam w := by
    rw [← hcard, ← hv]; exact hmem
  have hchop : births lam w ≤ births lam (w.take (w.length - 2)) + 1 :=
    births_le_births_take_add_one h w.length w rfl
  have hklen : k ≤ births lam (w.take (w.length - 2)) := by omega
  have htlen : (w.take (w.length - 2)).length = n - 2 := by
    rw [List.length_take, hlen]; omega
  have hle : births lam (w.take (w.length - 2)) ≤ N lam (n - 2) := by
    have := births_le_N h (w.take (w.length - 2))
    rwa [htlen] at this
  have hdk : d lam k ≤ n - 2 := Nat.sInf_le (Set.mem_setOf.2 (le_trans hklen hle))
  omega

end KnotGame
