import RequestProject.PlasticIndex

/-!
# A search tree of index configurations

To certify Proposition 9 at the plastic number we exhibit an explicit finite
set `V` of index configurations, each node carrying

* a key (the encoding `encCfg` of its configuration),
* the configuration itself,
* a tag (its breadth-first depth),
* a move and a configuration witnessing how it arises from a configuration of
  smaller tag.

`PlasticConfig.lean` then checks by kernel computation that the tree is closed
under the three moves with tags growing by at most one, that every member has
at most seven indices with a tag at least the record depth of its size, that
every member is reached from the empty configuration by its recorded parent,
and that the tree is correctly keyed and ordered.

Nothing about the shape of the tree is *assumed*: lookups compare the stored
configuration honestly, so a badly shaped tree can only make a lookup fail.
The ordering check `Tbl.ok` is needed only in the converse direction, to know
that every stored configuration *can* be found.
-/

namespace KnotGame
namespace Plastic

/-- A node carries: key, configuration, depth tag, the move producing it, the
parent configuration, and the two subtrees. -/
inductive Tbl where
  | leaf : Tbl
  | node : ℕ → List ℕ → ℕ → ℕ → List ℕ → Tbl → Tbl → Tbl

/-- The key of a configuration: one byte per index, shifted by one so that the
empty configuration is the only one with key `0`. -/
def encCfg : List ℕ → ℕ
  | [] => 0
  | i :: c => (i + 1) + 256 * encCfg c

/-- `t.findLe k c b` looks the key `k` up in `t` and succeeds if the node found
carries the configuration `c` with a tag at most `b`. -/
def Tbl.findLe : Tbl → ℕ → List ℕ → ℕ → Bool
  | .leaf, _, _, _ => false
  | .node k c d _ _ l r, k', c', b =>
      if k' < k then l.findLe k' c' b
      else if k < k' then r.findLe k' c' b
      else decide (c' = c) && decide (d ≤ b)

/-- `t.all p` tests `p` at every node of `t`, on its configuration, tag, move
and parent configuration. -/
def Tbl.all (p : List ℕ → ℕ → ℕ → List ℕ → Bool) : Tbl → Bool
  | .leaf => true
  | .node _ c d pm pc l r => p c d pm pc && Tbl.all p l && Tbl.all p r

/-- Anything found in a tree satisfies, at some node data with tag below the
search bound, every predicate that holds throughout the tree. -/
lemma Tbl.all_of_findLe {p : List ℕ → ℕ → ℕ → List ℕ → Bool} (t : Tbl) (hall : t.all p = true)
    {k : ℕ} {c : List ℕ} {b : ℕ} (h : t.findLe k c b = true) :
    ∃ d ≤ b, ∃ pm pc, p c d pm pc = true := by
  induction t with
  | leaf => simp [Tbl.findLe] at h
  | node k0 c0 d0 pm0 pc0 l r ihl ihr =>
      simp only [Tbl.all, Bool.and_eq_true] at hall
      simp only [Tbl.findLe] at h
      split at h
      · exact ihl hall.1.2 h
      · split at h
        · exact ihr hall.2 h
        · rw [Bool.and_eq_true] at h
          have hc : c = c0 := of_decide_eq_true h.1
          subst hc
          exact ⟨d0, of_decide_eq_true h.2, pm0, pc0, hall.1.1⟩

/-- Lookups are monotone in the tag bound. -/
lemma Tbl.findLe_mono (t : Tbl) {k : ℕ} {c : List ℕ} {b b' : ℕ} (hb : b ≤ b')
    (h : t.findLe k c b = true) : t.findLe k c b' = true := by
  induction t with
  | leaf => simp [Tbl.findLe] at h
  | node k0 c0 d0 pm0 pc0 l r ihl ihr =>
      simp only [Tbl.findLe] at h ⊢
      by_cases h1 : k < k0
      · rw [if_pos h1] at h ⊢
        exact ihl h
      · rw [if_neg h1] at h ⊢
        by_cases h2 : k0 < k
        · rw [if_pos h2] at h ⊢
          exact ihr h
        · rw [if_neg h2] at h ⊢
          rw [Bool.and_eq_true] at h ⊢
          exact ⟨h.1, decide_eq_true (le_trans (of_decide_eq_true h.2) hb)⟩

/-! ## The contents of a tree -/

/-- The configurations stored in a tree, in order. -/
def Tbl.toList : Tbl → List (List ℕ)
  | .leaf => []
  | .node _ c _ _ _ l r => l.toList ++ c :: r.toList

/-- The number of nodes, computed without building the list. -/
def Tbl.size : Tbl → ℕ
  | .leaf => 0
  | .node _ _ _ _ _ l r => l.size + 1 + r.size

lemma Tbl.length_toList (t : Tbl) : t.toList.length = t.size := by
  induction t with
  | leaf => rfl
  | node k c d pm pc l r ihl ihr =>
      simp [Tbl.toList, Tbl.size, ihl, ihr]
      omega

lemma Tbl.mem_toList_of_findLe (t : Tbl) {k : ℕ} {c : List ℕ} {b : ℕ}
    (h : t.findLe k c b = true) : c ∈ t.toList := by
  induction t with
  | leaf => simp [Tbl.findLe] at h
  | node k0 c0 d0 pm0 pc0 l r ihl ihr =>
      simp only [Tbl.findLe] at h
      simp only [Tbl.toList, List.mem_append, List.mem_cons]
      split at h
      · exact Or.inl (ihl h)
      · split at h
        · exact Or.inr (Or.inr (ihr h))
        · rw [Bool.and_eq_true] at h
          exact Or.inr (Or.inl (of_decide_eq_true h.1))

/-! ## Well-formedness of the tree -/

/-- The key is above the (optional) lower bound. -/
def boundLo : Option ℕ → ℕ → Bool
  | none, _ => true
  | some lo, k => decide (lo < k)

/-- The key is below the (optional) upper bound. -/
def boundHi : Option ℕ → ℕ → Bool
  | none, _ => true
  | some hi, k => decide (k < hi)

/-- `t.ok lo hi` checks that `t` is a search tree with keys strictly between
`lo` and `hi`, each node's key being the encoding of its configuration. -/
def Tbl.ok : Tbl → Option ℕ → Option ℕ → Bool
  | .leaf, _, _ => true
  | .node k c _ _ _ l r, lo, hi =>
      boundLo lo k && boundHi hi k && decide (k = encCfg c) &&
        l.ok lo (some k) && r.ok (some k) hi

lemma Tbl.pairwise_of_ok : ∀ (t : Tbl) (lo hi : Option ℕ), t.ok lo hi = true →
    List.Pairwise (· < ·) (t.toList.map encCfg) ∧
      ∀ x ∈ t.toList, boundLo lo (encCfg x) = true ∧ boundHi hi (encCfg x) = true
  | .leaf, _, _, _ => by simp [Tbl.toList]
  | .node k c d pm pc l r, lo, hi, h => by
      simp only [Tbl.ok, Bool.and_eq_true] at h
      obtain ⟨⟨⟨⟨hlo, hhi⟩, hkey⟩, hl⟩, hr⟩ := h
      have hk : k = encCfg c := of_decide_eq_true hkey
      obtain ⟨hsl, hbl⟩ := Tbl.pairwise_of_ok l lo (some k) hl
      obtain ⟨hsr, hbr⟩ := Tbl.pairwise_of_ok r (some k) hi hr
      constructor
      · simp only [Tbl.toList, List.map_append, List.map_cons]
        rw [List.pairwise_append]
        refine ⟨hsl, ?_, ?_⟩
        · rw [List.pairwise_cons]
          refine ⟨?_, hsr⟩
          intro b hb
          simp only [List.mem_map] at hb
          obtain ⟨y, hy, rfl⟩ := hb
          have := (hbr y hy).1
          simp only [boundLo, decide_eq_true_eq] at this
          omega
        · intro a ha b hb
          simp only [List.mem_map] at ha
          obtain ⟨x, hx, rfl⟩ := ha
          have hxk := (hbl x hx).2
          simp only [boundHi, decide_eq_true_eq] at hxk
          simp only [List.mem_cons, List.mem_map] at hb
          rcases hb with rfl | hb
          · omega
          · obtain ⟨y, hy, rfl⟩ := hb
            have := (hbr y hy).1
            simp only [boundLo, decide_eq_true_eq] at this
            omega
      · intro x hx
        simp only [Tbl.toList, List.mem_append, List.mem_cons] at hx
        rcases hx with hx | rfl | hx
        · exact ⟨(hbl x hx).1, by
            have h1 := (hbl x hx).2
            simp only [boundHi, decide_eq_true_eq] at h1
            cases hi with
            | none => simp [boundHi]
            | some hv =>
                simp only [boundHi, decide_eq_true_eq] at hhi ⊢
                omega⟩
        · exact ⟨by rw [← hk]; exact hlo, by rw [← hk]; exact hhi⟩
        · exact ⟨by
            have h1 := (hbr x hx).1
            simp only [boundLo, decide_eq_true_eq] at h1
            cases lo with
            | none => simp [boundLo]
            | some lv =>
                simp only [boundLo, decide_eq_true_eq] at hlo ⊢
                omega, (hbr x hx).2⟩

/-- In a well-formed tree, every stored configuration can be found. -/
lemma Tbl.findLe_of_mem_toList : ∀ (t : Tbl) (lo hi : Option ℕ), t.ok lo hi = true →
    ∀ {c : List ℕ}, c ∈ t.toList → ∃ n, t.findLe (encCfg c) c n = true
  | .leaf, _, _, _, _, h => by simp [Tbl.toList] at h
  | .node k c0 d pm pc l r, lo, hi, h, c, hc => by
      simp only [Tbl.ok, Bool.and_eq_true] at h
      obtain ⟨⟨⟨⟨hlo, hhi⟩, hkey⟩, hl⟩, hr⟩ := h
      have hk : k = encCfg c0 := of_decide_eq_true hkey
      simp only [Tbl.toList, List.mem_append, List.mem_cons] at hc
      rcases hc with hc | rfl | hc
      · obtain ⟨n, hn⟩ := Tbl.findLe_of_mem_toList l lo (some k) hl hc
        refine ⟨n, ?_⟩
        have hlt : encCfg c < k := by
          have := ((Tbl.pairwise_of_ok l lo (some k) hl).2 c hc).2
          simpa [boundHi] using this
        simp only [Tbl.findLe, if_pos hlt]
        exact hn
      · exact ⟨d, by rw [← hk]; simp [Tbl.findLe]⟩
      · obtain ⟨n, hn⟩ := Tbl.findLe_of_mem_toList r (some k) hi hr hc
        refine ⟨n, ?_⟩
        have hgt : k < encCfg c := by
          have := ((Tbl.pairwise_of_ok r (some k) hi hr).2 c hc).1
          simpa [boundLo] using this
        simp only [Tbl.findLe, if_neg (by omega : ¬ encCfg c < k), if_pos hgt]
        exact hn

end Plastic
end KnotGame
