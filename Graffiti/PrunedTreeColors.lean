import Graffiti342

namespace Graffiti
open SimpleGraph Finset SupportCounting

private theorem split_tree {V : Type*} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} [DecidableRel T.Adj] (ht : T.IsTree) :
    ∃ K : Finset V, ∀ x, 2 ≤ T.degree x →
      (∃ a ∈ K, T.Adj x a) ∧ (∃ b ∉ K, T.Adj x b) := by
  classical
  cases subsingleton_or_nontrivial V with
  | inl hs =>
    refine ⟨∅, fun x hd => False.elim ?_⟩
    obtain ⟨y,hy⟩ := (T.degree_pos_iff_exists_adj x).mp (by omega)
    exact hy.ne (Subsingleton.elim _ _)
  | inr hn =>
    obtain ⟨v⟩ := ht.isConnected.nonempty
    have h := tree_leaf_bounds ht v
    obtain ⟨r,hr⟩ := card_pos.mp (show 0 < (pendantVertices T).card by omega)
    have dr : T.degree r = 1 := (mem_filter.mp hr).2
    let K := univ.filter fun a => T.dist a r % 4 < 2
    refine ⟨K, fun x hd => ?_⟩
    have hx : x ≠ r := fun e => by rw [e,dr] at hd; omega
    obtain ⟨a,b,ea,eb,da,db⟩ := exists_straddling_neighbors ht hx hd
    have key : a ∈ K ↔ b ∉ K := by simp only [K,mem_filter,mem_univ,true_and]; omega
    by_cases hk : a ∈ K
    · exact ⟨⟨a,hk,ea⟩,⟨b,key.mp hk,eb⟩⟩
    · exact ⟨⟨b,by by_contra h'; exact hk (key.mpr h'),eb⟩,⟨a,hk,ea⟩⟩

/-- Restrict to surviving edges and color each remaining tree independently. -/
theorem split_after_pruning {V : Type*} [Fintype V] [DecidableEq V] {T : SimpleGraph V}
    [DecidableRel T.Adj] (ht : T.IsTree) (R : Finset V) :
    ∃ K : Finset V, ∀ x ∉ R, 2 ≤ (T.neighborFinset x \ R).card →
      (∃ a ∉ R, a ∈ K ∧ T.Adj x a) ∧ (∃ b ∉ R, b ∉ K ∧ T.Adj x b) := by
  classical
  let H : SimpleGraph V := {
    Adj := fun x y => T.Adj x y ∧ x ∉ R ∧ y ∉ R
    symm := fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩
    loopless := fun _ h => h.1.ne rfl }
  have parts (c : H.ConnectedComponent) := by
    let G := H.induce c.supp
    let f : G →g T := ⟨Subtype.val, fun h => h.1⟩
    have tree : G.IsTree := ⟨c.connected_induce_supp, fun _ p hp =>
      ht.IsAcyclic (p.map f) ((Walk.map_isCycle_iff_of_injective (f := f) Subtype.val_injective).2 hp)⟩
    exact split_tree tree
  choose colors spec using parts
  let K := univ.filter fun z => ∃ (c : H.ConnectedComponent) (hz : z ∈ c.supp), ⟨z,hz⟩ ∈ colors c
  have agree (c : H.ConnectedComponent) (z : c.supp) : z.val ∈ K ↔ z ∈ colors c := by
    simp only [K,mem_filter,mem_univ,true_and]
    constructor
    · rintro ⟨d,hd,h⟩
      have e : c = d := ((c.mem_supp_iff _).mp z.property).symm.trans hd
      cases e; exact h
    · exact fun h => ⟨c,z.property,h⟩
  refine ⟨K, fun x hx hd => ?_⟩
  let c := H.connectedComponentMk x
  let u : c.supp := ⟨x,rfl⟩
  have eq : H.neighborFinset x = T.neighborFinset x \ R := by
    ext z; simp [mem_neighborFinset,H,hx]
  have deg : 2 ≤ (H.induce c.supp).degree u := by
    rw [degree_induce_of_neighborSet_subset]
    · change 2 ≤ (H.neighborFinset x).card
      rwa [eq]
    · exact fun z hz => (c.mem_supp_congr_adj hz).mp u.property
  obtain ⟨⟨a,ha,ea⟩,⟨b,hb,eb⟩⟩ := spec c u deg
  exact ⟨⟨a,ea.2.2,(agree c a).2 ha,ea.1⟩,⟨b,eb.2.2,fun h => hb ((agree c b).1 h),eb.1⟩⟩

end Graffiti
