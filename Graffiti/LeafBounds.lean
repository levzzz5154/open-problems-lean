import Graffiti.LeafCount
import Graffiti.SpanningArms
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! # Spanning leaves, vertex degrees, and connected domination -/

namespace Graffiti

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [Nontrivial V]

theorem degree_pos_of_connected {G : SimpleGraph V} [DecidableRel G.Adj]
    (hc : G.Connected) (v : V) : 0 < G.degree v := by
  obtain ⟨x, hx⟩ := exists_ne v
  obtain ⟨w⟩ := hc.preconnected v x
  cases w with
  | nil => exact False.elim (hx rfl)
  | cons ha _ => exact (G.degree_pos_iff_exists_adj v).mpr ⟨_, ha⟩

/-- In a nontrivial tree every vertex accounts for at least two units of
`degree + leaf indicator`.  Retain the contribution of a specified vertex. -/
theorem tree_leaf_bounds {T : SimpleGraph V} [DecidableRel T.Adj]
    (ht : T.IsTree) (v : V) : max 2 (T.degree v) ≤ (pendantVertices T).card := by
  classical
  let f (x : V) := T.degree x + (if T.degree x = 1 then 1 else 0)
  have hf (x : V) : 2 ≤ f x := by
    have hp := degree_pos_of_connected ht.isConnected x
    dsimp [f]; split <;> omega
  have hsum : ∑ x, f x = 2 * T.edgeFinset.card + (pendantVertices T).card := by
    simp [f, sum_add_distrib, T.sum_degrees_eq_twice_card_edges, pendantVertices]
  have hsmall := Finset.sum_le_sum (s := (univ : Finset V).erase v) (fun x _ => hf x)
  have hcard := card_erase_add_one (mem_univ v)
  have hsplit := (univ : Finset V).add_sum_erase f (mem_univ v)
  have hrest : 2 * (univ.erase v).card ≤ ∑ x ∈ univ.erase v, f x := by
    simpa [Nat.mul_comm] using hsmall
  rw [card_univ] at hcard
  have he := ht.card_edgeFinset
  have hv := hf v
  have hv' : T.degree v ≤ f v := Nat.le_add_right ..
  omega

theorem two_le_maxLeafCount {G : SimpleGraph V} (hc : G.Connected) : 2 ≤ maxLeafCount G := by
  classical
  obtain ⟨T,hTG,ht⟩ := hc.exists_isTree_le
  let v : V := Classical.choice hc.nonempty
  exact (le_max_left 2 (T.degree v)).trans ((tree_leaf_bounds ht v).trans (leaves_le_maxLeafCount hTG ht))

theorem degree_le_maxLeafCount {G : SimpleGraph V} [DecidableRel G.Adj]
    (hc : G.Connected) (v : V) : G.degree v ≤ maxLeafCount G := by
  classical
  obtain ⟨T,hTG,ht,hs⟩ := tree_with_star G hc v
  have hdeg : G.degree v ≤ T.degree v := card_le_card (show G.neighborFinset v ⊆ T.neighborFinset v from
    fun x hx => (T.mem_neighborFinset v x).mpr (hs x ((G.mem_neighborFinset v x).mp hx)))
  exact hdeg.trans ((le_max_right 2 (T.degree v)).trans ((tree_leaf_bounds ht v).trans
    (leaves_le_maxLeafCount hTG ht)))

theorem pendants_le_maxLeafCount {G : SimpleGraph V} [DecidableRel G.Adj]
    (hc : G.Connected) : (pendantVertices G).card ≤ maxLeafCount G := by
  classical
  obtain ⟨T,hTG,ht⟩ := hc.exists_isTree_le
  apply le_trans (Finset.card_le_card (t := pendantVertices T) ?_) (leaves_le_maxLeafCount hTG ht)
  intro x hx
  have h₁ : G.degree x = 1 := (mem_filter.mp hx).2
  have h₂ := T.degree_le_of_le (v := x) hTG
  have h₃ := degree_pos_of_connected ht.isConnected x
  exact mem_filter.mpr ⟨mem_univ _, by omega⟩

/-- Attach each vertex outside the connected dominating set by just one edge.
Taking a spanning tree of the resulting connected graph preserves those leaves. -/
theorem order_le_connected_dominating_add_leaves {G : SimpleGraph V} {C : Finset V}
    (hc : (G.induce (C : Set V)).Connected) (hd : TotallyDominates G C) :
    Fintype.card V ≤ C.card + maxLeafCount G := by
  classical
  choose f hf ha using hd
  let H : SimpleGraph V :=
    { Adj := fun x y => G.Adj x y ∧ (x ∈ C ∨ y = f x) ∧ (y ∈ C ∨ x = f y)
      symm := fun _ _ ⟨h,hx,hy⟩ => ⟨h.symm,hy,hx⟩
      loopless := fun x h => G.loopless x h.1 }
  let incl : G.induce (C : Set V) →g H :=
    { toFun := Subtype.val
      map_rel' := fun {x y} h => ⟨h,Or.inl x.property,Or.inl y.property⟩ }
  let r := Classical.choice hc.nonempty
  have hcore (x : V) (hx : x ∈ C) : H.Reachable r.val x := (hc.preconnected r ⟨x,hx⟩).map incl
  have hcon : H.Connected := by
    apply (connected_iff_exists_forall_reachable H).mpr
    refine ⟨r.val, fun x => ?_⟩
    exact (hcore _ (hf x)).trans (show H.Adj x (f x) from ⟨ha x, Or.inr rfl, Or.inl (hf _)⟩).symm.reachable
  obtain ⟨T,hTH,ht⟩ := hcon.exists_isTree_le
  have hTG : T ≤ G := fun _ _ h => (hTH h).1
  have hout : Cᶜ ⊆ pendantVertices T := by
    intro x hx
    have hx' := mem_compl.mp hx
    have hsub : T.neighborFinset x ⊆ {f x} := by
      intro y hy
      exact mem_singleton.mpr ((hTH ((T.mem_neighborFinset x y).mp hy)).2.1.resolve_left hx')
    have hlo := degree_pos_of_connected ht.isConnected x
    have hhi : T.degree x ≤ 1 := (card_le_card hsub).trans_eq (card_singleton _)
    exact mem_filter.mpr ⟨mem_univ _, by omega⟩
  have hcount := (card_le_card hout).trans (leaves_le_maxLeafCount hTG ht)
  have hpart := card_add_card_compl C
  omega

end Graffiti
