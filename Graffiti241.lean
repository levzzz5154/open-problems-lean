import Graffiti434d
import Graffiti.TreeCenters
import Graffiti258
import Graffiti450

/-! # Written on the Wall II, Graffiti.pc 241

This row cites definition **61**: average the nonzero distances *between*
center vertices. Definition 109 (distances *to a set*) is different. Distinct
tree centers are adjacent, so the average, when defined, is exactly one.
For any vertex set in any graph a total dominating set is strictly larger
than the number of components induced by that set's closed neighborhood.

https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json
https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/definitions.json
-/

namespace Graffiti

open Finset SimpleGraph SupportCounting

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

noncomputable def closedComponentCount (S : Finset V) : ℕ :=
  Nat.card (G.induce (closedNeighborhood G S : Set V)).ConnectedComponent

/-- A neighboring dominator of each component seed gives an injection into
`D`. It is not onto: distinct image vertices are never adjacent, whereas `D`
must contain an edge. No tree, connectivity or degree assumptions. -/
theorem closed_components_lt_total_set [Nonempty V] (S : Finset V) {D : Finset V}
    (hd : TotallyDominates G D) : closedComponentCount G S < D.card := by
  classical
  let K := (G.induce (closedNeighborhood G S : Set V)).ConnectedComponent
  letI : Fintype K := Fintype.ofFinite _
  obtain ⟨b,_,sep⟩ := closed_component_packing G S
  obtain ⟨o⟩ := ‹Nonempty V›
  obtain ⟨a,ha,_⟩ := hd o
  obtain ⟨z,hz,e⟩ := hd a
  choose f hf he using hd
  let F (c : K) : ↥D := ⟨f (b c),hf _⟩
  have near (c : K) : InZone G (b c) (F c).val := Or.inr (he _)
  have inj : Function.Injective F := by
    intro i j h; by_contra ne
    exact (sep ne (near i) (near j)).1 (congrArg Subtype.val h)
  have missing : ¬Function.Surjective F := by
    intro on
    obtain ⟨i,hi⟩ := on ⟨a,ha⟩
    obtain ⟨j,hj⟩ := on ⟨z,hz⟩
    have adj : G.Adj (F i).val (F j).val := by rw [hi,hj]; exact e
    have ne : i ≠ j := fun eq => adj.ne (congrArg (fun c => (F c).val) eq)
    exact (sep ne (near i) (near j)).2 adj
  calc closedComponentCount G S = Fintype.card K := Nat.card_eq_fintype_card
       _ < Fintype.card ↥D := Fintype.card_lt_of_injective_not_surjective F inj missing
       _ = D.card := Fintype.card_coe _

/-- Ordered distinct pairs; reversing every pair does not change the mean. -/
noncomputable def distinctCenterPairs : Finset (V × V) := by
  classical exact univ.filter fun p => p.1 ∈ G.center ∧ p.2 ∈ G.center ∧ p.1 ≠ p.2

theorem tree_center_pair_sum (ht : G.IsTree) :
    (∑ p ∈ distinctCenterPairs G, G.dist p.1 p.2) = (distinctCenterPairs G).card := by
  classical
  calc _ = ∑ _ ∈ distinctCenterPairs G, 1 := by
          apply sum_congr rfl; intro p hp
          obtain ⟨ha,hb,ne⟩ := (mem_filter.mp hp).2
          exact dist_eq_one_iff_adj.mpr (tree_center_adj ht ha hb ne)
       _ = _ := by simp

/-- Floor of the mean is expressed by natural division. An empty sample
(single center) gives zero under this explicit convention. The stronger
component bound also covers that case if the mean is left undefined. -/
theorem graffiti241 [Nontrivial V] [DecidableRel G.Adj] (ht : G.IsTree) :
    closedComponentCount G (degreeClass G 2) +
      (∑ p ∈ distinctCenterPairs G, G.dist p.1 p.2) / (distinctCenterPairs G).card ≤ totalDominationNumber G := by
  obtain ⟨D,hd,hm⟩ := exists_min_total_set ht.isConnected
  have lt := closed_components_lt_total_set G (degreeClass G 2) hd
  rw [tree_center_pair_sum G ht]
  by_cases h : (distinctCenterPairs G).card = 0
  · simp only [h,Nat.zero_div,Nat.add_zero]; omega
  · rw [Nat.div_self (Nat.pos_of_ne_zero h)]; omega

end Graffiti
