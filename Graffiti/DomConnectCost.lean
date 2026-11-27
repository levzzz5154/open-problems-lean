import Graffiti315
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-! # Connecting a total dominating set

A vertex of the dominating set adjacent to the current connected set is free to
attach. When no such vertex remains available, two connector vertices suffice
to attach a new adjacent pair from the dominating set.
-/

namespace Graffiti

open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V}

theorem connected_insert_neighbor [DecidableEq V] {C : Finset V} {c x : V}
    (hC : (G.induce (C : Set V)).Connected) (hc : c ∈ C) (hcx : G.Adj c x) :
    (G.induce (↑(insert x C) : Set V)).Connected := by
  have heq : (↑(insert x C) : Set V) = (C : Set V) ∪ {c, x} := by
    ext z
    simp only [Finset.mem_coe, Finset.mem_insert, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    aesop
  rw [heq]
  exact induce_union_connected hC (induce_pair_connected_of_adj hcx) ⟨c, hc, by simp⟩

private theorem exists_crossing_edge {P : V → Prop} {s t : V}
    (hst : G.Reachable s t) (hs : P s) (ht : ¬P t) :
    ∃ x y, P x ∧ ¬P y ∧ G.Adj x y := by
  classical
  by_contra hn
  apply ht
  have hr := (reachable_iff_reflTransGen (G := G) s t).mp hst
  clear ht hst
  induction hr with
  | refl => exact hs
  | tail _ hxy ih => exact of_not_not fun hy => hn ⟨_, _, ih, hy, hxy⟩

/-- A growth step: adding at most one vertex gains one member of `D`, or
adding at most four vertices gains at least two members of `D`. -/
private theorem grow_dom_set [DecidableEq V] {C D : Finset V}
    (hG : G.Connected) (hD : TotallyDominates G D)
    (hC : (G.induce (C : Set V)).Connected) (hmiss : ¬D ⊆ C) :
    ∃ C' : Finset V, (G.induce (C' : Set V)).Connected ∧
      ((C'.card ≤ C.card + 1 ∧ (C ∩ D).card + 1 ≤ (C' ∩ D).card) ∨
       (C'.card ≤ C.card + 4 ∧ (C ∩ D).card + 2 ≤ (C' ∩ D).card)) := by
  classical
  by_cases hfree : ∃ d ∈ D, d ∉ C ∧ ∃ c ∈ C, G.Adj c d
  · obtain ⟨d, hd, hdC, c, hc, hcd⟩ := hfree
    refine ⟨insert d C, connected_insert_neighbor hC hc hcd, Or.inl ⟨card_insert_le _ _, ?_⟩⟩
    rw [insert_inter_of_mem hd, card_insert_of_not_mem (fun h => hdC (mem_inter.mp h).1)]
  obtain ⟨t, htD, htC⟩ := Finset.not_subset.mp hmiss
  let P (v : V) := ∃ c ∈ C, G.Adj c v
  have ht : ¬P t := fun h => hfree ⟨t, htD, htC, h⟩
  obtain ⟨⟨s, hs⟩⟩ := hC.nonempty
  obtain ⟨z, _, hsz⟩ := hD s
  obtain ⟨x, y, ⟨c, hc, hcx⟩, hy, hxy⟩ :=
    exists_crossing_edge (P := P) (hG z t) ⟨s, hs, hsz⟩ ht
  obtain ⟨d, hd, hyd⟩ := hD y
  have hdC : d ∉ C := fun h => hy ⟨d, h, hyd.symm⟩
  obtain ⟨e, he, hde⟩ := hD d
  have heC : e ∉ C := fun h => hfree ⟨d, hd, hdC, e, h, hde.symm⟩
  let C' := insert e (insert d (insert y (insert x C)))
  have hx := connected_insert_neighbor hC hc hcx
  have hy' := connected_insert_neighbor hx (mem_insert_self _ _) hxy
  have hd' := connected_insert_neighbor hy' (mem_insert_self _ _) hyd
  refine ⟨C', connected_insert_neighbor hd' (mem_insert_self _ _) hde, Or.inr ⟨?_, ?_⟩⟩
  · dsimp [C']
    have := card_insert_le x C
    have := card_insert_le y (insert x C)
    have := card_insert_le d (insert y (insert x C))
    have := card_insert_le e (insert d (insert y (insert x C)))
    omega
  · have hsub : insert e (insert d (C ∩ D)) ⊆ C' ∩ D := by
      intro v hv
      rcases mem_insert.mp hv with rfl | hv
      · exact mem_inter.mpr ⟨mem_insert_self _ _, he⟩
      rcases mem_insert.mp hv with rfl | hv
      · exact mem_inter.mpr ⟨mem_insert_of_mem (mem_insert_self _ _), hd⟩
      obtain ⟨hvC, hvD⟩ := mem_inter.mp hv
      exact mem_inter.mpr ⟨by simp [C', hvC], hvD⟩
    have hcount := card_le_card hsub
    rw [card_insert_of_not_mem (by simp [hde.ne.symm, heC]),
      card_insert_of_not_mem (by simp [hdC])] at hcount
    exact hcount

/-- Every finite total dominating set in a connected graph has a connected
superset, with at most two connector vertices per pair after the first pair. -/
theorem exists_connected_total_superset {D : Finset V}
    (hG : G.Connected) (hD : TotallyDominates G D) :
    ∃ C : Finset V, D ⊆ C ∧ (G.induce (C : Set V)).Connected ∧
      C.card + 2 ≤ D.card + 2 * (D.card / 2) := by
  classical
  let rec grow (C : Finset V) (hC : (G.induce (C : Set V)).Connected)
      (hcost : C.card + 2 ≤ (C ∩ D).card + 2 * ((C ∩ D).card / 2)) :
      ∃ S : Finset V, D ⊆ S ∧ (G.induce (S : Set V)).Connected ∧
        S.card + 2 ≤ D.card + 2 * (D.card / 2) := by
    by_cases hdone : D ⊆ C
    · rw [inter_eq_right.mpr hdone] at hcost
      exact ⟨C, hdone, hC, hcost⟩
    obtain ⟨C', hconn, hstep⟩ := grow_dom_set hG hD hC hdone
    exact grow C' hconn (by rcases hstep with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
  termination_by letI := Classical.decEq V; D.card - (C ∩ D).card
  decreasing_by
    classical
    have hcap : (C' ∩ D).card ≤ D.card := card_le_card inter_subset_right
    rcases hstep with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
  obtain ⟨v⟩ := hG.nonempty
  obtain ⟨a, ha, _⟩ := hD v
  obtain ⟨b, hb, hab⟩ := hD a
  have hpair : ({a, b} : Finset V) ⊆ D := insert_subset ha (singleton_subset_iff.mpr hb)
  apply grow {a, b}
  · rw [Finset.coe_pair]
    exact induce_pair_connected_of_adj hab
  · rw [inter_eq_left.mpr hpair, card_pair hab.ne]

end Graffiti
