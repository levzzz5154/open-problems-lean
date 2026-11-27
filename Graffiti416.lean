import Graffiti.Critical
import Mathlib.Combinatorics.SimpleGraph.Diam

/-! # Graffiti.pc 416, without the subtractive constant

For a connected graph of diameter at most two, an isolate in the graph induced
by the second neighborhood of the pendants is itself pendant. All pendants
belong to the union of the maximum critical independent sets.
The same strengthening and a prior Lean proof appear in Evan Dash Rust's
Graffiti batch: https://github.com/EvanDashRust/Conjecture-Killers/tree/main/Results/GraffitiBatch
https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json
-/

namespace Graffiti

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def isolatesIn (s : Finset V) : Finset V := s.filter fun v => ∀ w ∈ s, ¬G.Adj v w

omit [DecidableRel G.Adj] in
private theorem universal_pendant_neighbor (hG : G.Connected) (hd : G.diam ≤ 2) {x c : V}
    (ha : G.Adj x c) (hu : ∀ w, G.Adj x w → w = c) {v : V} (hv : v ≠ c) : G.Adj c v := by
  by_cases he : x = v
  · rw [← he]; exact ha.symm
  haveI : Nonempty V := hG.nonempty
  have hbound : G.dist x v ≤ 2 := (dist_le_diam (connected_iff_ediam_ne_top.mp hG)).trans hd
  obtain ⟨p,hp⟩ := hG.exists_walk_length_eq_dist x v
  have hn : ¬p.Nil := Walk.not_nil_of_ne he
  have hs : p.snd = c := hu _ (p.adj_snd hn)
  have hlen := p.length_tail_add_one hn
  have hp0 : p.tail.length ≠ 0 := fun h => hv ((p.tail.eq_of_length_eq_zero h).symm.trans hs)
  have hadj := p.tail.adj_of_length_eq_one (show p.tail.length = 1 by omega)
  exact hs ▸ hadj

theorem second_pendant_isolates_subset (hG : G.Connected) (hd : G.diam ≤ 2) :
    isolatesIn G (neighborhood G (neighborhood G (pendantVertices G))) ⊆ pendantVertices G := by
  intro v hv
  obtain ⟨hvN, hIso⟩ := mem_filter.mp hv
  obtain ⟨c,hc,ha⟩ := mem_neighborhood_iff.mp hvN
  obtain ⟨x,hx,hcx⟩ := mem_neighborhood_iff.mp hc
  obtain ⟨z,_,hz⟩ := pendant_neighbor G hx
  have he := hz c hcx.symm
  subst z
  have hNb : G.neighborFinset v = {c} := by
    ext w
    rw [mem_neighborFinset, mem_singleton]
    constructor
    · intro h
      by_contra hne
      have hw := universal_pendant_neighbor G hG hd hcx.symm hz hne
      exact hIso w (mem_neighborhood_iff.mpr ⟨c,hc,hw.symm⟩) h
    · rintro rfl; exact ha
  exact mem_filter.mpr ⟨mem_univ _, by rw [← card_neighborFinset_eq_degree, hNb, card_singleton]⟩

/-- The original statement subtracts two from the left side; neither that loss
nor the restriction to graphs of order greater than two is needed. -/
theorem conjecture416 (hG : G.Connected) (hd : G.diam ≤ 2) :
    (isolatesIn G (neighborhood G (neighborhood G (pendantVertices G)))).card ≤ (criticalHull G).card :=
  card_le_card ((second_pendant_isolates_subset G hG hd).trans (pendants_subset_criticalHull G))

end Graffiti
