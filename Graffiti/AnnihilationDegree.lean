import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Powerset

/-! # The annihilation number of a finite graph -/

namespace Graffiti

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Maximum cardinality of a set of vertices whose degrees sum to at most the edge count. -/
def annihilationNumber : ℕ :=
  ((univ : Finset (Finset V)).filter fun D => ∑ v ∈ D, G.degree v ≤ G.edgeFinset.card).sup card

omit [DecidableEq V] in
theorem card_le_annihilationNumber {D : Finset V} (h : ∑ v ∈ D, G.degree v ≤ G.edgeFinset.card) :
    D.card ≤ annihilationNumber G :=
  le_sup (mem_filter.mpr ⟨mem_univ _, h⟩)

/-- Split the vertices into two nearly equal parts. By the degree-sum formula,
 at least one part has degree sum at most the edge count. -/
theorem half_order_le_annihilationNumber : Fintype.card V / 2 ≤ annihilationNumber G := by
  have hs : Fintype.card V / 2 ≤ (univ : Finset V).card := by rw [card_univ]; omega
  obtain ⟨D, _, hD⟩ := exists_subset_card_eq hs
  by_cases h : ∑ v ∈ D, G.degree v ≤ G.edgeFinset.card
  · exact hD ▸ card_le_annihilationNumber G h
  · have hsum := D.sum_add_sum_compl (fun v => G.degree v)
    rw [G.sum_degrees_eq_twice_card_edges] at hsum
    have hcompl : ∑ v ∈ Dᶜ, G.degree v ≤ G.edgeFinset.card := by omega
    apply le_trans _ (card_le_annihilationNumber G hcompl)
    rw [card_compl, hD]
    omega

end Graffiti
