import Graffiti315
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Lattice.Fold

namespace Graffiti

open Finset SimpleGraph

variable {V : Type*} [Fintype V]

/-- Maximum number of degree-one vertices over the spanning trees of `G`. -/
noncomputable def maxLeafCount (G : SimpleGraph V) : ℕ := by
  classical
  exact ((univ : Finset (SimpleGraph V)).filter (fun T => T ≤ G ∧ T.IsTree)).sup
    (fun T => (pendantVertices T).card)

theorem leaves_le_maxLeafCount {G T : SimpleGraph V} [inst : DecidableRel T.Adj]
    (hTG : T ≤ G) (hT : T.IsTree) : (pendantVertices T).card ≤ maxLeafCount G := by
  classical
  rw [show inst = Classical.decRel T.Adj from Subsingleton.elim _ _]
  unfold maxLeafCount
  apply Finset.le_sup (b := T)
  exact mem_filter.mpr ⟨mem_univ _, hTG, hT⟩

end Graffiti
