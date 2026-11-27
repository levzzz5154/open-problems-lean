import Graffiti.HighDegreeBudget
import Graffiti.UpperDegreeMedian

/-! # Written on the Wall II, Graffiti.pc 377

The strict majority threshold counts vertices with multiplicity. In the only
case where the isolated maximum-degree vertices leave just one extra slot,
a strict majority are leaves, so the upper median fits that slot.
https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json
-/

namespace Graffiti

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj]

theorem graffiti377 (ht : T.IsTree) (hn : 2 < Fintype.card V) :
    (isolatedMaxVertices T).card + upperDegreeMedian T ≤ totalDominationNumber T := by
  rcases isolated_max_dichotomy T ht hn with h | ⟨r,shape,eq⟩
  · have := upperDegreeMedian_tree_le_two ht hn; omega
  · have := upperDegreeMedian_maxLeafStar_le_one ht hn shape; omega

end Graffiti
