import Graffiti416
import Graffiti434

namespace Graffiti

open SimpleGraph Finset

variable {V : Type*} [Fintype V] (T : SimpleGraph V) [DecidableRel T.Adj]

/-- Isolated vertices of the subgraph induced by all vertices of maximum degree. -/
def isolatedMaxVertices [DecidableEq V] : Finset V := isolatesIn T (maxVertices T)

/-- A star of equal maximum-degree branches. Only the hub and the specified
branch centers may have degree greater than one; the hub has smaller degree. -/
structure MaxLeafStar (I : Finset V) (r : V) : Prop where
  outside : r ∉ I
  inhabited : I.Nonempty
  adjacent : ∀ i ∈ I, T.Adj r i
  maximum : ∀ i ∈ I, T.degree i = T.maxDegree
  hub_lt : T.degree r < T.maxDegree
  leaves : ∀ x, x ∉ I → x ≠ r → T.degree x = 1

end Graffiti
