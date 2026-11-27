import Mathlib.Combinatorics.SimpleGraph.Diam

namespace Graffiti

variable {V : Type*}

/-- The eccentricity of the *set* of graph centers: the least distance within
which the centers cover the graph. For finite connected graphs this is the
maximum, over vertices, of their minimum distance to a center. -/
noncomputable def centerDepth (G : SimpleGraph V) : ℕ :=
  sInf {r : ℕ | ∀ v, ∃ c ∈ G.center, G.dist c v ≤ r}

theorem centerDepth_le {G : SimpleGraph V} {r : ℕ} (h : ∀ v, ∃ c ∈ G.center, G.dist c v ≤ r) :
    centerDepth G ≤ r := Nat.sInf_le h

end Graffiti
