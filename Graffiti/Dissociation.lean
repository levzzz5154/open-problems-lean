import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Powerset

/-! # Maximum order of an induced subgraph of degree at most one

This is the 2-independence number in definition 118 of *Written on the Wall II*.
-/

namespace Graffiti

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def withinDegree (s : Finset V) (v : V) : ℕ := (s.filter (G.Adj v)).card

def Dissociated (s : Finset V) : Prop := ∀ v ∈ s, withinDegree G s v ≤ 1

instance (s : Finset V) : Decidable (Dissociated G s) :=
  inferInstanceAs (Decidable (∀ v ∈ s, withinDegree G s v ≤ 1))

def dissociationNumber : ℕ := (univ.filter (Dissociated G)).sup card

theorem le_dissociationNumber {s : Finset V} (hs : Dissociated G s) : s.card ≤ dissociationNumber G :=
  le_sup (mem_filter.mpr ⟨mem_univ _, hs⟩)

theorem dissociationNumber_le {n : ℕ} (h : ∀ s, Dissociated G s → s.card ≤ n) :
    dissociationNumber G ≤ n := Finset.sup_le fun s hs => h s (mem_filter.mp hs).2

def highVertices : Finset V := univ.filter fun v => 3 ≤ G.degree v

end Graffiti
