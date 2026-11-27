import Graffiti.CliqueFiber

/-! # Sharpness of the four-vertex cutoff in Theorem 2.10

The five high vertices are labelled by the vertices of an auxiliary pentagon;
there are no edges between the high vertices themselves. An independent set
in the low part uses at most two A-types (from the same pentagon edge) and at
most one B-type. If an independent dominating set uses either A-type
on an edge, it must use both: no selected high vertex can see that edge.
Even with both A-types and a B-type, some high vertex is missed because
every edge meets the vertex cover missed by the B-type.

Theorem 2.10: https://www.uhd.edu/documents/academics/sciences/dpw-cn2011.pdf.
Earlier disproof with eight high vertices: https://graffiti-verification-ae088f.gitlab.io/README.md, §7be.
-/

namespace Graffiti.FiveHeavy

open Graffiti.CliqueFiber

abbrev Color := Fin 20

/-- Labels 0–4 are high; 5–14 are pairs indexed by pentagon edges; 15–19
are B-types indexed by the five independent pairs of the pentagon. -/
def weight (i : Color) : ℕ := if i.val < 5 then 1 else if i.val < 15 then 15 else 24

def highs : Finset Color := {0, 1, 2, 3, 4}

private def edgeIndex (a : ℕ) := (a - 5) / 2

/-- Adjacency table for the ordered pair of numerical labels `a ≤ b`. -/
private def orderedAdj (a b : ℕ) : Bool :=
  if b < 5 then false
  else if a < 5 then
    if b < 15 then decide (a ≠ edgeIndex b ∧ a ≠ (edgeIndex b + 1) % 5)
    else decide (a = b - 15 ∨ a = (b - 15 + 2) % 5)
  else if b < 15 then decide (edgeIndex a ≠ edgeIndex b)
  else decide (15 ≤ a ∧ a ≠ b)

def quotient : SimpleGraph Color where
  Adj i j := orderedAdj (min i.val j.val) (max i.val j.val) = true
  symm := by
    intro i j h
    rwa [min_comm j.val i.val, max_comm j.val i.val]
  loopless := by
    change ∀ i : Color, ¬ orderedAdj (min i.val i.val) (max i.val i.val) = true
    decide

instance : DecidableRel quotient.Adj := fun i j =>
  inferInstanceAs (Decidable (orderedAdj (min i.val j.val) (max i.val j.val) = true))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem dataCert : Certificate quotient weight highs 3 4 5 275 where
  positive := by decide
  order_eq := by decide
  hubs_eq := by decide
  singleton_hubs := by decide
  indep_hubs := by decide
  seen := ⟨0, 3, by decide⟩
  checked := ⟨List.finRange 20, by decide, by decide⟩

/-- The graph has order 275 and exactly five independent strict-majority
vertices. Deleting them leaves independence number at most 3, strictly below
the independent domination number of the whole graph (at least 4). -/
theorem five_heavy_counterexample :
    Witness (liftGraph quotient weight) (majority (liftGraph quotient weight)) 3 4 5 275 := by
  have h := realize quotient weight highs 3 4 5 275 dataCert
  rw [fibers_eq_majority quotient weight highs 275 dataCert.order_eq (by decide)] at h
  exact h

end Graffiti.FiveHeavy
