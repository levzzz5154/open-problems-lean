import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.SetTheory.Cardinal.Finite

/-! The components of an induced subgraph of a parent forest are indexed
by the vertices whose parent is missing (or which are themselves roots). -/

namespace Graffiti.ParentForest

open Finset SimpleGraph

variable {V : Type*} (p : V → V)

def graph : SimpleGraph V where
  Adj x y := x ≠ y ∧ (p x = y ∨ p y = x)
  symm := fun _ _ h => ⟨h.1.symm,h.2.symm⟩
  loopless := fun _ h => h.1 rfl

instance [DecidableEq V] : DecidableRel (graph p).Adj := fun x y =>
  inferInstanceAs (Decidable (x ≠ y ∧ (p x = y ∨ p y = x)))

theorem connected_of_unique_root (rank : V → ℕ) (desc : ∀ x, p x ≠ x → rank (p x) < rank x)
    (r : V) (fixed : ∀ x, p x = x → x = r) : (graph p).Connected := by
  have reach (x : V) : (graph p).Reachable x r := by
    induction x using (measure rank).wf.induction with
    | h x ih =>
      by_cases eq : p x = x
      · rw [fixed x eq]
      · exact (show (graph p).Adj x (p x) from ⟨Ne.symm eq,Or.inl rfl⟩).reachable.trans
          (ih _ (desc x eq))
  exact (connected_iff_exists_forall_reachable _).mpr ⟨r,fun x => (reach x).symm⟩

variable [DecidableEq V]

def roots (S : Finset V) : Finset V := S.filter fun x => ¬(p x ≠ x ∧ p x ∈ S)

private def anchor (rank : V → ℕ) (desc : ∀ x, p x ≠ x → rank (p x) < rank x)
    (S : Finset V) (x : V) : V :=
  if _h : p x ≠ x ∧ p x ∈ S then anchor rank desc S (p x) else x
termination_by rank x
decreasing_by exact desc x _h.1

/-- The cardinality formula does not depend on an edge or reachability
algorithm. Following parents in the selected vertices stops at a unique root. -/
theorem component_count (rank : V → ℕ) (desc : ∀ x, p x ≠ x → rank (p x) < rank x) (S : Finset V) :
    Nat.card ((graph p).induce (S : Set V)).ConnectedComponent = (roots p S).card := by
  let H := (graph p).induce (S : Set V)
  let A := anchor p rank desc S
  let emb (r : ↥(roots p S)) : (S : Set V) := ⟨r.val,(mem_filter.mp r.property).1⟩
  have fixed (r : ↥(roots p S)) : A r.val = r.val := by
    change anchor p rank desc S r.val = _
    rw [anchor,dif_neg (mem_filter.mp r.property).2]
  have up {x y : (S : Set V)} (e : p x.val = y.val) (ne : x.val ≠ y.val) : A x.val = A y.val := by
    have h : p x.val ≠ x.val ∧ p x.val ∈ S := ⟨by rw [e]; exact ne.symm, e ▸ y.property⟩
    change anchor p rank desc S x.val = _
    rw [anchor,dif_pos h,e]
  have stable {x y : (S : Set V)} (walk : H.Walk x y) : A x.val = A y.val := by
    induction walk with
    | nil => rfl
    | cons e _ ih =>
      apply Eq.trans _ ih
      rcases e with ⟨ne,e|e⟩
      · exact up e ne
      · exact (up e ne.symm).symm
  have hit (x : V) (hx : x ∈ S) : ∃ r : ↥(roots p S), H.Reachable ⟨x,hx⟩ (emb r) := by
    induction x using (measure rank).wf.induction with
    | h x ih =>
      by_cases h : p x ≠ x ∧ p x ∈ S
      · obtain ⟨r,hr⟩ := ih (p x) (desc x h.1) h.2
        exact ⟨r,(show H.Adj ⟨x,hx⟩ ⟨p x,h.2⟩ from ⟨h.1.symm,Or.inl rfl⟩).reachable.trans hr⟩
      · exact ⟨⟨x,mem_filter.mpr ⟨hx,h⟩⟩,Reachable.rfl⟩
  let f (r : ↥(roots p S)) := H.connectedComponentMk (emb r)
  have inj : Function.Injective f := by
    intro a b h
    obtain ⟨walk⟩ := ConnectedComponent.exact h
    exact Subtype.ext ((fixed a).symm.trans ((stable walk).trans (fixed b)))
  have surj : Function.Surjective f := by
    intro c
    obtain ⟨x,hx⟩ := c.exists_rep
    obtain ⟨r,hr⟩ := hit x.val x.property
    exact ⟨r,(ConnectedComponent.sound hr).symm.trans hx⟩
  exact (Nat.card_congr (Equiv.ofBijective _ ⟨inj,surj⟩)).symm.trans
    (by rw [Nat.card_eq_fintype_card]; exact Fintype.card_coe _)

end Graffiti.ParentForest
