import Graffiti.ParentForest
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fintype.Sigma

/-! # A three-arm family with isolated supports five steps apart in pairs

The root and every fifth arm vertex are selected relays. Their neighbors on
the three arms are marked and receive a private leaf. Arms 0 and 1 have one
more five-edge block than arm 2. At the last marked vertex of arm 2, add an
arbitrary bouquet. It changes the peripheral mean, not the relay budget.
-/

namespace Graffiti.ParentForest
open SimpleGraph Finset

/-- A finite parent graph with decreasing rank and a unique fixed root is a tree. -/
theorem tree_of_unique_root {V : Type*} [Fintype V] [DecidableEq V] (p : V → V)
    (rank : V → ℕ) (r : V) (hroot : p r = r) (desc : ∀ x, x ≠ r → rank (p x) < rank x) :
    (graph p).IsTree := by
  have nonfix {x} (hx : x ≠ r) : p x ≠ x := fun eq => by
    have h := desc x hx
    rw [eq] at h
    exact Nat.lt_irrefl _ h
  have hc := connected_of_unique_root p rank (fun x hx => desc x (fun e => hx (e ▸ hroot))) r
    (fun x hx => Classical.byContradiction fun ne => nonfix ne hx)
  let U := (univ : Finset V).erase r
  let f (x : V) := s(x,p x)
  have sub : (graph p).edgeFinset ⊆ U.image f := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ a b =>
      have hab : (graph p).Adj a b := mem_edgeFinset.mp he
      rcases hab with ⟨hne, hp | hp⟩
      · refine mem_image.mpr ⟨a, mem_erase.mpr ⟨fun eq => hne (by simpa [eq, hroot] using hp), mem_univ _⟩, ?_⟩
        simp only [f,hp]
      · refine mem_image.mpr ⟨b, mem_erase.mpr ⟨fun eq => hne (by simpa [eq, hroot] using hp.symm), mem_univ _⟩, ?_⟩
        rw [show f b = s(b,a) by simp [f,hp], Sym2.eq_swap]
  have size := card_erase_add_one (mem_univ r)
  have ub : (graph p).edgeFinset.card ≤ U.card := (card_le_card sub).trans card_image_le
  apply isTree_iff_connected_and_card.mpr
  refine ⟨hc, le_antisymm ?_ hc.card_vert_le_card_edgeSet_add_one⟩
  rw [Nat.card_eq_fintype_card, ← edgeFinset_card, Nat.card_eq_fintype_card]
  change ((univ : Finset V).erase r).card + 1 = univ.card at size
  rw [card_univ] at size
  change (graph p).edgeFinset.card ≤ ((univ : Finset V).erase r).card at ub
  omega
end Graffiti.ParentForest

namespace Graffiti.PeripheralTripod

/-- Number of complete five-edge blocks between the root and the last relay. -/
def blocks (m : ℕ) (a : Fin 3) : ℕ := if a = 2 then m else m + 1

abbrev Segment (m : ℕ) := (a : Fin 3) × Fin (5 * blocks m a + 1)
def MarkedAt (j : ℕ) : Prop := j % 5 = 0 ∨ j % 5 = 3
instance (j : ℕ) : Decidable (MarkedAt j) := inferInstanceAs (Decidable (_ ∨ _))
abbrev Marked (m : ℕ) := {z : Segment m // MarkedAt z.2.val}
abbrev Base (m : ℕ) := Option (Segment m) ⊕ Marked m
abbrev Vertex (m N : ℕ) := Base m ⊕ Fin N

abbrev root {m N} : Vertex m N := .inl (.inl none)
abbrev stem {m N} (z : Segment m) : Vertex m N := .inl (.inl (some z))
abbrev sprout {m N} (z : Marked m) : Vertex m N := .inl (.inr z)
abbrev bunch {m N} (i : Fin N) : Vertex m N := .inr i

def lastSeg (m : ℕ) (a : Fin 3) : Segment m := ⟨a, ⟨5 * blocks m a, by omega⟩⟩

def parent {m N} : Vertex m N → Vertex m N
  | .inl (.inl none) => root
  | .inl (.inl (some ⟨a, i⟩)) =>
    if i.val = 0 then root else stem ⟨a, ⟨i.val - 1, by omega⟩⟩
  | .inl (.inr z) => stem z.val
  | .inr _ => stem (lastSeg m 2)

abbrev tree (m N : ℕ) := ParentForest.graph (@parent m N)

def depth {m N} : Vertex m N → ℕ
  | .inl (.inl none) => 0
  | .inl (.inl (some z)) => z.2.val + 1
  | .inl (.inr z) => z.val.2.val + 2
  | .inr _ => 5*m + 2

def arm {m N} : Vertex m N → Option (Fin 3)
  | .inl (.inl none) => none
  | .inl (.inl (some z)) => some z.1
  | .inl (.inr z) => some z.val.1
  | .inr _ => some 2

theorem parent_depth {m N} (x : Vertex m N) (hx : x ≠ root) : depth (parent x) + 1 = depth x := by
  rcases x with ((_|⟨a,i⟩)|z)|j
  · exact (hx rfl).elim
  · simp only [parent]
    by_cases hz : i.val = 0
    · rw [if_pos hz]; change 0 + 1 = i.val + 1; rw [hz]
    · rw [if_neg hz]; change i.val - 1 + 1 + 1 = i.val + 1; omega
  · rfl
  · simp [parent,lastSeg,depth,blocks]

theorem parent_arm {m N} (x : Vertex m N) (hx : parent x ≠ root) : arm (parent x) = arm x := by
  rcases x with ((_|⟨a,i⟩)|z)|j
  · exact (hx rfl).elim
  · simp only [parent] at hx ⊢; split at hx <;> rename_i h
    · exact (hx rfl).elim
    · simp [h,arm]
  · rfl
  · rfl

theorem isTree (m N : ℕ) : (tree m N).IsTree :=
  ParentForest.tree_of_unique_root parent depth root rfl (fun x hx => by have := parent_depth x hx; omega)

end Graffiti.PeripheralTripod
