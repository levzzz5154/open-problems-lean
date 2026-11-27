import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Clique bundles for Graffiti.pc 76

Take a clique on `k+1` hubs. Attach a private `(r+1)`-clique at each hub,
identifying just that vertex. Each clique in the resulting graph is either
entirely in one private clique or entirely in the hub clique.
-/

namespace Graffiti.Wall76

open SimpleGraph Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Removing `v` from an incident triangle leaves an unordered pair. -/
noncomputable def trianglePairs (G : SimpleGraph α) (v : α) : Finset (Finset α) := by
  classical
  exact ((univ.erase v).powersetCard 2).filter fun t => G.IsClique (insert v (t : Set α))

noncomputable def trianglesAt (G : SimpleGraph α) (v : α) : ℕ := (trianglePairs G v).card

noncomputable def maxTriangleFrequency (G : SimpleGraph α) : ℕ := by
  classical
  exact (univ.filter fun v => trianglesAt G v = univ.sup (trianglesAt G)).card

def floorAverageDegree (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  (∑ v, G.degree v) / Fintype.card α

noncomputable def largestInducedTree (G : SimpleGraph α) : ℕ := by
  classical
  exact (univ.filter fun s : Finset α => (G.induce (s : Set α)).IsTree).sup card

abbrev Vertex (k r : ℕ) := Fin (k+1) × Fin (r+1)

def graph (k r : ℕ) : SimpleGraph (Vertex k r) where
  Adj v w := v ≠ w ∧ (v.1 = w.1 ∨ (v.2 = 0 ∧ w.2 = 0))
  symm := fun _ _ ⟨h, h'⟩ => ⟨h.symm, h'.imp Eq.symm And.symm⟩
  loopless := fun _ h => h.1 rfl

instance (k r : ℕ) : DecidableRel (graph k r).Adj := fun v w =>
  inferInstanceAs (Decidable (v ≠ w ∧ (v.1 = w.1 ∨ (v.2 = 0 ∧ w.2 = 0))))

variable {k r : ℕ}

def fiber (i : Fin (k+1)) (r : ℕ) : Finset (Vertex k r) :=
  univ.map ⟨Prod.mk i, fun _ _ h => congrArg Prod.snd h⟩

def hubs (k r : ℕ) : Finset (Vertex k r) :=
  univ.map ⟨fun i => (i, 0), fun _ _ h => congrArg Prod.fst h⟩

@[simp] theorem mem_fiber {v : Vertex k r} {i} : v ∈ fiber i r ↔ v.1 = i := by
  rcases v with ⟨j, b⟩
  simp [fiber, Prod.ext_iff, eq_comm]

@[simp] theorem mem_hubs {v : Vertex k r} : v ∈ hubs k r ↔ v.2 = 0 := by
  rcases v with ⟨i, b⟩
  simp [hubs, Prod.ext_iff, eq_comm]

@[simp] theorem card_fiber (i : Fin (k+1)) : (fiber i r).card = r+1 := by simp [fiber]
@[simp] theorem card_hubs : (hubs k r).card = k+1 := by simp [hubs]

private def localNeighbors (v : Vertex k r) := (fiber v.1 r).erase v
private def hubNeighbors (v : Vertex k r) := if v.2 = 0 then (hubs k r).erase v else ∅

@[simp] private theorem mem_local {v w : Vertex k r} :
    w ∈ localNeighbors v ↔ w ≠ v ∧ w.1 = v.1 := by simp [localNeighbors]

@[simp] private theorem mem_hubNeighbors {v w : Vertex k r} :
    w ∈ hubNeighbors v ↔ w ≠ v ∧ v.2 = 0 ∧ w.2 = 0 := by
  by_cases h : v.2 = 0 <;> simp [hubNeighbors, h]

private theorem neighbors_disjoint (v : Vertex k r) : Disjoint (localNeighbors v) (hubNeighbors v) := by
  refine disjoint_left.mpr fun w hl hh => ?_
  obtain ⟨hne, hfst⟩ := mem_local.mp hl
  obtain ⟨_, hv, hw⟩ := mem_hubNeighbors.mp hh
  exact hne (Prod.ext hfst (hw.trans hv.symm))

@[simp] private theorem card_local (v : Vertex k r) : (localNeighbors v).card = r := by
  unfold localNeighbors
  rw [card_erase_of_mem (mem_fiber.mpr rfl), card_fiber]; omega

@[simp] private theorem card_hubNeighbors (v : Vertex k r) :
    (hubNeighbors v).card = if v.2 = 0 then k else 0 := by
  by_cases hv : v.2 = 0
  · simp [hubNeighbors, hv, card_erase_of_mem (mem_hubs.mpr hv)]
  · simp [hubNeighbors, hv]

theorem degree_eq (v : Vertex k r) : (graph k r).degree v = r + (if v.2 = 0 then k else 0) := by
  have h : (graph k r).neighborFinset v = localNeighbors v ∪ hubNeighbors v := by
    ext w
    rw [mem_neighborFinset, mem_union, mem_local, mem_hubNeighbors]
    change (v ≠ w ∧ (v.1 = w.1 ∨ (v.2 = 0 ∧ w.2 = 0))) ↔ _
    constructor
    · rintro ⟨hne, h | h⟩
      · exact Or.inl ⟨Ne.symm hne, h.symm⟩
      · exact Or.inr ⟨Ne.symm hne, h⟩
    · rintro (⟨hne, h⟩ | ⟨hne, h⟩)
      · exact ⟨Ne.symm hne, Or.inl h.symm⟩
      · exact ⟨Ne.symm hne, Or.inr h⟩
  rw [← card_neighborFinset_eq_degree, h, card_union_of_disjoint (neighbors_disjoint v),
    card_local, card_hubNeighbors]

theorem floorAverageDegree_eq (k r : ℕ) : floorAverageDegree (graph k r) = r + k / (r+1) := by
  have hsum : (∑ v : Vertex k r, (graph k r).degree v) = (k+1) * ((r+1)*r+k) := by
    simp only [degree_eq, Fintype.sum_prod_type, sum_add_distrib]
    simp [Nat.mul_add]
  unfold floorAverageDegree
  rw [hsum, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Nat.mul_div_mul_left _ _ (by omega)]
  rw [Nat.mul_comm (r+1) r, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.add_comm]

private theorem clique_cases {s : Set (Vertex k r)} (hs : (graph k r).IsClique s) :
    (∀ v ∈ s, v.2 = 0) ∨ ∃ i, ∀ v ∈ s, v.1 = i := by
  by_cases h : ∀ v ∈ s, v.2 = 0
  · exact Or.inl h
  push_neg at h
  obtain ⟨x, hx, hx0⟩ := h
  refine Or.inr ⟨x.1, fun y hy => ?_⟩
  by_cases e : y = x
  · rw [e]
  rcases (hs hx hy (Ne.symm e)).2 with hf | hz
  · exact hf.symm
  · exact (hx0 hz.1).elim

private theorem clique_of_fiber {s : Set (Vertex k r)} {i : Fin (k+1)}
    (hs : ∀ v ∈ s, v.1 = i) : (graph k r).IsClique s :=
  fun v hv w hw h => ⟨h, Or.inl ((hs v hv).trans (hs w hw).symm)⟩

private theorem clique_of_hubs {s : Set (Vertex k r)} (hs : ∀ v ∈ s, v.2 = 0) :
    (graph k r).IsClique s := fun v hv w hw h => ⟨h, Or.inr ⟨hs v hv, hs w hw⟩⟩

private theorem trianglePairs_eq (v : Vertex k r) : trianglePairs (graph k r) v =
    (localNeighbors v).powersetCard 2 ∪ (hubNeighbors v).powersetCard 2 := by
  classical
  ext t
  simp only [trianglePairs, mem_filter, mem_powersetCard, mem_union]
  constructor
  · rintro ⟨⟨ht, hc⟩, hcl⟩
    rcases clique_cases hcl with hh | ⟨i, hi⟩
    · exact Or.inr ⟨fun x hx => mem_hubNeighbors.mpr ⟨(mem_erase.mp (ht hx)).1,
        hh v (Set.mem_insert _ _), hh x (Set.mem_insert_of_mem _ hx)⟩, hc⟩
    · exact Or.inl ⟨fun x hx => mem_local.mpr ⟨(mem_erase.mp (ht hx)).1,
        (hi x (Set.mem_insert_of_mem _ hx)).trans (hi v (Set.mem_insert _ _)).symm⟩, hc⟩
  · rintro (⟨ht, hc⟩ | ⟨ht, hc⟩)
    · refine ⟨⟨fun x hx => mem_erase.mpr ⟨(mem_local.mp (ht hx)).1, mem_univ _⟩, hc⟩,
        clique_of_fiber (i := v.1) ?_⟩
      rintro x (rfl | hx)
      · rfl
      · exact (mem_local.mp (ht hx)).2
    · obtain ⟨z, hz⟩ := card_pos.mp (show 0 < t.card by omega)
      refine ⟨⟨fun x hx => mem_erase.mpr ⟨(mem_hubNeighbors.mp (ht hx)).1, mem_univ _⟩, hc⟩,
        clique_of_hubs ?_⟩
      rintro x (rfl | hx)
      · exact (mem_hubNeighbors.mp (ht hz)).2.1
      · exact (mem_hubNeighbors.mp (ht hx)).2.2

omit [Fintype α] [DecidableEq α] in
private theorem disjoint_pairs {a b : Finset α} (h : Disjoint a b) :
    Disjoint (a.powersetCard 2) (b.powersetCard 2) := by
  refine disjoint_left.mpr fun s hs ht => ?_
  obtain ⟨hsa, hc⟩ := mem_powersetCard.mp hs
  obtain ⟨x, hx⟩ := card_pos.mp (show 0 < s.card by omega)
  exact disjoint_left.mp h (hsa hx) ((mem_powersetCard.mp ht).1 hx)

theorem trianglesAt_eq (v : Vertex k r) :
    trianglesAt (graph k r) v = r.choose 2 + (if v.2 = 0 then k.choose 2 else 0) := by
  unfold trianglesAt
  rw [trianglePairs_eq, card_union_of_disjoint (disjoint_pairs (neighbors_disjoint v))]
  by_cases h : v.2 = 0 <;> simp [card_powersetCard, h]

theorem maxTriangleFrequency_eq (h : 2 ≤ k) : maxTriangleFrequency (graph k r) = k+1 := by
  classical
  have hp : 0 < k.choose 2 := Nat.choose_pos h
  have hm : univ.sup (trianglesAt (graph k r)) = r.choose 2 + k.choose 2 := by
    apply le_antisymm
    · exact Finset.sup_le fun v _ => by rw [trianglesAt_eq]; split <;> omega
    · exact le_sup_of_le (b := (0, 0)) (mem_univ _) (by simp [trianglesAt_eq])
  have he : (univ.filter fun v => trianglesAt (graph k r) v = univ.sup (trianglesAt (graph k r))) =
      hubs k r := by
    ext v
    simp only [mem_filter, mem_univ, true_and, hm, trianglesAt_eq, mem_hubs]
    by_cases hv : v.2 = 0 <;> simp [hv, Nat.ne_of_gt hp]
  exact (congrArg Finset.card he).trans card_hubs

end Graffiti.Wall76
