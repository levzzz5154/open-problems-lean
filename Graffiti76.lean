import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Graffiti.ClusterStar

/-! # Graffiti.pc 76 fails by an unbounded amount

https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json

The conjecture compares the order of a largest induced tree to the number of
vertices maximizing triangle incidence divided by the floor of the average
degree. The examples have connected induced trees of size at most four, yet
the proposed lower bound is unbounded.
-/

namespace Graffiti.Wall76

open SimpleGraph Finset

variable {α : Type*} {G : SimpleGraph α} {k r : ℕ}

theorem connected (k r : ℕ) : (graph k r).Connected := by
  apply (connected_iff_exists_forall_reachable _).mpr
  refine ⟨(0, 0), fun v => ?_⟩
  let u : Vertex k r := (v.1, 0)
  have h₁ : (graph k r).Reachable (0, 0) u := by
    by_cases e : (0, 0) = u
    · rw [e]
    · exact Adj.reachable (show (graph k r).Adj (0, 0) u from ⟨e, Or.inr ⟨rfl, rfl⟩⟩)
  have h₂ : (graph k r).Reachable u v := by
    by_cases e : u = v
    · rw [e]
    · exact Adj.reachable (show (graph k r).Adj u v from ⟨e, Or.inl rfl⟩)
  exact h₁.trans h₂

private theorem acyclic_no_triangle (h : G.IsAcyclic) {x y z : α}
    (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : G.Adj y z) : False := by
  let p : G.Walk x z := .cons hxy (.cons hyz .nil)
  let q : G.Walk x z := .cons hxz .nil
  have hp : p.IsPath := by simp [p, Walk.isPath_def, hxy.ne, hxz.ne, hyz.ne]
  have hq : q.IsPath := by simp [q, Walk.isPath_def, hxz.ne]
  have e := congrArg (fun a : G.Path x z => a.val.length) (h.path_unique ⟨p, hp⟩ ⟨q, hq⟩)
  exact (by decide : (2 : ℕ) ≠ 1) e

private theorem clique_in_tree_le_two [DecidableEq α] {s t : Finset α}
    (h : (G.induce (s : Set α)).IsTree) (ht : t ⊆ s) (hc : G.IsClique (t : Set α)) :
    t.card ≤ 2 := by
  by_contra! hn
  obtain ⟨a, b, c, ha, hb, hc', hab, hac, hbc⟩ := two_lt_card_iff.mp hn
  let A : (s : Set α) := ⟨a, ht ha⟩
  let B : (s : Set α) := ⟨b, ht hb⟩
  let C : (s : Set α) := ⟨c, ht hc'⟩
  exact acyclic_no_triangle (x := A) (y := B) (z := C) h.IsAcyclic
    (hc ha hb hab) (hc ha hc' hac) (hc hb hc' hbc)

private theorem reachable_preserves {p : α → Prop}
    (step : ∀ {a b}, G.Adj a b → p a → p b) {a b : α} (h : G.Reachable a b) : p a → p b := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact id
  | cons e _ ih => exact fun ha => ih (step e ha)

/-- An induced connected subgraph meeting two fibers must include both hubs. -/
private theorem hub_at {s : Finset (Vertex k r)} (hc : ((graph k r).induce (s : Set _)).Connected)
    {i j : Fin (k+1)} (hi : i ∈ s.image Prod.fst) (hj : j ∈ s.image Prod.fst) (hne : i ≠ j) :
    (i, (0 : Fin (r+1))) ∈ s := by
  obtain ⟨x, hx, hxi⟩ := mem_image.mp hi
  obtain ⟨y, hy, hyj⟩ := mem_image.mp hj
  by_contra hm
  have step {a b : ↥s} (he : ((graph k r).induce (s : Set _)).Adj a b)
      (ha : a.val.1 = i) : b.val.1 = i := by
    rcases (show (graph k r).Adj a.val b.val from he).2 with h | h
    · exact h.symm.trans ha
    · exact False.elim (hm ((show a.val = (i, 0) from Prod.ext ha h.1) ▸ a.property))
  have e := reachable_preserves (p := fun a : ↥s => a.val.1 = i)
    (fun h => step h) (hc ⟨x, hx⟩ ⟨y, hy⟩) hxi
  exact hne (e.symm.trans hyj)

theorem induced_tree_le_four {s : Finset (Vertex k r)}
    (ht : ((graph k r).induce (s : Set _)).IsTree) : s.card ≤ 4 := by
  classical
  have hgroup (i : Fin (k+1)) : (s.filter fun x => x.1 = i).card ≤ 2 :=
    clique_in_tree_le_two ht (filter_subset _ _)
      (fun _ ha _ hb h => ⟨h, Or.inl ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm)⟩)
  have hf : (s.image Prod.fst).card ≤ 2 := by
    by_contra! hn
    obtain ⟨i, j, l, hi, hj, hl, hij, hil, hjl⟩ := two_lt_card_iff.mp hn
    let H := (graph k r).induce (s : Set _)
    let a : ↥s := ⟨(i, 0), hub_at ht.isConnected hi hj hij⟩
    let b : ↥s := ⟨(j, 0), hub_at ht.isConnected hj hi (Ne.symm hij)⟩
    let c : ↥s := ⟨(l, 0), hub_at ht.isConnected hl hi (Ne.symm hil)⟩
    have ab : H.Adj a b := ⟨fun e => hij (congrArg Prod.fst e), Or.inr ⟨rfl, rfl⟩⟩
    have ac : H.Adj a c := ⟨fun e => hil (congrArg Prod.fst e), Or.inr ⟨rfl, rfl⟩⟩
    have bc : H.Adj b c := ⟨fun e => hjl (congrArg Prod.fst e), Or.inr ⟨rfl, rfl⟩⟩
    exact acyclic_no_triangle ht.IsAcyclic ab ac bc
  calc s.card = ∑ i ∈ s.image Prod.fst, (s.filter fun x => x.1 = i).card := card_eq_sum_card_image ..
       _ ≤ ∑ _i ∈ s.image Prod.fst, 2 := sum_le_sum (fun i _ => hgroup i)
       _ ≤ 4 := by simpa only [sum_const, nsmul_eq_mul] using (show (s.image Prod.fst).card * 2 ≤ 4 by omega)

theorem largestInducedTree_le_four (k r : ℕ) : largestInducedTree (graph k r) ≤ 4 := by
  classical
  exact Finset.sup_le fun _ hs => induced_tree_le_four (mem_filter.mp hs).2

/-- A 343-vertex counterexample. The original lower bound is `49/12 > 4`. -/
theorem counterexample76 : (graph 48 6).Connected ∧
    maxTriangleFrequency (graph 48 6) = 49 ∧ floorAverageDegree (graph 48 6) = 12 ∧
    (largestInducedTree (graph 48 6) : ℚ) <
      (maxTriangleFrequency (graph 48 6) : ℚ) / floorAverageDegree (graph 48 6) := by
  have hf := maxTriangleFrequency_eq (r := 6) (k := 48) (by decide)
  have hd : floorAverageDegree (graph 48 6) = 12 := (floorAverageDegree_eq 48 6).trans (by decide)
  refine ⟨connected .., hf, hd, ?_⟩
  rw [hf, hd]
  have hl : (largestInducedTree (graph 48 6) : ℚ) ≤ 4 := by exact_mod_cast largestInducedTree_le_four 48 6
  exact lt_of_le_of_lt hl (by norm_num)

/-- No constant bound survives: even with tree number at most four and positive
floor average degree, the ratio in the conjecture exceeds any prescribed `B`. -/
theorem unbounded76 (B : ℕ) : ∃ k r, (graph k r).Connected ∧ largestInducedTree (graph k r) ≤ 4 ∧
    0 < floorAverageDegree (graph k r) ∧ B * floorAverageDegree (graph k r) < maxTriangleFrequency (graph k r) := by
  let r := 2*B+2
  let k := r + r*(r+1)
  have hr : 2 ≤ r := by dsimp [r]; omega
  have hk : 2 ≤ k := Nat.le_trans hr (Nat.le_add_right ..)
  have he : k / (r+1) = r := by
    dsimp only [k]; rw [Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega), Nat.zero_add]
  refine ⟨k, r, connected .., largestInducedTree_le_four .., ?_, ?_⟩
  · rw [floorAverageDegree_eq, he]; omega
  · rw [floorAverageDegree_eq, he, maxTriangleFrequency_eq hk]
    dsimp only [k, r]; nlinarith

end Graffiti.Wall76
