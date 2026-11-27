import Graffiti.MaxLeafStar
import Graffiti.LeafBounds

namespace Graffiti

open Finset SimpleGraph

variable {V : Type*} [Fintype V] (T : SimpleGraph V) [DecidableRel T.Adj]

/-- Upper middle degree: the least threshold reached by strictly more than half
of the vertices. Thus degrees are counted with their vertex multiplicities. -/
noncomputable def upperDegreeMedian : ℕ :=
  sInf {d : ℕ | Fintype.card V / 2 < (univ.filter fun x => T.degree x ≤ d).card}

/-- The upper median has one-based rank `⌊n/2⌋ + 1` in nondecreasing order. -/
theorem upperDegreeMedian_le_iff (hn : 0 < Fintype.card V) (d : ℕ) :
    upperDegreeMedian T ≤ d ↔ Fintype.card V / 2 < (univ.filter fun x => T.degree x ≤ d).card := by
  let S := {k : ℕ | Fintype.card V / 2 < (univ.filter fun x => T.degree x ≤ k).card}
  have hS : S.Nonempty := by
    refine ⟨T.maxDegree, ?_⟩
    change Fintype.card V / 2 < (univ.filter fun x => T.degree x ≤ T.maxDegree).card
    simp [T.degree_le_maxDegree, show Fintype.card V / 2 < Fintype.card V by omega]
  change sInf S ≤ d ↔ d ∈ S
  refine ⟨fun h => ?_, fun h => Nat.sInf_le h⟩
  have hs : sInf S ∈ S := Nat.sInf_mem hS
  exact lt_of_lt_of_le hs (card_le_card fun x hx =>
    mem_filter.mpr ⟨mem_univ x, ((mem_filter.mp hx).2 : T.degree x ≤ sInf S).trans h⟩)

variable {T}

/-- If all but at most one vertex above the cutoff have degree ≥ 3, the
handshaking deficit of two still forces a strict majority below or at it. -/
private theorem median_le_of_exception (ht : T.IsTree) (hn : 2 < Fintype.card V)
    (d : ℕ) (e : V) (high : ∀ x, x ≠ e → d < T.degree x → 3 ≤ T.degree x)
    (he : d < T.degree e → 2 ≤ T.degree e) : upperDegreeMedian T ≤ d := by
  classical
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  apply (upperDegreeMedian_le_iff T (by omega) d).mpr
  let low (x : V) : ℕ := if T.degree x ≤ d then 1 else 0
  have hlow : ∑ x, low x = (univ.filter fun x => T.degree x ≤ d).card := by simp [low]
  have point (x : V) : 3 ≤ T.degree x + low x + low x + (if x = e then 1 else 0) := by
    have hp := degree_pos_of_connected ht.isConnected x
    by_cases hl : T.degree x ≤ d
    · simp only [low, if_pos hl]; omega
    · simp only [low, if_neg hl, Nat.add_zero]
      by_cases hx : x = e
      · subst x; simpa using (show 3 ≤ T.degree e + 1 by have := he (by omega); omega)
      · simpa [hx] using high x hx (by omega)
  have hs := sum_le_sum (s := (univ : Finset V)) (fun x _ => point x)
  simp only [sum_const, card_univ, smul_eq_mul, sum_add_distrib,
    T.sum_degrees_eq_twice_card_edges, hlow] at hs
  rw [show (∑ x : V, if x = e then 1 else 0 : ℕ) = 1 by simp] at hs
  have htree := ht.card_edgeFinset
  omega

/-- Every tree of order greater than two has upper middle degree at most two. -/
theorem upperDegreeMedian_tree_le_two (ht : T.IsTree) (hn : 2 < Fintype.card V) :
    upperDegreeMedian T ≤ 2 :=
  median_le_of_exception ht hn 2 (Classical.choice ht.isConnected.nonempty)
    (fun _ _ h => h) (fun h => by omega)

/-- A tree with one lower-degree hub and equal maximum-degree branch centers
has a strict majority of leaves, including when the hub is itself a leaf. -/
theorem upperDegreeMedian_maxLeafStar_le_one (ht : T.IsTree) (hn : 2 < Fintype.card V)
    {I : Finset V} {r : V} (h : MaxLeafStar T I r) : upperDegreeMedian T ≤ 1 := by
  classical
  by_cases big : 3 ≤ T.maxDegree
  · apply median_le_of_exception ht hn 1 r _ (fun h => h)
    intro x hxr hx
    by_cases hI : x ∈ I
    · simpa [h.maximum x hI] using big
    · have := h.leaves x hI hxr
      omega
  · obtain ⟨i, hi⟩ := h.inhabited
    have small : (T.neighborFinset r).card ≤ 1 := by
      rw [card_neighborFinset_eq_degree]; have := h.hub_lt; omega
    apply median_le_of_exception ht hn 1 i _ (fun h => h)
    intro x hxi hx
    by_cases hxr : x = r
    · subst x; have := h.hub_lt; omega
    · have hout : x ∉ I := fun hI => hxi (card_le_one.mp small _
          ((T.mem_neighborFinset r x).mpr (h.adjacent x hI)) _
          ((T.mem_neighborFinset r i).mpr (h.adjacent i hi)))
      have := h.leaves x hout hxr
      omega

end Graffiti
