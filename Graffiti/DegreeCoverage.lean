import Graffiti369

namespace Graffiti.FirstZero

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {T : SimpleGraph V} [DecidableRel T.Adj]

omit [DecidableEq V] in
private theorem sorted_degree_sum (D : Finset V) :
    ((D.val.map (fun v => T.degree v)).sort (· ≥ ·)).sum = ∑ v ∈ D, T.degree v :=
  congrArg Multiset.sum (Multiset.sort_eq (· ≥ ·) _)

omit [DecidableEq V] in
theorem degree_list_facts (ht : T.IsTree) (hn : 2 < Fintype.card V) :
    (degrees T).length = Fintype.card V ∧ (degrees T).sum + 2 = 2 * Fintype.card V ∧
    (degrees T).Pairwise (· ≥ ·) ∧ (∀ d ∈ degrees T, 0 < d) ∧
    ((degrees T).filter (fun d => 1 < d)).length =
      (Finset.univ.filter (fun v => 1 < T.degree v)).card := by
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  refine ⟨by simp [degrees], ?_, Multiset.sort_sorted _ _, ?_, ?_⟩
  · have hs : (degrees T).sum = ∑ v, T.degree v := sorted_degree_sum univ
    have he := T.sum_degrees_eq_twice_card_edges
    have hc := ht.card_edgeFinset
    omega
  · intro d hd
    obtain ⟨v, _, rfl⟩ := Multiset.mem_map.mp ((Multiset.mem_sort _).mp hd)
    exact degree_pos_of_connected ht.isConnected v
  · change Multiset.card (Multiset.filter (fun d : ℕ => 1 < d) (degrees T : Multiset ℕ)) = _
    rw [degrees, Multiset.sort_eq, Multiset.filter_map, Multiset.card_map]
    rfl

/-- The head of a descending list bounds the head of any nonempty sublist;
removing both heads preserves the sublist relation. -/
private theorem sublist_sum_le_prefix {xs ys : List ℕ} (hsub : xs.Sublist ys)
    (hs : ys.Pairwise (· ≥ ·)) {b : ℕ} (hb : xs.length ≤ b) :
    xs.sum ≤ (ys.take b).sum := by
  induction ys generalizing xs b with
  | nil => simp [List.sublist_nil.mp hsub]
  | cons y ys ih =>
    cases xs with
    | nil => simp
    | cons x xs =>
      cases b with
      | zero => simp at hb
      | succ b =>
        have hx := hsub.subset (List.mem_cons_self (a := x) (l := xs))
        have hxy : x ≤ y := (List.mem_cons.mp hx).elim (fun h => h.le)
          (fun h => (List.pairwise_cons.mp hs).1 x h)
        have ht := ih (xs := xs) (b := b) hsub.tail (List.pairwise_cons.mp hs).2 (by simpa using hb)
        simpa using Nat.add_le_add hxy ht

theorem degree_prefix_cover {D : Finset V} (hd : TotallyDominates T D) {b : ℕ}
    (hb : D.card ≤ b) : Fintype.card V ≤ ((degrees T).take b).sum := by
  have hcover : (univ : Finset V) ⊆ D.biUnion (fun v => T.neighborFinset v) := by
    intro x _
    obtain ⟨v, hv, ha⟩ := hd x
    exact mem_biUnion.mpr ⟨v, hv, (T.mem_neighborFinset _ _).mpr ha.symm⟩
  have hdom : Fintype.card V ≤ ∑ v ∈ D, T.degree v := by
    simpa using (card_le_card hcover).trans card_biUnion_le
  let xs := (D.val.map (fun v => T.degree v)).sort (· ≥ ·)
  have hsub : xs.Sublist (degrees T) := by
    apply List.sublist_of_subperm_of_sorted (r := (· ≥ ·)) _ (Multiset.sort_sorted _ _)
      (Multiset.sort_sorted _ _)
    apply Multiset.coe_le.mp
    simp only [xs, degrees, Multiset.sort_eq]
    exact Multiset.map_le_map (val_le_iff.mpr (subset_univ D))
  rw [← sorted_degree_sum] at hdom
  exact hdom.trans (sublist_sum_le_prefix hsub (Multiset.sort_sorted _ _) (by simpa [xs] using hb))

end Graffiti.FirstZero

#print axioms Graffiti.FirstZero.degree_list_facts
#print axioms Graffiti.FirstZero.degree_prefix_cover
