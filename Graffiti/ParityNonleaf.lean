import Graffiti.HighDegreeBudget

namespace Graffiti.FirstZero

open Finset SimpleGraph SupportCounting

/-- Nonleaf vertices consume domination budget, with an extra unit of slack
when the total dominating set has odd cardinality. -/
theorem nonleaf_parity_budget {V : Type*} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} [DecidableRel T.Adj] (ht : T.IsTree) {D : Finset V}
    (hd : TotallyDominates T D) :
    (univ.filter (fun v => 1 < T.degree v)).card + 2 ≤ D.card + 2 * (D.card / 2) := by
  let N := univ.filter (fun v => 1 < T.degree v)
  have part := card_sdiff_add_card_inter N D
  have inside := card_le_card (inter_subset_right : N ∩ D ⊆ D)
  have outside : (N \ D).card ≤ ∑ v ∈ Dᶜ, (T.degree v - 1) := by
    calc
      _ = ∑ _ ∈ N \ D, 1 := by simp
      _ ≤ ∑ v ∈ N \ D, (T.degree v - 1) := by
        apply sum_le_sum; intro v hv
        have := (mem_filter.mp (mem_sdiff.mp hv).1).2
        omega
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg
        (fun v hv => mem_compl.mpr (mem_sdiff.mp hv).2) (fun _ _ _ => Nat.zero_le _)
  have eq := domination_excess_identity T ht hd
  let H := T.induce (↑D : Set V)
  have degree (v : D) : H.degree v = withinDegree T D v := by
    rw [← card_neighborFinset_eq_degree, withinDegree]
    apply card_bij (fun (w : D) _ => (w : V))
    · intro w hw; exact mem_filter.mpr ⟨w.property, (H.mem_neighborFinset v w).mp hw⟩
    · intro a _ b _ h; exact Subtype.ext h
    · intro w hw
      obtain ⟨hwD, ha⟩ := mem_filter.mp hw
      exact ⟨⟨w, hwD⟩, (H.mem_neighborFinset v ⟨w, hwD⟩).mpr ha, rfl⟩
  have shake := H.sum_degrees_eq_twice_card_edges
  simp_rw [degree] at shake
  have hs : (∑ v ∈ D, withinDegree T D v) = 2 * H.edgeFinset.card := by
    simpa only [← Finset.sum_attach D (withinDegree T D)] using shake
  have split : (∑ v ∈ D, (withinDegree T D v - 1)) + D.card = 2 * H.edgeFinset.card := by
    rw [← hs]
    calc
      _ = (∑ v ∈ D, (withinDegree T D v - 1)) + ∑ _ ∈ D, 1 := by simp
      _ = _ := by
        rw [← sum_add_distrib]; apply sum_congr rfl; intro v _
        obtain ⟨w, hw, hadj⟩ := hd v
        apply Nat.sub_add_cancel
        exact card_pos.mpr ⟨w, mem_filter.mpr ⟨hw, hadj⟩⟩
  have bound := sum_le_sum_of_subset_of_nonneg (f := fun v => withinDegree T D v - 1)
    (subset_univ D) (fun _ _ _ => Nat.zero_le _)
  change (∑ v ∈ D, (withinDegree T D v - 1)) ≤ ∑ v, (withinDegree T D v - 1) at bound
  change N.card + 2 ≤ _
  omega

end Graffiti.FirstZero
