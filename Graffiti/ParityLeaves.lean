import Graffiti.LeafBounds
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Metric

namespace Graffiti

open Finset SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- The first step of a shortest walk toward `r` decreases its distance by one. -/
private theorem exists_closer_neighbor (hG : G.Connected) {r x : V} (hx : x ≠ r) :
    ∃ y, G.Adj x y ∧ G.dist r x = G.dist r y + 1 := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist x r
  have hn := Walk.not_nil_of_ne (p := p) hx
  have ha := p.adj_snd hn
  have hlen := p.length_tail_add_one hn
  have hlo := dist_le p.tail
  have hhi : G.dist r x ≤ G.dist r p.snd + 1 := by
    simpa only [dist_eq_one_iff_adj.mpr ha.symm] using
      (hG.dist_triangle (u := r) (v := p.snd) (w := x))
  rw [dist_comm (u := x) (v := r)] at hp
  rw [dist_comm (u := p.snd) (v := r)] at hlo
  exact ⟨p.snd, ha, by omega⟩

variable [Fintype V] [Nontrivial V]

/-- On one side of a connected bipartite graph the departure from degree two
is exactly the excess branching minus the number of leaves on that side. -/
theorem parity_side_balance [DecidableEq V] [DecidableRel G.Adj]
    (hG : G.Connected) (S : Finset V) (hb : G.IsBipartiteWith S (Sᶜ : Finset V)) :
    2 * S.card + ∑ x ∈ S, (G.degree x - 2) =
      G.edgeFinset.card + (S.filter fun x => G.degree x = 1).card := by
  classical
  have h := sum_congr (s₁ := S) rfl fun x _ =>
    (show 2 + (G.degree x - 2) = G.degree x + (if G.degree x = 1 then 1 else 0) by
      have hp := degree_pos_of_connected hG x
      split <;> omega)
  simpa [sum_add_distrib, Nat.mul_comm, isBipartiteWith_sum_degrees_eq_card_edges hb] using h

private theorem twice_side_card_le [DecidableEq V] [DecidableRel G.Adj]
    (hG : G.Connected) (S : Finset V) (hb : G.IsBipartiteWith S (Sᶜ : Finset V)) :
    2 * S.card ≤ G.edgeFinset.card + (pendantVertices G).card := by
  have hb' := parity_side_balance hG S hb
  have hc : (S.filter (fun x => G.degree x = 1)).card ≤ (pendantVertices G).card :=
    card_le_card fun x hx => mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hx).2⟩
  omega

/-- The even and odd distance layers are the two sides of a spanning tree,
even when the original graph is not bipartite. -/
theorem exists_parity_spanning_tree [DecidableEq V] (hG : G.Connected) (r : V) :
    ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree ∧
      let S := (univ : Finset V).filter (fun x => Even (G.dist r x))
      T.IsBipartiteWith S (Sᶜ : Finset V) := by
  classical
  let S := (univ : Finset V).filter fun x => Even (G.dist r x)
  let H : SimpleGraph V := {
    Adj := fun x y => G.Adj x y ∧ (x ∈ S ∧ y ∉ S ∨ x ∉ S ∧ y ∈ S)
    symm := fun _ _ ⟨ha, hc⟩ => ⟨ha.symm, hc.elim (Or.inr ∘ And.symm) (Or.inl ∘ And.symm)⟩
    loopless := fun x h => G.loopless x h.1 }
  have hr (x : V) : H.Reachable x r := by
    induction hd : G.dist r x generalizing x with
    | zero => exact (hG.dist_eq_zero_iff.mp hd) ▸ Reachable.rfl
    | succ n ih =>
      have hx : x ≠ r := by rintro rfl; simp [dist_self] at hd
      obtain ⟨y, hxy, hy⟩ := exists_closer_neighbor hG hx
      have hyd : G.dist r y = n := by omega
      have ha : H.Adj x y := by
        refine ⟨hxy, ?_⟩
        simp only [S, mem_filter, mem_univ, true_and, hy, Nat.even_add_one]
        tauto
      exact ha.reachable.trans (ih y hyd)
  have hH : H.Connected := ⟨fun x y => (hr x).trans (hr y).symm⟩
  obtain ⟨T, hTH, hT⟩ := hH.exists_isTree_le
  have hb : T.IsBipartiteWith S (Sᶜ : Finset V) := by
    refine ⟨Set.disjoint_left.mpr (fun _ hx hc => (Finset.mem_compl.mp hc) hx),
      fun {x y} hxy => ?_⟩
    simpa only [Finset.mem_coe, Finset.mem_compl] using (hTH hxy).2
  exact ⟨T, fun _ _ h => (hTH h).1, hT, hb⟩

/-- Both distance parities obey the same leaf bound; equivalently the even
count lies within `(L-1)/2` of half the order. -/
theorem parity_card_bounds [DecidableEq V] (hG : G.Connected) (r : V) :
    let S := (univ : Finset V).filter (fun x => Even (G.dist r x))
    2 * S.card + 1 ≤ Fintype.card V + maxLeafCount G ∧
      2 * Sᶜ.card + 1 ≤ Fintype.card V + maxLeafCount G := by
  classical
  let S := (univ : Finset V).filter fun x => Even (G.dist r x)
  obtain ⟨T,hle,hT,hb⟩ := exists_parity_spanning_tree hG r
  change T.IsBipartiteWith S (Sᶜ : Finset V) at hb
  have he := twice_side_card_le hT.isConnected S hb
  have ho := twice_side_card_le hT.isConnected Sᶜ (by simpa only [compl_compl] using hb.symm)
  have hleaf := leaves_le_maxLeafCount hle hT
  have hsize := hT.card_edgeFinset
  change 2 * S.card + 1 ≤ _ ∧ 2 * Sᶜ.card + 1 ≤ _
  constructor <;> omega

theorem even_card_le_order_add_leaves (hG : G.Connected) (r : V) :
    2 * ((univ : Finset V).filter (fun x => Even (G.dist r x))).card + 1 ≤
      Fintype.card V + maxLeafCount G := by
  classical exact (parity_card_bounds hG r).1

end Graffiti
