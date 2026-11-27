import Graffiti258
import Graffiti.PeripheralTwo
import Graffiti450

/-! # Written on the Wall II, Graffiti.pc 259, 260, and 261

With at least three spanning leaves, *every* vertex set satisfies the bound
on its external neighborhood. With only two spanning leaves, the three
specified sets reduce to the degree classes and periphery of paths or cycles.
https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json
-/

namespace Graffiti

open Finset SimpleGraph SupportCounting

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable def externalNeighbors (G : SimpleGraph V) (S : Finset V) : Finset V := by
  classical exact neighborhood G S \ S

@[simp] theorem mem_externalNeighbors {S : Finset V} {v : V} :
    v ∈ externalNeighbors G S ↔ v ∉ S ∧ ∃ w ∈ S, G.Adj v w := by
  classical simp [externalNeighbors, mem_neighborhood_iff, and_comm]

private theorem external_arith {x s n l d : ℕ} (hd : 2 ≤ d) (hl : 3 ≤ l)
    (ho : n + 2 ≤ l + d + 2 * (d / 2)) (hc : x + s ≤ n) (hb : x ≤ s * l) :
    2 * x ≤ d * l := by
  by_cases hs : s ≤ 1
  · have hx : x ≤ l := (hb.trans (Nat.mul_le_mul_right l hs)).trans_eq (one_mul l)
    exact (Nat.mul_le_mul_left 2 hx).trans (Nat.mul_le_mul_right l hd)
  by_cases h3 : l = 3
  · subst l
    by_cases h : s ≤ d / 2 <;> omega
  have hn : n + 2 ≤ l + 2 * d := by omega
  obtain ⟨a,ha⟩ := Nat.exists_eq_add_of_le hd
  obtain ⟨b,hb'⟩ := Nat.exists_eq_add_of_le (show 4 ≤ l by omega)
  rw [ha,hb'] at hn ⊢
  have hs' : 2 ≤ s := by omega
  nlinarith [Nat.zero_le (a*b)]

variable [Nontrivial V]

/-- A common strengthening of 259–261 when a spanning tree has at least three leaves. -/
theorem external_product_of_three_leaves (hG : G.Connected) (hL : 3 ≤ maxLeafCount G) (S : Finset V) :
    2 * (externalNeighbors G S).card ≤ totalDominationNumber G * maxLeafCount G := by
  classical
  apply external_arith (s := S.card) (two_le_totalDominationNumber hG) hL (order_total_leaves hG)
  · have hs : externalNeighbors G S ⊆ Sᶜ := fun x hx => mem_compl.mpr (mem_externalNeighbors.mp hx).1
    have h₁ := card_le_card hs
    have h₂ := card_add_card_compl S
    omega
  · have hs : externalNeighbors G S ⊆ S.biUnion (fun y => G.neighborFinset y) := by
      intro x hx
      obtain ⟨y,hy,hxy⟩ := (mem_externalNeighbors.mp hx).2
      exact mem_biUnion.mpr ⟨y,hy,(G.mem_neighborFinset y x).mpr hxy.symm⟩
    exact (card_le_card hs).trans (card_biUnion_le_card_mul _ _ _ fun y _ => degree_le_maxLeafCount hG y)

private theorem boundary_product (hG : G.Connected) (S : Finset V)
    (hs : maxLeafCount G ≤ 2 → (externalNeighbors G S).card ≤ maxLeafCount G) :
    2 * (externalNeighbors G S).card ≤ totalDominationNumber G * maxLeafCount G := by
  by_cases h : 3 ≤ maxLeafCount G
  · exact external_product_of_three_leaves hG h S
  exact (Nat.mul_le_mul_left _ (hs (by omega))).trans (Nat.mul_le_mul_right _ (two_le_totalDominationNumber hG))

variable [DecidableRel G.Adj]

private theorem boundary_product_of_pendant_compl (hG : G.Connected) (S : Finset V)
    (hs : (∀ v, G.degree v ≤ 2) → ∀ v ∉ S, G.degree v = 1) :
    2 * (externalNeighbors G S).card ≤ totalDominationNumber G * maxLeafCount G := by
  apply boundary_product hG S
  intro hL
  have hdeg := hs fun v => (degree_le_maxLeafCount hG v).trans hL
  apply le_trans (card_le_card (t := pendantVertices G) ?_) (pendants_le_maxLeafCount hG)
  exact fun x hx => mem_filter.mpr ⟨mem_univ _,hdeg x (mem_externalNeighbors.mp hx).1⟩

theorem graffiti259 (hG : G.Connected) :
    2 * (externalNeighbors G (degreeClass G G.maxDegree)).card ≤ totalDominationNumber G * maxLeafCount G := by
  apply boundary_product_of_pendant_compl hG
  intro hd x hx
  have hne := mt (mem_degreeClass (G := G)).mpr hx
  have hmax := G.maxDegree_le_of_forall_degree_le 2 hd
  have hlo := degree_pos_of_connected hG x
  have hhi := G.degree_le_maxDegree x
  omega

omit [DecidableRel G.Adj] in
theorem graffiti260 (hG : G.Connected) :
    2 * (externalNeighbors G (peripheralVertices G)).card ≤ totalDominationNumber G * maxLeafCount G := by
  classical
  apply boundary_product hG
  intro hL
  have hdeg (v : V) := (degree_le_maxLeafCount hG v).trans hL
  have h := peripheral_external_card_le_two G hG hdeg
  have heq : externalNeighbors G (peripheralVertices G) = univ.filter
      (fun x => x ∉ peripheralVertices G ∧ ∃ y ∈ peripheralVertices G, G.Adj x y) := by ext; simp
  rw [heq]
  exact h.trans (two_le_maxLeafCount hG)

theorem graffiti261 (hG : G.Connected) :
    2 * (externalNeighbors G (degreeClass G 2)).card ≤ totalDominationNumber G * maxLeafCount G := by
  apply boundary_product_of_pendant_compl hG
  intro hd x hx
  have hne := mt (mem_degreeClass (G := G)).mpr hx
  have hlo := degree_pos_of_connected hG x
  have hhi := hd x
  omega

end Graffiti
