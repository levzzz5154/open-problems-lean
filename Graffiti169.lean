import Graffiti258

/-! # Written on the Wall II, 169: spread of the even-distance counts

https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json

Both distance parities satisfy the same bound in a parity-preserving spanning
tree. The constant is attained by every star with at least two leaves. The
catalog does not exclude the one-vertex graph; under the degree-one definition
of a leaf it is the unique connected order for which the inequality fails.
-/

namespace Graffiti

open Finset SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable def minEvenLayerCount (G : SimpleGraph V) [Nonempty V] : ℕ := by
  classical
  exact univ.inf' univ_nonempty fun r => (univ.filter fun v => Even (G.dist r v)).card

theorem even_parity_spread [Nontrivial V] (hG : G.Connected) (u v : V) :
    (univ.filter fun x => Even (G.dist u x)).card + 1 ≤
      maxLeafCount G + (univ.filter fun x => Even (G.dist v x)).card := by
  classical
  have he := (parity_card_bounds hG u).1
  have ho := (parity_card_bounds hG v).2
  have hc := card_add_card_compl (univ.filter fun x => Even (G.dist v x))
  omega

/-- The catalog inequality with no truncated subtraction. -/
theorem graffiti169 [Nontrivial V] (hG : G.Connected) :
    maxEvenLayerCount G + 1 ≤ maxLeafCount G + minEvenLayerCount G := by
  classical
  let E (r : V) := (univ.filter fun x => Even (G.dist r x)).card
  obtain ⟨u, _, hu⟩ := univ.exists_mem_eq_sup univ_nonempty E
  obtain ⟨v, _, hv⟩ := exists_mem_eq_inf' (s := univ) univ_nonempty E
  change univ.sup E + 1 ≤ maxLeafCount G + univ.inf' univ_nonempty E
  rw [hu,hv]
  exact even_parity_spread hG u v

/-- No tree of order at least three has every vertex a leaf. -/
theorem maxLeafCount_lt_order (hn : 2 < Fintype.card V) : maxLeafCount G < Fintype.card V := by
  classical
  suffices maxLeafCount G ≤ Fintype.card V - 1 by omega
  apply Finset.sup_le
  intro T hT
  obtain ⟨_,ht⟩ := (mem_filter.mp hT).2
  have hle := (pendantVertices T).card_le_univ
  by_contra! h
  have he : (pendantVertices T).card = Fintype.card V := by omega
  have hall := (card_eq_iff_eq_univ _).mp he
  have deg (x : V) : T.degree x = 1 := (mem_filter.mp (hall ▸ mem_univ x : x ∈ pendantVertices T)).2
  have hs := T.sum_degrees_eq_twice_card_edges
  simp only [deg, sum_const, card_univ, smul_eq_mul, mul_one] at hs
  have hc := ht.card_edgeFinset
  omega

/-- Every `K₁,ₖ`, `k ≥ 2`, is an equality case, for arbitrarily large spread. -/
theorem graffiti169_star (k : ℕ) (hk : 2 ≤ k) :
    let G := completeBipartiteGraph Unit (Fin k)
    maxLeafCount G = k ∧ maxEvenLayerCount G + 1 = maxLeafCount G + minEvenLayerCount G := by
  classical
  let G := completeBipartiteGraph Unit (Fin k)
  let c : Unit ⊕ Fin k := Sum.inl ()
  let f : Fin k → Unit ⊕ Fin k := Sum.inr
  let a : Fin k := ⟨0, by omega⟩
  let E (r : Unit ⊕ Fin k) := univ.filter fun x => Even (G.dist r x)
  have cross (i : Fin k) : G.Adj c (f i) := by simp [G,c,f,completeBipartiteGraph]
  have hc : G.Connected := (connected_iff_exists_forall_reachable G).mpr ⟨c, fun x => by
    rcases x with ⟨⟩ | i
    · exact Reachable.rfl
    · exact (cross i).reachable⟩
  have horder : Fintype.card (Unit ⊕ Fin k) = 1 + k := by simp
  letI : Nontrivial (Unit ⊕ Fin k) := ⟨⟨c, f a, (cross a).ne⟩⟩
  have hem : (E c).card ≤ 1 := by
    apply card_le_one.mpr
    have only (x : Unit ⊕ Fin k) (hx : x ∈ E c) : x = c := by
      rcases x with ⟨⟩ | i
      · rfl
      · change f i ∈ E c at hx
        simp [E,dist_eq_one_iff_adj.mpr (cross i)] at hx
    intro x hx y hy
    exact (only x hx).trans (only y hy).symm
  have hl (i : Fin k) : f i ∈ E (f a) := by
    apply mem_filter.mpr ⟨mem_univ _, ?_⟩
    by_cases he : a = i
    · simp [he,dist_self]
    have hne : f a ≠ f i := fun e => he (Sum.inr.inj e)
    have h0 : G.dist (f a) (f i) ≠ 0 := fun e => hne (hc.dist_eq_zero_iff.mp e)
    have h1 : G.dist (f a) (f i) ≠ 1 := by
      intro e
      have := dist_eq_one_iff_adj.mp e
      simp [f,G,completeBipartiteGraph] at this
    have h2 := hc.dist_triangle (u := f a) (v := c) (w := f i)
    rw [dist_eq_one_iff_adj.mpr (cross a).symm, dist_eq_one_iff_adj.mpr (cross i)] at h2
    rw [show G.dist (f a) (f i) = 2 by omega]
    decide
  have hlo : (univ : Finset (Fin k)).card ≤ (E (f a)).card :=
    card_le_card_of_injOn f (fun i _ => hl i) (fun _ _ _ _ e => Sum.inr.inj e)
  simp only [card_univ,Fintype.card_fin] at hlo
  have hmin : minEvenLayerCount G ≤ (E c).card := inf'_le _ (mem_univ c)
  have hmax : (E (f a)).card ≤ maxEvenLayerCount G :=
    le_sup (f := fun r => (E r).card) (mem_univ (f a))
  have hupper := maxLeafCount_lt_order (G := G) (show 2 < Fintype.card (Unit ⊕ Fin k) by omega)
  have hspread := graffiti169 hc
  change maxLeafCount G = k ∧ maxEvenLayerCount G + 1 = maxLeafCount G + minEvenLayerCount G
  constructor <;> omega

/-- With the catalog's degree-one leaf convention, order one is an actual exception. -/
theorem graffiti169_singleton [Subsingleton V] [Nonempty V] (G : SimpleGraph V) :
    ¬ maxEvenLayerCount G + 1 ≤ maxLeafCount G + minEvenLayerCount G := by
  classical
  let r : V := Classical.choice inferInstance
  let E (u : V) := (univ.filter fun x => Even (G.dist u x)).card
  have hmin : minEvenLayerCount G ≤ E r := inf'_le _ (mem_univ r)
  have hmax : E r ≤ maxEvenLayerCount G := le_sup (mem_univ r)
  have hz : maxLeafCount G ≤ 0 := by
    apply Finset.sup_le
    intro T _
    have hp : pendantVertices T = ∅ := by
      apply eq_empty_of_forall_not_mem
      intro x hx
      have he : T.degree x = 1 := (mem_filter.mp hx).2
      obtain ⟨y,hy⟩ := (T.degree_pos_iff_exists_adj x).mp (by omega)
      exact hy.ne (Subsingleton.elim x y)
    simp [hp]
  omega

end Graffiti
