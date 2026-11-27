import Graffiti.TripleRadius

/-! # Radius and distance domination

Davila, Fast, Henning and Kenter, *Lower bounds on the distance domination
number of a graph*, Corollary 3.5, prove `2 rad(G) ≤ (2k+1) γₖ(G)`.
https://cdm.ucalgary.ca/article/download/62487/46806/178608

Here the proof builds a connected core at a cost of at most `2k` connector
vertices per new dominator and takes a median in a spanning tree of that core.
-/

namespace Graffiti

open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V}

private theorem attach_walk {x y : V} (p : G.Walk x y) {C : Finset V}
    (hx : x ∈ C) (hc : (G.induce (C : Set V)).Connected) :
    ∃ S : Finset V, C ⊆ S ∧ y ∈ S ∧ (G.induce (S : Set V)).Connected ∧ S.card ≤ C.card+p.length := by
  classical
  induction p generalizing C with
  | nil => exact ⟨C,Subset.rfl,hx,hc,by simp⟩
  | @cons x u y e p ih =>
    obtain ⟨S,hs,hy,hS,hsize⟩ := ih (mem_insert_self u C) (connected_insert_neighbor hc hx e)
    have hb := card_insert_le u C
    exact ⟨S,(subset_insert ..).trans hs,hy,hS,by simp only [Walk.length_cons]; omega⟩

/-- A distance-`k` dominating set can be connected by spending at most `2k`
extra vertices per dominator after the first. -/
theorem distance_domination_core (hc : G.Connected) {R : Finset V} {k : ℕ}
    (cover : ∀ v, ∃ r ∈ R, G.dist v r ≤ k) :
    ∃ C : Finset V, R ⊆ C ∧ (G.induce (C : Set V)).Connected ∧
      C.card+2*k ≤ (2*k+1)*R.card := by
  classical
  choose g hmem near using cover
  let f (v : V) := if v ∈ R then v else g v
  have fmem (v : V) : f v ∈ R := by dsimp [f]; split <;> first | assumption | exact hmem v
  have fix {v : V} (hv : v ∈ R) : f v = v := if_pos hv
  have close (v : V) : G.dist v (f v) ≤ k := by
    by_cases h : v ∈ R
    · simp [fix h,dist_self]
    · simpa [f,h] using near v
  obtain ⟨v⟩ := hc.nonempty
  let r := g v
  have hr : r ∈ R := hmem v
  let rec grow (C : Finset V) (hseed : r ∈ C) (hC : (G.induce (C : Set V)).Connected)
      (cost : C.card+2*k ≤ (2*k+1)*(C ∩ R).card) :
      ∃ S : Finset V, R ⊆ S ∧ (G.induce (S : Set V)).Connected ∧ S.card+2*k ≤ (2*k+1)*R.card := by
    by_cases done_ : R ⊆ C
    · exact ⟨C,done_,hC,by rwa [inter_eq_right.mpr done_] at cost⟩
    obtain ⟨b,hb,hout⟩ := not_subset.mp done_
    obtain ⟨w⟩ := hc r b
    obtain ⟨e,_,ha,he⟩ := w.exists_boundary_dart {x | f x ∈ C}
      (show f r ∈ C by simpa [fix hr] using hseed) (show f b ∉ C by simpa [fix hb] using hout)
    have d1 := hc.dist_triangle (u := f e.fst) (v := e.fst) (w := f e.snd)
    have d2 := hc.dist_triangle (u := e.fst) (v := e.snd) (w := f e.snd)
    rw [dist_comm (u := f e.fst) (v := e.fst)] at d1
    rw [dist_eq_one_iff_adj.mpr e.adj] at d2
    obtain ⟨q,hq⟩ := hc.exists_walk_length_eq_dist (f e.fst) (f e.snd)
    obtain ⟨S,hs,hin,hS,hcard⟩ := attach_walk q ha hC
    have inc : (C ∩ R).card < (S ∩ R).card := by
      apply card_lt_card; apply Finset.ssubset_iff_subset_ne.mpr; constructor
      · exact inter_subset_inter hs Subset.rfl
      · intro eq
        have hm : f e.snd ∈ S ∩ R := mem_inter.mpr ⟨hin,fmem _⟩
        rw [← eq] at hm; exact he (mem_inter.mp hm).1
    apply grow S (hs hseed) hS
    have len : q.length ≤ 2*k+1 := by have := close e.fst; have := close e.snd; omega
    have hmul : (2*k+1)*((C ∩ R).card+1) ≤ (2*k+1)*(S ∩ R).card := Nat.mul_le_mul_left _ inc
    rw [Nat.mul_add,Nat.mul_one] at hmul
    omega
  termination_by (by classical exact R.card-(C ∩ R).card : ℕ)
  decreasing_by
    classical
    have hcap : (S ∩ R).card ≤ R.card := card_le_card inter_subset_right
    omega
  apply grow {r} (mem_singleton_self _)
  · rw [coe_singleton,induce_singleton_eq_top]
    letI : Nonempty ({r} : Set V) := ⟨⟨r,Set.mem_singleton r⟩⟩
    exact top_connected
  · rw [inter_eq_left.mpr (singleton_subset_iff.mpr hr),card_singleton,Nat.mul_one]; omega

/-- The radius lower bound for distance domination, for every witnessing set
rather than just the minimum. It also covers radius-zero domination. -/
theorem radius_distance_domination [Fintype V] (hc : G.Connected) {R : Finset V} {k : ℕ}
    (cover : ∀ v, ∃ r ∈ R, G.dist v r ≤ k) : 2*G.radius.toNat ≤ (2*k+1)*R.card := by
  classical
  obtain ⟨C,hr,hC,cost⟩ := distance_domination_core hc cover
  obtain ⟨T,hTH,ht⟩ := hC.exists_isTree_le
  obtain ⟨c,hcent⟩ := tree_half_order_center ht
  obtain ⟨w,hw⟩ := G.exists_edist_eq_eccent_of_finite c.val
  obtain ⟨r,hm,hn⟩ := cover w
  let u : (C : Set V) := ⟨r,hr hm⟩
  have hc' := hcent u
  rw [← Nat.card_eq_fintype_card,Set.Nat.card_coe_set_eq,Set.ncard_coe_Finset] at hc'
  obtain ⟨p,hp⟩ := ht.isConnected.exists_walk_length_eq_dist c u
  let f : T →g G := { toFun := Subtype.val, map_rel' := fun h => hTH h }
  have hd : G.dist c.val r ≤ T.dist c u := by simpa only [Walk.length_map,hp] using dist_le (p.map f)
  have tri := hc.dist_triangle (u := c.val) (v := r) (w := w)
  rw [dist_comm (u := r) (v := w)] at tri
  have bound : G.radius.toNat ≤ G.dist c.val w := ENat.toNat_le_toNat
    ((G.radius_le_eccent (u := c.val)).trans_eq hw.symm) (edist_ne_top_iff_reachable.mpr (hc c.val w))
  omega

end Graffiti
