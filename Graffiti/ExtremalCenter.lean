import Graffiti434

/-! The equality case of the independent domination versus degeneracy bound:
vertices of eccentricity at most two form a dominating set. -/

namespace Graffiti

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
private theorem neighbor_of_distinct (G : SimpleGraph V) (hc : G.Connected)
    {x y : V} (h : x ≠ y) : ∃ z, G.Adj x z := by
  obtain ⟨p⟩ := hc.preconnected x y
  cases p with
  | nil => exact (h rfl).elim
  | cons e _ => exact ⟨_, e⟩

private theorem max_room_independent (G : SimpleGraph V) [DecidableRel G.Adj]
    (ht : degeneracy Gᶜ < independentDominationNumber G) {m : V} (hm : m ∈ maxVertices G) :
    G.IsIndepSet (room G Finset.univ m : Set V) := by
  classical
  obtain ⟨a, _, ha⟩ := peel_univ G Finset.univ Finset.Subset.rfl ⟨m, Finset.mem_univ _⟩
  have ham := (G.degree_le_maxDegree a).trans (mem_maxVertices.mp hm).ge
  have h₁ := full_room_degree G a
  have h₂ := full_room_degree G m
  have hs : G.IsIndepSet (({m} : Finset V) : Set V) := by
    rw [Finset.coe_singleton]; exact Set.pairwise_singleton _ _
  obtain ⟨I, hsub, _, hI, hcard⟩ := exists_large G {m} (Finset.subset_univ _) hs
  have hmI := hsub (Finset.mem_singleton_self m)
  have he : I = room G Finset.univ m := Finset.eq_of_subset_of_card_le
    (fun _ hy => (mem_room G).mpr ⟨Finset.mem_univ _, independent_nonadj G hI hmI hy⟩) (by omega)
  rwa [← he]

/-- If neither vertex has a maximum-degree neighbor, their open neighborhoods are nested. -/
private theorem nested_of_extremal (G : SimpleGraph V) [DecidableRel G.Adj]
    (ht : degeneracy Gᶜ < independentDominationNumber G) (u v : V)
    (hu : ∀ x, G.Adj u x → x ∉ maxVertices G) (hv : ∀ x, G.Adj v x → x ∉ maxVertices G) :
    G.neighborFinset u ⊆ G.neighborFinset v ∨ G.neighborFinset v ⊆ G.neighborFinset u := by
  classical
  by_cases huv : G.neighborFinset u ⊆ G.neighborFinset v
  · exact Or.inl huv
  right
  by_contra hvu
  obtain ⟨a, hau, hav⟩ := Finset.not_subset.mp huv
  obtain ⟨b, hbv, hbu⟩ := Finset.not_subset.mp hvu
  let X := G.neighborFinset u ∪ G.neighborFinset v
  have memX {x : V} : x ∈ X ↔ G.Adj u x ∨ G.Adj v x := by simp [X]
  let B := Finset.univ.filter (fun y => ∃ x ∈ X, ¬ G.Adj x y)
  have memB {y : V} : y ∈ B ↔ ∃ x ∈ X, ¬ G.Adj x y := by simp [B]
  have huB : u ∈ B := memB.mpr ⟨b, Finset.mem_union_right _ hbv,
    fun e => hbu ((G.mem_neighborFinset u b).mpr e.symm)⟩
  have hvB : v ∈ B := memB.mpr ⟨a, Finset.mem_union_left _ hau,
    fun e => hav ((G.mem_neighborFinset v a).mpr e.symm)⟩
  obtain ⟨y, hyB, hsmall⟩ := peel_univ G B (Finset.subset_univ _) ⟨u, huB⟩
  by_cases hy : y ∈ X
  · -- All of y's complement-neighbors survived, and y is nonmaximum in G.
    have he : room G B y = room G Finset.univ y := by
      ext z
      simp only [mem_room, Finset.mem_univ, true_and]
      exact ⟨And.right, fun h => ⟨memB.mpr ⟨y, hy, h⟩, h⟩⟩
    rw [he] at hsmall
    have hyn : y ∉ maxVertices G := (memX.mp hy).elim (hu y) (hv y)
    have hydeg := lt_of_le_of_ne (G.degree_le_maxDegree y) (fun h => hyn (mem_maxVertices.mpr h))
    letI : Nonempty V := ⟨y⟩
    obtain ⟨m, hm⟩ := G.exists_maximal_degree_vertex
    have h₁ := full_room_degree G y
    have h₂ := full_room_degree G m
    have h₃ := room_large G m
    omega
  · -- A full independent set through x and y survives, with another compatible vertex.
    obtain ⟨x, hx, hxy⟩ := memB.mp hyB
    obtain ⟨w, hwB, hwx, hwy⟩ : ∃ w ∈ B, G.Adj w x ∧ ¬ G.Adj w y := by
      rcases memX.mp hx with e | e
      · exact ⟨u, huB, e, fun h => hy (memX.mpr (Or.inl h))⟩
      · exact ⟨v, hvB, e, fun h => hy (memX.mpr (Or.inr h))⟩
    have hp : G.IsIndepSet (({x, y} : Finset V) : Set V) := by
      intro s hs t ht' _
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hs ht'
      rcases hs with rfl | rfl <;> rcases ht' with rfl | rfl <;>
        first | exact G.loopless _ | exact hxy | exact fun e => hxy e.symm
    obtain ⟨I, hpair, _, hi, hsize⟩ := exists_large G {x, y} (Finset.subset_univ _) hp
    have hxI := hpair (by simp : x ∈ ({x, y} : Finset V))
    have hyI := hpair (by simp : y ∈ ({x, y} : Finset V))
    have hwI : w ∉ I := fun h => independent_nonadj G hi h hxI hwx
    have hsub : insert w I ⊆ room G B y := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact (mem_room G).mpr ⟨hwB, fun e => hwy e.symm⟩
      · exact (mem_room G).mpr ⟨memB.mpr ⟨x, hx, independent_nonadj G hi hxI hz⟩,
          independent_nonadj G hi hyI hz⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_insert_of_not_mem hwI] at hc
    omega

/-- In the extremal case, every vertex is at distance at most one from a vertex
whose distance to every vertex is at most two. Distances are exhibited by edges. -/
theorem extremal_center_cover (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (ht : degeneracy Gᶜ < independentDominationNumber G) (v : V) :
    ∃ c, (v = c ∨ G.Adj v c) ∧ ∀ x, x = c ∨ G.Adj c x ∨ ∃ y, G.Adj c y ∧ G.Adj y x := by
  classical
  letI : Nonempty V := hc.nonempty
  have viaMax {m w x : V} (hm : m ∈ maxVertices G) (hmw : ¬ G.Adj m w) (hwx : G.Adj w x) :
      G.Adj m x := by
    by_contra hmx
    exact independent_nonadj G (max_room_independent G ht hm)
      ((mem_room G).mpr ⟨Finset.mem_univ _, hmw⟩) ((mem_room G).mpr ⟨Finset.mem_univ _, hmx⟩) hwx
  have centralMax {m : V} (hm : m ∈ maxVertices G) (x : V) :
      x = m ∨ G.Adj m x ∨ ∃ y, G.Adj m y ∧ G.Adj y x := by
    by_cases he : x = m
    · exact Or.inl he
    by_cases e : G.Adj m x
    · exact Or.inr (Or.inl e)
    obtain ⟨y, ey⟩ := neighbor_of_distinct G hc he
    exact Or.inr (Or.inr ⟨y, viaMax hm e ey, ey.symm⟩)
  by_cases hvM : v ∈ maxVertices G
  · exact ⟨v, Or.inl rfl, centralMax hvM⟩
  by_cases hvN : ∃ m ∈ maxVertices G, G.Adj v m
  · obtain ⟨m, hm, e⟩ := hvN
    exact ⟨m, Or.inr e, centralMax hm⟩
  let W := Finset.univ.filter (fun z => z ∉ maxVertices G ∧ ¬ ∃ m ∈ maxVertices G, G.Adj z m)
  have memW {z : V} : z ∈ W ↔ z ∉ maxVertices G ∧ ¬ ∃ m ∈ maxVertices G, G.Adj z m := by
    simp only [W, Finset.mem_filter, Finset.mem_univ, true_and]
  have hvW := memW.mpr ⟨hvM, hvN⟩
  obtain ⟨w, hw, hmin⟩ := W.exists_min_image (fun z => (G.neighborFinset z).card) ⟨v, hvW⟩
  have miss {z : V} (hz : z ∈ W) : ∀ x, G.Adj z x → x ∉ maxVertices G :=
    fun x e hm => (memW.mp hz).2 ⟨x, hm, e⟩
  have least {z : V} (hz : z ∈ W) : G.neighborFinset w ⊆ G.neighborFinset z := by
    rcases nested_of_extremal G ht w z (miss hw) (miss hz) with h | h
    · exact h
    · exact le_of_eq (Finset.eq_of_subset_of_card_le h (hmin z hz)).symm
  obtain ⟨m, hm⟩ := G.exists_maximal_degree_vertex
  have hmM : m ∈ maxVertices G := mem_maxVertices.mpr hm.symm
  have hwm : w ≠ m := by
    rintro rfl
    exact (memW.mp hw).1 hmM
  obtain ⟨c, he⟩ := neighbor_of_distinct G hc hwm
  have coverW {z : V} (hz : z ∈ W) : G.Adj z c :=
    (G.mem_neighborFinset z c).mp (least hz ((G.mem_neighborFinset w c).mpr he))
  have coverM {z : V} (hz : z ∈ maxVertices G) : G.Adj z c :=
    viaMax hz (fun e => miss hw z e.symm hz) he
  refine ⟨c, Or.inr (coverW hvW), ?_⟩
  intro x
  by_cases hxM : x ∈ maxVertices G
  · exact Or.inr (Or.inl (coverM hxM).symm)
  by_cases hxN : ∃ z ∈ maxVertices G, G.Adj x z
  · obtain ⟨z, hz, e⟩ := hxN
    exact Or.inr (Or.inr ⟨z, (coverM hz).symm, e.symm⟩)
  · exact Or.inr (Or.inl (coverW (memW.mpr ⟨hxM, hxN⟩)).symm)

end Graffiti
