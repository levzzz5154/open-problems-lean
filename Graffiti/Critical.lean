import Graffiti426
import Graffiti315

/-! # Critical independent sets and pendant exchanges

The difference is integer-valued, not truncated subtraction. A *maximum
critical* independent set maximizes cardinality among all maximizers of that
difference. Its union with the other maximum critical sets need not be independent.
-/

namespace Graffiti

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

noncomputable def criticalScore (I : Finset V) : ℤ := (I.card : ℤ) - (neighborhood G I).card

def CriticalIndependent (I : Finset V) : Prop := G.IsIndepSet (I : Set V) ∧
  ∀ J : Finset V, G.IsIndepSet (J : Set V) → criticalScore G J ≤ criticalScore G I

def MaximumCriticalIndependent (I : Finset V) : Prop := CriticalIndependent G I ∧
  ∀ J : Finset V, CriticalIndependent G J → J.card ≤ I.card

noncomputable def criticalHull : Finset V := by
  classical
  exact univ.filter fun v => ∃ I : Finset V, MaximumCriticalIndependent G I ∧ v ∈ I

theorem exists_maximumCriticalIndependent : ∃ I, MaximumCriticalIndependent G I := by
  classical
  let F := univ.filter fun I : Finset V => G.IsIndepSet (I : Set V)
  have h0 : G.IsIndepSet ((∅ : Finset V) : Set V) := by simp [IsIndepSet]
  obtain ⟨A,hA,hscore⟩ := F.exists_max_image (criticalScore G) ⟨∅, mem_filter.mpr ⟨mem_univ _,h0⟩⟩
  have ha : CriticalIndependent G A := ⟨(mem_filter.mp hA).2,
    fun J hj => hscore J (mem_filter.mpr ⟨mem_univ _,hj⟩)⟩
  let C := univ.filter (CriticalIndependent G)
  obtain ⟨I,hI,hcard⟩ := C.exists_max_image card ⟨A, mem_filter.mpr ⟨mem_univ _,ha⟩⟩
  exact ⟨I, (mem_filter.mp hI).2, fun J hj => hcard J (mem_filter.mpr ⟨mem_univ _,hj⟩)⟩

variable [DecidableRel G.Adj]

omit [DecidableEq V] in
/-- The unique neighbor, with both directions of the adjacency description. -/
theorem pendant_neighbor {x : V} (hx : x ∈ pendantVertices G) :
    ∃ c, G.Adj x c ∧ ∀ w, G.Adj x w → w = c := by
  obtain ⟨c, he⟩ := card_eq_one.mp (show (G.neighborFinset x).card = 1 from (mem_filter.mp hx).2)
  refine ⟨c, (G.mem_neighborFinset _ _).mp (he ▸ mem_singleton_self _), fun w hw => ?_⟩
  exact mem_singleton.mp (he ▸ (G.mem_neighborFinset _ _).mpr hw)

omit [DecidableRel G.Adj] in
/-- If a maximum critical set omits a pendant, insert the pendant and erase its
unique neighbor. The new set is again maximum critical. -/
theorem critical_pendant_exchange {I : Finset V} (hI : MaximumCriticalIndependent G I)
    {x c : V} (hmiss : x ∉ I) (hxy : G.Adj x c) (hu : ∀ w, G.Adj x w → w = c) :
    MaximumCriticalIndependent G (insert x (I.erase c)) := by
  classical
  let J := insert x (I.erase c)
  have notin : x ∉ I.erase c := fun h => hmiss (mem_erase.mp h).2
  have hK : G.IsIndepSet ((I.erase c : Finset V) : Set V) :=
    fun _ ha _ hb h => hI.1.1 (mem_erase.mp ha).2 (mem_erase.mp hb).2 h
  have hJ : G.IsIndepSet (J : Set V) := by
    change G.IsIndepSet ((insert x (I.erase c) : Finset V) : Set V)
    rw [coe_insert]
    exact hK.insert_of_symmetric (fun _ _ hn ha => hn ha.symm)
      (fun w hw _ ha => (mem_erase.mp hw).1 (hu w ha))
  have sub : neighborhood G J ⊆ insert c (neighborhood G I) := by
    intro z hz
    obtain ⟨w,hw,ha⟩ := mem_neighborhood_iff.mp hz
    rcases mem_insert.mp hw with rfl | h
    · exact mem_insert.mpr (Or.inl (hu z ha.symm))
    · exact mem_insert_of_mem (mem_neighborhood_iff.mpr ⟨w,(mem_erase.mp h).2,ha⟩)
  have hcard : J.card = (I.erase c).card + 1 := card_insert_of_not_mem notin
  have his : I.card ≤ J.card := by
    by_cases hc : c ∈ I
    · have := card_erase_add_one hc; omega
    · rw [hcard, erase_eq_of_not_mem hc]; omega
  have better : criticalScore G I ≤ criticalScore G J := by
    unfold criticalScore
    by_cases hc : c ∈ I
    · have hxN : x ∈ neighborhood G I := mem_neighborhood_iff.mpr ⟨c,hc,hxy⟩
      have sub' : neighborhood G J ⊆ insert c ((neighborhood G I).erase x) := by
        intro z hz
        rcases mem_insert.mp (sub hz) with he | hn
        · exact mem_insert.mpr (Or.inl he)
        · apply mem_insert_of_mem
          refine mem_erase.mpr ⟨?_, hn⟩
          rintro rfl
          obtain ⟨w,hw,ha⟩ := mem_neighborhood_iff.mp hz
          exact hJ (mem_insert_self _ _) hw ha.ne ha
      have hn := (card_le_card sub').trans (card_insert_le _ _)
      have hcN := card_erase_add_one hxN
      omega
    · have hn := (card_le_card sub).trans (card_insert_le _ _)
      rw [erase_eq_of_not_mem hc] at hcard
      omega
  exact ⟨⟨hJ, fun K hK => (hI.1.2 K hK).trans better⟩, fun K hK => (hI.2 K hK).trans his⟩

/-- Any independent collection of pendants can be included *simultaneously*,
not just vertex by vertex in possibly different maximum critical sets. -/
theorem exists_maximumCritical_cover_pendants (P : Finset V) (hP : P ⊆ pendantVertices G)
    (hi : G.IsIndepSet (P : Set V)) : ∃ I, MaximumCriticalIndependent G I ∧ P ⊆ I := by
  classical
  obtain ⟨A,hA⟩ := exists_maximumCriticalIndependent G
  let F := univ.filter (MaximumCriticalIndependent G)
  obtain ⟨I,hI,hbest⟩ := F.exists_max_image (fun I => (I ∩ P).card)
    ⟨A, mem_filter.mpr ⟨mem_univ _,hA⟩⟩
  have hm := (mem_filter.mp hI).2
  refine ⟨I,hm,fun x hx => ?_⟩
  by_contra hmiss
  obtain ⟨c,ha,hu⟩ := pendant_neighbor G (hP hx)
  have hc : c ∉ P := fun h => hi hx h ha.ne ha
  let J := insert x (I.erase c)
  have hj : MaximumCriticalIndependent G J := critical_pendant_exchange G hm hmiss ha hu
  have hsub : insert x (I ∩ P) ⊆ J ∩ P := by
    intro y hy
    rcases mem_insert.mp hy with rfl | h
    · exact mem_inter.mpr ⟨mem_insert_self _ _,hx⟩
    · obtain ⟨hyI,hyP⟩ := mem_inter.mp h
      exact mem_inter.mpr ⟨mem_insert_of_mem (mem_erase.mpr ⟨fun e => hc (e ▸ hyP),hyI⟩),hyP⟩
  have hjcard := card_le_card hsub
  rw [card_insert_of_not_mem (fun h => hmiss (mem_inter.mp h).1)] at hjcard
  have hle := hbest J (mem_filter.mpr ⟨mem_univ _, hj⟩)
  omega

theorem pendants_subset_criticalHull : pendantVertices G ⊆ criticalHull G := by
  classical
  intro x hx
  obtain ⟨I,hI,hi⟩ := exists_maximumCritical_cover_pendants G {x} (singleton_subset_iff.mpr hx)
    (by simp [IsIndepSet])
  exact mem_filter.mpr ⟨mem_univ _, I, hI, hi (mem_singleton_self _)⟩

end Graffiti
