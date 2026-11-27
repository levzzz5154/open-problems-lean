import Graffiti.Peeling
import Mathlib.Combinatorics.SimpleGraph.Path

/-! # Written on the Wall II, 434a and 434b

Source: https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json.
Here the Szekeres–Wilf invariant is degeneracy, not degeneracy plus one:
https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/definitions.json (119).
-/

namespace Graffiti

variable {V : Type*} [Fintype V] [DecidableEq V]

private noncomputable def neighborsIn (G : SimpleGraph V) (S : Finset V) (v : V) : Finset V := by
  classical exact S.filter (G.Adj v)

private noncomputable def minimumOn (G : SimpleGraph V) (S : Finset V) : ℕ := by
  classical exact if h : S.Nonempty then S.inf' h (fun v => (neighborsIn G S v).card) else 0

/-- The maximum of the minimum degrees of the induced subgraphs. This is also
the maximum over all subgraphs, since adding the missing edges cannot lower
the minimum degree. -/
noncomputable def degeneracy (G : SimpleGraph V) : ℕ :=
  (Finset.univ : Finset (Finset V)).sup (minimumOn G)

def maxVertices (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter (fun x => G.degree x = G.maxDegree)

omit [DecidableEq V] in
@[simp] theorem mem_maxVertices {G : SimpleGraph V} [DecidableRel G.Adj] {v : V} :
    v ∈ maxVertices G ↔ G.degree v = G.maxDegree := by simp [maxVertices]


theorem peel_univ (G : SimpleGraph V) : PeelsAt G Finset.univ (degeneracy Gᶜ + 1) := by
  classical
  intro S _ hS
  obtain ⟨v,hv,hmin⟩ := S.exists_mem_eq_inf' hS (fun w => (neighborsIn Gᶜ S w).card)
  have hle : minimumOn Gᶜ S ≤ degeneracy Gᶜ := Finset.le_sup (f := minimumOn Gᶜ) (Finset.mem_univ S)
  rw [minimumOn,dif_pos hS,hmin] at hle
  have hN : v ∉ neighborsIn Gᶜ S v := by simp [neighborsIn]
  have he : room G S v = insert v (neighborsIn Gᶜ S v) := by
    ext y
    by_cases h : y = v
    · subst y; simp [hv]
    · simp [neighborsIn,h,Ne.symm h,SimpleGraph.compl_adj]
  exact ⟨v,hv,by rw [he,Finset.card_insert_of_not_mem hN]; omega⟩

theorem full_room_degree (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (room G Finset.univ v).card + G.degree v = Fintype.card V := by
  classical
  have he : room G Finset.univ v = (G.neighborFinset v)ᶜ := by ext w; simp
  rw [he,Nat.add_comm,← SimpleGraph.card_neighborFinset_eq_degree]
  exact Finset.card_add_card_compl _

theorem exists_large (G : SimpleGraph V) : ExtendsTo G Finset.univ (independentDominationNumber G) := by
  classical
  intro B _ hb
  obtain ⟨I,hBI,hI,hdom⟩ := extend_independent G hb
  exact ⟨I,hBI,Finset.subset_univ _,hI,Nat.sInf_le ⟨I,hI,hdom,rfl⟩⟩

omit [Fintype V] [DecidableEq V] in
private theorem singleton_indep (G : SimpleGraph V) (v : V) : G.IsIndepSet (({v} : Finset V) : Set V) := by
  rw [Finset.coe_singleton]; exact Set.pairwise_singleton _ _

theorem room_large (G : SimpleGraph V) (v : V) :
    independentDominationNumber G ≤ (room G Finset.univ v).card := by
  obtain ⟨I,hs,_,hi,hsize⟩ := exists_large G {v} (Finset.subset_univ _) (singleton_indep G v)
  exact hsize.trans (Finset.card_le_card (fun y hy => (mem_room G).mpr
    ⟨Finset.mem_univ _,independent_nonadj G hi (hs (Finset.mem_singleton_self v)) hy⟩))

/-- The elementary universal bound, with no well-coveredness assumption. -/
theorem independent_domination_le_degeneracy_succ (G : SimpleGraph V) [Nonempty V] :
    independentDominationNumber G ≤ degeneracy Gᶜ + 1 := by
  obtain ⟨v,_,hv⟩ := peel_univ G Finset.univ (Finset.Subset.rfl) Finset.univ_nonempty
  exact (room_large G v).trans hv

/-- The equality case forces every maximum-degree vertex to have a
maximum-degree neighbor, provided the graph has an edge. -/
theorem adjacent_max_of_extremal (G : SimpleGraph V) [DecidableRel G.Adj]
    (edge : ∃ x y, G.Adj x y) (ht : degeneracy Gᶜ < independentDominationNumber G)
    {v : V} (hv : v ∈ maxVertices G) : ∃ w ∈ maxVertices G, G.Adj v w := by
  classical
  let k := degeneracy Gᶜ + 1
  have hki : k ≤ independentDominationNumber G := ht
  let S : Finset V := Finset.univ
  have low := peel_univ G
  have hdeg := (mem_maxVertices.mp hv).ge
  obtain ⟨a,_,ha⟩ := low S (Finset.Subset.rfl) ⟨v,Finset.mem_univ _⟩
  have hvsize : (room G S v).card ≤ k := by
    have hle := (G.degree_le_maxDegree a).trans hdeg
    have h₁ := full_room_degree G a
    have h₂ := full_room_degree G v
    dsimp only [S,k] at *; omega
  have large : ExtendsTo G S k := by
    intro B hB hi
    obtain ⟨I,hBI,hIS,hI,hc⟩ := exists_large G B hB hi
    exact ⟨I,hBI,hIS,hI,hki.trans hc⟩
  obtain ⟨I,hvI,hIS,hi,hsize⟩ := large {v} (Finset.subset_univ _) (singleton_indep G v)
  have hr : I = room G S v := Finset.eq_of_subset_of_card_le
    (fun y hy => (mem_room G).mpr ⟨hIS hy,independent_nonadj G hi (hvI (Finset.mem_singleton_self v)) hy⟩)
    (hvsize.trans hsize)
  obtain ⟨x,y,he⟩ := edge
  have hmiss : ∃ z ∈ S, z ∉ I := by
    by_cases hx : x ∈ I
    · exact ⟨y,Finset.mem_univ _,fun hy => independent_nonadj G hi hx hy he⟩
    · exact ⟨x,Finset.mem_univ _,hx⟩
  obtain ⟨w,hw,hwI,hwc⟩ := low_outside_clique G S I k hIS hi hmiss low large
  have hvlarge : k ≤ (room G S v).card := hr ▸ hsize
  have hm : G.degree w = G.maxDegree := by
    have hwdeg := G.degree_le_maxDegree w
    have h₁ := full_room_degree G v
    have h₂ := full_room_degree G w
    dsimp only [S] at *; omega
  refine ⟨w,mem_maxVertices.mpr hm,?_⟩
  by_contra hn
  exact hwI (hr ▸ (mem_room G).mpr ⟨hw,hn⟩)

omit [DecidableEq V] in
private theorem edge_of_connected (G : SimpleGraph V) (hc : G.Connected) (hn : 3 < Fintype.card V) :
    ∃ x y, G.Adj x y := by
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  by_contra! h
  have he : G = ⊥ := by ext x y; simp [h]
  exact SimpleGraph.bot_not_preconnected (he ▸ hc.preconnected)

/-- WOW II 434a: the floor is applied to half the Szekeres–Wilf invariant. -/
theorem conjecture434a (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected) (hn : 3 < Fintype.card V) :
    independentDominationNumber G ≤ (maxVertices G).card + 2 * (degeneracy Gᶜ / 2) := by
  classical
  letI : Nonempty V := hc.nonempty
  obtain ⟨v,hv⟩ := G.exists_maximal_degree_vertex
  have hvM : v ∈ maxVertices G := mem_maxVertices.mpr hv.symm
  have h₁ : 0 < (maxVertices G).card := Finset.card_pos.mpr ⟨v,hvM⟩
  have hb := independent_domination_le_degeneracy_succ G
  by_cases ht : degeneracy Gᶜ < independentDominationNumber G
  · obtain ⟨w,hw,ha⟩ := adjacent_max_of_extremal G (edge_of_connected G hc hn) ht hvM
    have h₂ : 1 < (maxVertices G).card := Finset.one_lt_card.mpr ⟨v,hvM,w,hw,ha.ne⟩
    omega
  · omega

/-- WOW II 434b, both clauses: the stronger bound in fact requires **no**
restriction on the diameter. -/
theorem conjecture434b (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected) (hn : 3 < Fintype.card V) :
    independentDominationNumber G ≤ (G.induce (maxVertices G : Set V)).minDegree + degeneracy Gᶜ := by
  classical
  letI : Nonempty V := hc.nonempty
  have hb := independent_domination_le_degeneracy_succ G
  by_cases ht : degeneracy Gᶜ < independentDominationNumber G
  · obtain ⟨v,hv⟩ := G.exists_maximal_degree_vertex
    letI : Nonempty (maxVertices G : Set V) := ⟨⟨v,mem_maxVertices.mpr hv.symm⟩⟩
    have hδ : 1 ≤ (G.induce (maxVertices G : Set V)).minDegree := by
      apply SimpleGraph.le_minDegree_of_forall_le_degree
      intro z
      obtain ⟨w,hw,ha⟩ := adjacent_max_of_extremal G (edge_of_connected G hc hn) ht z.property
      exact (SimpleGraph.degree_pos_iff_exists_adj _ _).mpr ⟨⟨w,hw⟩,ha⟩
    omega
  · omega

end Graffiti
