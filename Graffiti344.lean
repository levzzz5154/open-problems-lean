import Graffiti362
import Graffiti342

/-! # Written on the Wall II, conjecture 344

Each isolated support has its own support–leaf component. This gives enough
slack in conjecture 342 except when there is just one component and one
isolated support. In that case the unique support is the hub of a star.
-/

namespace Graffiti

open Finset SimpleGraph SupportCounting

variable {V : Type*} [Fintype V] [DecidableEq V] {T : SimpleGraph V} [DecidableRel T.Adj]

private abbrev SL (T : SimpleGraph V) [DecidableRel T.Adj] :=
  T.induce ((supportVertices T ∪ degreeClass T 1 : Finset V) : Set V)

private def supportComponent {s : V} (hs : s ∈ supportVertices T) : (SL T).ConnectedComponent :=
  (SL T).connectedComponentMk ⟨s, mem_union_left _ hs⟩

/-- A walk starting at an isolated support stays at that support or at one of
its private pendant neighbors. In particular it cannot reach another support. -/
private theorem eq_of_same_component {s t : V} (hs : s ∈ isolatedSupports T)
    (ht : t ∈ supportVertices T) (he : supportComponent (mem_filter.mp hs).1 = supportComponent ht) :
    t = s := by
  let X := ((supportVertices T ∪ degreeClass T 1 : Finset V) : Set V)
  let P (x : X) := x.val = s ∨ (x.val ∉ supportVertices T ∧ T.degree x.val = 1 ∧ T.Adj x.val s)
  have step {x y : X} (h : (SL T).Adj x y) : P x → P y := by
    have exy : T.Adj x.val y.val := h
    rintro (e | ⟨_, hl, hxs⟩)
    · rw [e] at exy
      have hn : y.val ∉ supportVertices T := by
        intro hy
        have hz : ((supportVertices T).filter (T.Adj s)).card = 0 := (mem_filter.mp hs).2
        exact (Nat.ne_of_gt (card_pos.mpr ⟨_, mem_filter.mpr ⟨hy, exy⟩⟩)) hz
      exact Or.inr ⟨hn, (mem_degreeClass T).mp ((mem_union.mp y.property).resolve_left hn), exy.symm⟩
    · exact Or.inl (unique_neighbor_at_leaf T hl exy hxs)
  have along {x y : X} (p : (SL T).Walk x y) : P x → P y := by
    induction p with
    | nil => exact id
    | cons e _ ih => exact fun h => ih (step e h)
  obtain ⟨p⟩ := ConnectedComponent.exact he
  exact (along p (Or.inl rfl)).elim id (fun h => (h.1 ht).elim)

/-- A vertex farthest from the unique support must be a leaf. Its neighbor
is therefore that support, so every vertex has distance at most one to it. -/
private theorem universal_of_unique_support [Nontrivial V] (ht : T.IsTree) {s : V}
    (hu : ∀ t ∈ supportVertices T, t = s) :
    ∀ v, v ≠ s → T.Adj v s := by
  obtain ⟨x, _, hmax⟩ := (univ : Finset V).exists_max_image (fun v => T.dist v s) ⟨s, mem_univ _⟩
  intro v hvs
  have hv := hmax v (mem_univ _)
  have hp : 0 < T.dist v s := Nat.pos_of_ne_zero (fun h => hvs (ht.isConnected.dist_eq_zero_iff.mp h))
  have hxs : x ≠ s := fun e => by
    have hz : T.dist x s = 0 := by rw [e, dist_self]
    omega
  have hl : T.degree x = 1 := by
    have hpos := degree_pos_of_connected ht.isConnected x
    have hn : ¬ 1 < T.degree x := by
      intro h
      obtain ⟨_, b, _, _, _, hb⟩ := exists_straddling_neighbors ht hxs h
      have := hmax b (mem_univ _)
      omega
    omega
  obtain ⟨y, hxy⟩ := (T.degree_pos_iff_exists_adj x).mp (by omega)
  have e := hu y ((support_iff_pendant T).mpr ⟨x, hl, hxy.symm⟩)
  have hd := dist_eq_one_iff_adj.mpr (e ▸ hxy : T.Adj x s)
  exact dist_eq_one_iff_adj.mp (by omega)

/-- The hub and any neighbor form both a total dominating pair in the tree
and an admissible pair for annihilation in the complement. -/
private theorem star_bounds [Nontrivial V] {s : V} (hu : ∀ x, x ≠ s → T.Adj x s) :
    totalDominationNumber T ≤ 2 ∧ 2 ≤ annihilationNumber Tᶜ := by
  obtain ⟨z, hz⟩ := exists_ne s
  have hD : TotallyDominates T {z, s} := by
    intro x
    rcases eq_or_ne x s with rfl | hx
    · exact ⟨z, mem_insert_self .., (hu z hz).symm⟩
    · exact ⟨s, by simp, hu x hx⟩
  constructor
  · exact Nat.sInf_le ⟨{z,s}, hD, card_pair hz⟩
  · have hzdeg : Tᶜ.degree s = 0 := by
      by_contra! h
      obtain ⟨y, hy⟩ := (Tᶜ.degree_pos_iff_exists_adj s).mp (Nat.pos_of_ne_zero h)
      exact ((T.compl_adj s y).mp hy).2 (hu y hy.ne.symm).symm
    have hed : Tᶜ.degree z ≤ Tᶜ.edgeFinset.card := by
      rw [← card_incidenceFinset_eq_degree, incidenceFinset_eq_filter]
      exact card_filter_le ..
    have hsum : ∑ v ∈ ({z,s} : Finset V), Tᶜ.degree v ≤ Tᶜ.edgeFinset.card := by
      simpa [hz, hzdeg] using hed
    simpa [hz] using card_le_annihilationNumber Tᶜ hsum

/-- Written on the Wall II 344, with annihilation taken in the complement. -/
theorem graffiti344 (ht : T.IsTree) (hn : 2 < Fintype.card V) :
    totalDominationNumber T + 1 ≤ annihilationNumber Tᶜ + supportLeafComponents T := by
  classical
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  letI : Finite (SL T).ConnectedComponent := Quot.finite _
  letI : Fintype (SL T).ConnectedComponent := Fintype.ofFinite _
  have hcard : supportLeafComponents T = Fintype.card (SL T).ConnectedComponent :=
    Nat.card_eq_fintype_card
  obtain ⟨r⟩ := ht.isConnected.nonempty
  have hleaves := tree_leaf_bounds ht r
  obtain ⟨l, hl⟩ := card_pos.mp (show 0 < (pendantVertices T).card by omega)
  obtain ⟨s, hls⟩ := (T.degree_pos_iff_exists_adj l).mp (by have := (mem_filter.mp hl).2; omega)
  have hs : s ∈ supportVertices T := (support_iff_pendant T).mpr ⟨l, (mem_filter.mp hl).2, hls.symm⟩
  have hpos : 0 < supportLeafComponents T := by
    rw [hcard, Fintype.card_pos_iff]; exact ⟨supportComponent hs⟩
  let f (i : isolatedSupports T) := supportComponent (mem_filter.mp i.property).1
  have hinj : Function.Injective f := fun i j h => Subtype.ext
    (eq_of_same_component i.property (mem_filter.mp j.property).1 h).symm
  have hcount : (isolatedSupports T).card ≤ supportLeafComponents T := by
    rw [hcard, ← Fintype.card_coe]; exact Fintype.card_le_of_injective f hinj
  have h342 := graffiti342 ht hn
  by_cases special : supportLeafComponents T = 1 ∧ (isolatedSupports T).card = 1
  · obtain ⟨i, hi⟩ := card_pos.mp (show 0 < (isolatedSupports T).card by omega)
    have uniq : ∀ t ∈ supportVertices T, t = i := fun t ht' => eq_of_same_component hi ht'
      (Fintype.card_le_one_iff.mp (by omega : Fintype.card (SL T).ConnectedComponent ≤ 1) _ _)
    obtain ⟨hdom, hann⟩ := star_bounds (universal_of_unique_support ht uniq)
    omega
  · omega

end Graffiti

#print axioms Graffiti.graffiti344
