import Graffiti.DistanceDomination
import Graffiti.ForcedSupports

/-! # Written on the Wall II, conjecture 362

The tree assumption is unnecessary. Pick one support from every component of
the graph induced by the supports and the leaves. These representatives are
independent and forced into every total dominating set. Removing them leaves
a distance-two dominating set. The radius bound of Davila–Fast–Henning–Kenter
then yields a stronger inequality for all finite connected graphs of order ≥2.

https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json
-/

namespace Graffiti

open Finset SimpleGraph SupportCounting

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def supportLeafComponents : ℕ :=
  Nat.card (G.induce ((supportVertices G ∪ degreeClass G 1 : Finset V) : Set V)).ConnectedComponent

/-- Components are represented by supports even when the chosen initial
representative happens to be a pendant. -/
private theorem support_representatives {D : Finset V} (hd : TotallyDominates G D) :
    ∃ I : Finset V, I.card = supportLeafComponents G ∧ I ⊆ D ∧ G.IsIndepSet (I : Set V) := by
  classical
  let S := supportVertices G
  let X := S ∪ degreeClass G 1
  let H := G.induce (X : Set V)
  letI : Finite H.ConnectedComponent := Quot.finite _
  letI : Fintype H.ConnectedComponent := Fintype.ofFinite _
  have rep (c : H.ConnectedComponent) : ∃ u : (X : Set V), u.val ∈ S ∧ H.connectedComponentMk u = c := by
    induction c using ConnectedComponent.ind with
    | h u =>
      by_cases h : u.val ∈ S
      · exact ⟨u,h,rfl⟩
      have hl := (mem_degreeClass G).mp ((mem_union.mp u.property).resolve_left h)
      obtain ⟨y,_,hy⟩ := hd u.val
      have hs : y ∈ S := (support_iff_pendant G).mpr ⟨u.val,hl,hy.symm⟩
      let y' : (X : Set V) := ⟨y,mem_union_left _ hs⟩
      exact ⟨y',hs,ConnectedComponent.connectedComponentMk_eq_of_adj (show H.Adj y' u from hy.symm)⟩
  choose g hs hg using rep
  let f (c : H.ConnectedComponent) : V := (g c).val
  have inj : Function.Injective f := by
    intro c d h
    exact (hg c).symm.trans ((congrArg H.connectedComponentMk (Subtype.ext h)).trans (hg d))
  let I := univ.image f
  refine ⟨I,?_,?_,?_⟩
  · change (univ.image f).card = Nat.card H.ConnectedComponent
    rw [card_image_of_injective _ inj,card_univ,Nat.card_eq_fintype_card]
  · intro x hx; obtain ⟨c,_,rfl⟩ := mem_image.mp hx
    exact support_forced G hd (hs c)
  · intro x hx y hy hne ha
    obtain ⟨c,_,rfl⟩ := mem_image.mp hx
    obtain ⟨d,_,rfl⟩ := mem_image.mp hy
    have e : H.Adj (g c) (g d) := ha
    exact hne (congrArg f ((hg c).symm.trans ((ConnectedComponent.connectedComponentMk_eq_of_adj e).trans (hg d))))

/-- Twice the radius plus five times the component count fits into five
times the size of every total dominating set. -/
theorem support_components_radius_budget (hc : G.Connected) {D : Finset V} (hd : TotallyDominates G D) :
    2*G.radius.toNat + 5*supportLeafComponents G ≤ 5*D.card ∧ supportLeafComponents G < D.card := by
  classical
  obtain ⟨I,hnum,hin,hi⟩ := support_representatives G hd
  let R := D \ I
  have cover (x : V) : ∃ r ∈ R, G.dist x r ≤ 2 := by
    obtain ⟨y,hy,hxy⟩ := hd x
    by_cases h : y ∈ I
    · obtain ⟨z,hz,hyz⟩ := hd y
      refine ⟨z,mem_sdiff.mpr ⟨hz,fun h' => hi h h' hyz.ne hyz⟩,?_⟩
      have he := hc.dist_triangle (u := x) (v := y) (w := z)
      rwa [dist_eq_one_iff_adj.mpr hxy,dist_eq_one_iff_adj.mpr hyz] at he
    · exact ⟨y,mem_sdiff.mpr ⟨hy,h⟩,by simp [dist_eq_one_iff_adj.mpr hxy]⟩
  have hr := radius_distance_domination hc cover
  have part : R.card+I.card = D.card := card_sdiff_add_card_eq_card hin
  obtain ⟨x⟩ := hc.nonempty
  obtain ⟨r,hm,_⟩ := cover x
  have := card_pos.mpr ⟨r,hm⟩
  omega

theorem graffiti362_connected [Nontrivial V] (hc : G.Connected) :
    3*supportLeafComponents G + 1 + G.radius.toNat ≤ 3*totalDominationNumber G := by
  obtain ⟨D,hD,hmin⟩ := exists_min_total_set hc
  obtain ⟨bound,strict⟩ := support_components_radius_budget G hc hD
  omega

theorem graffiti362 (ht : G.IsTree) (hn : 2 < Fintype.card V) :
    3*supportLeafComponents G + 1 + G.radius.toNat ≤ 3*totalDominationNumber G := by
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  exact graffiti362_connected G ht.isConnected

end Graffiti
