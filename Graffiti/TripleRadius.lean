import Graffiti258
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Tauto

/-! # Radius versus three-point separation

Given three vertices in a finite tree, minimize the sum of distances to them.
Across any edge incident with the minimizer, at most one terminal can lie on
the far side. A path in the near side thus pays for the separation of a pair;
a path from the edge to an arbitrary vertex pays for its radius contribution.
The two paths have disjoint vertex sets. Applied to a spanning tree of a
connected dominating core, this yields a metric bound for the original graph.
-/

namespace Graffiti

open SimpleGraph Finset

variable {V : Type*} [Fintype V] {T G : SimpleGraph V}

private noncomputable def side (H : SimpleGraph V) (x : V) : Finset V := by
  classical exact univ.filter (H.Reachable x)

private theorem side_card {H : SimpleGraph V} (hle : H ≤ T) {o a b : V}
    (ha : H.Reachable o a) (hb : H.Reachable o b) : T.dist a b + 1 ≤ (side H o).card := by
  classical
  obtain ⟨q,hq,hl⟩ := (ha.symm.trans hb).exists_path_of_dist
  have sub : q.support.toFinset ⊆ side H o := by
    intro v hv; apply mem_filter.mpr; refine ⟨mem_univ _,ha.trans ?_⟩
    exact (q.takeUntil v (List.mem_toFinset.mp hv)).reachable
  have h := card_le_card sub
  rw [List.toFinset_card_of_nodup hq.support_nodup,Walk.length_support,hl] at h
  exact (Nat.add_le_add_right ((ha.symm.trans hb).dist_anti hle) _).trans h

omit [Fintype V] in
private theorem closer_across {c z t : V} (hc : T.Connected)
    (h : ¬ (T.deleteEdges {s(c,z)}).Reachable c t) : T.dist z t + 1 ≤ T.dist c t := by
  classical
  obtain ⟨p,hp,hl⟩ := hc.exists_path_of_dist c t
  have useEdge : s(c,z) ∈ p.edges := by
    by_contra notUsed; exact h (reachable_delete_edges_iff_exists_walk.mpr ⟨p,notUsed⟩)
  cases p with
  | nil => simp at useEdge
  | @cons _ u _ e q =>
    have hn := (Walk.cons_isPath_iff e q).mp hp
    have ha : s(_,z) ∉ q.edges := fun he => hn.2 (q.fst_mem_support_of_mem_edges he)
    simp only [Walk.edges_cons,List.mem_cons,ha,or_false] at useEdge
    have he : z = u := by simpa [e.ne] using useEdge
    subst u
    have hd := dist_le q
    simp only [Walk.length_cons] at hl
    omega

private theorem toward_side (ht : T.IsTree) {c w : V} (hw : c ≠ w) :
    ∃ z, T.Adj c z ∧ T.dist c w ≤ (side (T.deleteEdges {s(c,z)}) z).card := by
  classical
  obtain ⟨p,hp,hl⟩ := ht.isConnected.exists_path_of_dist c w
  cases p with
  | nil => exact (hw rfl).elim
  | @cons c z w ec q =>
    let H := T.deleteEdges {s(c,z)}
    have hzq : H.Reachable z w := reachable_delete_edges_iff_exists_walk.mpr ⟨q,fun he =>
      ((Walk.cons_isPath_iff ec q).mp hp).2 (q.fst_mem_support_of_mem_edges he)⟩
    have far := side_card (T.deleteEdges_le {s(c,z)}) (o := z) Reachable.rfl hzq
    have step := ht.isConnected.dist_triangle (u := c) (v := z) (w := w)
    rw [dist_eq_one_iff_adj.mpr ec] at step
    exact ⟨z,ec,(step.trans_eq (Nat.add_comm ..)).trans far⟩

/-- A median of all vertices of a finite tree is within half its order of
each vertex. Moving one step toward a heavier branch would decrease the
total distance, so no branch at a median contains more than half the tree. -/
theorem tree_half_order_center (ht : T.IsTree) :
    ∃ c, ∀ w, 2*T.dist c w ≤ Fintype.card V := by
  classical
  haveI : Nonempty V := ht.isConnected.nonempty
  let F (c : V) := ∑ u, T.dist c u
  obtain ⟨c,_,best⟩ := univ.exists_min_image F univ_nonempty
  refine ⟨c,fun w => ?_⟩
  by_cases e : c = w
  · simp [e,dist_self]
  obtain ⟨z,ec,hfar⟩ := toward_side ht e
  let H := T.deleteEdges {s(c,z)}
  let S := side H z
  have hz : ¬ H.Reachable c z := (isBridge_iff.mp
    ((isAcyclic_iff_forall_adj_isBridge.mp ht.IsAcyclic) ec)).2
  have inside (u : V) (hu : u ∈ S) : T.dist z u + 1 ≤ T.dist c u := by
    apply closer_across ht.isConnected
    exact fun h => hz (h.trans (((mem_filter.mp hu).2 : H.Reachable z u).symm))
  have outside (u : V) (_ : u ∈ Sᶜ) : T.dist z u ≤ T.dist c u + 1 := by
    simpa [dist_eq_one_iff_adj.mpr ec.symm, Nat.add_comm] using
      ht.isConnected.dist_triangle (u := z) (v := c) (w := u)
  have hi := sum_le_sum inside
  have ho := sum_le_sum outside
  simp only [sum_add_distrib,sum_const_zero,sum_const,Nat.smul_one_eq_cast,Nat.cast_id] at hi ho
  have hc := S.sum_add_sum_compl (T.dist c)
  have hs := S.sum_add_sum_compl (T.dist z)
  have hm := best z (mem_univ z)
  dsimp only [F] at hm
  change T.dist c w ≤ S.card at hfar
  have := card_add_card_compl S
  omega

/-- A tree with three pairwise `s`-separated terminals has a vertex whose
maximum distance plus `s` is at most its number of edges. Terminals may repeat. -/
theorem tree_three_separation (ht : T.IsTree) {a b v : V} {s : ℕ}
    (hab : s ≤ T.dist a b) (hav : s ≤ T.dist a v) (hbv : s ≤ T.dist b v) :
    ∃ c, ∀ w, T.dist c w + s + 1 ≤ Fintype.card V := by
  classical
  haveI : Nonempty V := ht.isConnected.nonempty
  let F (c : V) := T.dist c a + T.dist c b + T.dist c v
  obtain ⟨c,_,best⟩ := univ.exists_min_image F univ_nonempty
  refine ⟨c,fun w => ?_⟩
  by_cases hw : c = w
  · subst w
    have h := (side_card (T := T) (H := T) le_rfl (o := a) Reachable.rfl (ht.isConnected a b)).trans
      (side T a).card_le_univ
    simp only [dist_self,zero_add]; omega
  · obtain ⟨z,ec,far⟩ := toward_side ht hw
    let H := T.deleteEdges {s(c,z)}
    have hle : H ≤ T := T.deleteEdges_le _
    have hz : ¬ H.Reachable c z := (isBridge_iff.mp ((isAcyclic_iff_forall_adj_isBridge.mp ht.IsAcyclic) ec)).2
    have dis : Disjoint (side H c) (side H z) := by
      apply disjoint_left.mpr; intro u hu hv
      exact hz (((mem_filter.mp hu).2 : H.Reachable c u).trans ((mem_filter.mp hv).2 : H.Reachable z u).symm)
    have budget := (side H c ∪ side H z).card_le_univ
    rw [card_union_of_disjoint dis] at budget
    change T.dist c w ≤ (side H z).card at far
    have approx (u : V) : T.dist z u ≤ 1 + T.dist c u := by
      simpa [dist_eq_one_iff_adj.mpr ec.symm] using ht.isConnected.dist_triangle (u := z) (v := c) (w := u)
    have minsum := best z (mem_univ z)
    dsimp [F] at minsum
    have move (u : V) (h : ¬ H.Reachable c u) : T.dist z u + 1 ≤ T.dist c u :=
      closer_across ht.isConnected h
    have two : (H.Reachable c a ∧ H.Reachable c b) ∨ (H.Reachable c a ∧ H.Reachable c v) ∨
        (H.Reachable c b ∧ H.Reachable c v) := by
      have ab (na : ¬ H.Reachable c a) (nb : ¬ H.Reachable c b) : False := by
        have := move _ na; have := move _ nb; have := approx v; omega
      have av (na : ¬ H.Reachable c a) (nv : ¬ H.Reachable c v) : False := by
        have := move _ na; have := move _ nv; have := approx b; omega
      have bv (nb : ¬ H.Reachable c b) (nv : ¬ H.Reachable c v) : False := by
        have := move _ nb; have := move _ nv; have := approx a; omega
      tauto
    rcases two with ⟨ha,hb⟩ | ⟨ha,hv⟩ | ⟨hb,hv⟩
    · have := side_card hle ha hb; omega
    · have := side_card hle ha hv; omega
    · have := side_card hle hb hv; omega

/-- A connected total dominating core of size `m` gives radius plus any
three-point separation at most `m+2`, with ambient graph distances. -/
theorem radius_separation_core (hc : G.Connected) {C : Finset V}
    (hC : (G.induce (C : Set V)).Connected) (hD : TotallyDominates G C)
    {a b v : V} {s : ℕ} (hab : s ≤ G.dist a b) (hav : s ≤ G.dist a v) (hbv : s ≤ G.dist b v) :
    G.radius.toNat + s ≤ C.card + 2 := by
  classical
  let H := G.induce (C : Set V)
  obtain ⟨T,hTH,ht⟩ := hC.exists_isTree_le
  have i (x y : (C : Set V)) : G.dist x.val y.val ≤ T.dist x y := by
    obtain ⟨p,hp⟩ := ht.isConnected.exists_walk_length_eq_dist x y
    let f : T →g G := { toFun := Subtype.val, map_rel' := fun h => hTH h }
    have h := dist_le (p.map f)
    simpa only [Walk.length_map,hp] using h
  choose f hmem hadj using hD
  let g (u : V) : (C : Set V) := ⟨f u,hmem u⟩
  have project (u w : V) : G.dist u w ≤ T.dist (g u) (g w) + 2 := by
    have h1 := hc.dist_triangle (u := u) (v := f u) (w := w)
    have h2 := hc.dist_triangle (u := f u) (v := f w) (w := w)
    rw [dist_eq_one_iff_adj.mpr (hadj u)] at h1
    rw [dist_eq_one_iff_adj.mpr (hadj w).symm] at h2
    have h3 : G.dist (f u) (f w) ≤ T.dist (g u) (g w) := i (g u) (g w)
    omega
  obtain ⟨c,cover⟩ := tree_three_separation (a := g a) (b := g b) (v := g v) (s := s-2) ht
    (by have := project a b; omega) (by have := project a v; omega) (by have := project b v; omega)
  have cr : ∀ w : V, G.dist c.val w + s ≤ C.card + 2 := by
    intro w
    have hc' := cover (g w)
    rw [← Nat.card_eq_fintype_card,Set.Nat.card_coe_set_eq,Set.ncard_coe_Finset] at hc'
    have hg : G.dist c.val (f w) ≤ T.dist c (g w) := i c (g w)
    have h := hc.dist_triangle (u := c.val) (v := f w) (w := w)
    rw [dist_eq_one_iff_adj.mpr (hadj w).symm] at h
    omega
  obtain ⟨w,hw⟩ := G.exists_edist_eq_eccent_of_finite c.val
  have er := ENat.toNat_le_toNat ((G.radius_le_eccent (u := c.val)).trans_eq hw.symm)
    (edist_ne_top_iff_reachable.mpr (hc c.val w))
  exact (Nat.add_le_add_right er s).trans (cr w)

end Graffiti
