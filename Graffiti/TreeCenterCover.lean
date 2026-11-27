import Graffiti.CenterDepth
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace Graffiti

open SimpleGraph

variable {V : Type*} {T : SimpleGraph V}

/-- Split at the edge with zero-based index `n`. -/
private theorem split_at_edge {a b : V} (p : T.Walk a b) (n : ℕ) (hn : n < p.length) :
    ∃ (x y : V) (l : T.Walk a x) (e : T.Adj x y) (r : T.Walk y b),
      p = l.append (.cons e r) ∧ l.length = n := by
  induction p generalizing n with
  | nil => simp at hn
  | cons e p ih =>
    cases n with
    | zero => exact ⟨_, _, .nil, e, p, rfl, rfl⟩
    | succ n =>
      have hn' : n < p.length := by simpa only [Walk.length_cons, Nat.succ_eq_add_one,
        Nat.add_lt_add_iff_right] using hn
      obtain ⟨x, y, l, d, r, rfl, hl⟩ := ih n hn'
      exact ⟨x, y, .cons e l, d, r, rfl, by simp [hl]⟩

private theorem via_vertex {a b x : V} (p : T.Walk a b) (hx : x ∈ p.support) :
    T.dist a x + T.dist x b ≤ p.length := by
  obtain ⟨q, r, rfl⟩ := Walk.mem_support_iff_exists_append.mp hx
  rw [Walk.length_append]
  exact Nat.add_le_add (dist_le q) (dist_le r)

variable [Fintype V] [DecidableEq V]

/-- One of the endpoints of the middle edge of a positive-length diametral path is
within half the diameter of each vertex. The path through a given vertex need not
be simple, but erasing its loops recovers the unique path between the endpoints. -/
private theorem tree_middle_edge (hT : T.IsTree) (hpos : 0 < T.diam) :
    ∃ x y, T.Adj x y ∧ ∀ v, T.dist x v ≤ T.diam / 2 ∨ T.dist y v ≤ T.diam / 2 := by
  classical
  haveI : Nonempty V := hT.isConnected.nonempty
  have hfin : T.ediam ≠ ⊤ := connected_iff_ediam_ne_top.mp hT.isConnected
  obtain ⟨a, b, hab⟩ := T.exists_dist_eq_diam
  obtain ⟨p, hp, hlen⟩ := hT.isConnected.exists_path_of_dist a b
  obtain ⟨x, y, l, e, r, hsplit, hl⟩ := split_at_edge p (T.diam / 2) (by omega)
  have hsum : l.length + (r.length + 1) = T.diam := by
    simpa only [hsplit, Walk.length_append, Walk.length_cons] using hlen.trans hab
  have hay : T.diam / 2 + 1 ≤ T.dist a y := by
    have h := hT.isConnected.dist_triangle (u := a) (v := y) (w := b)
    have hr := dist_le r
    omega
  have hxb : T.diam - T.diam / 2 ≤ T.dist x b := by
    have h := hT.isConnected.dist_triangle (u := a) (v := x) (w := b)
    have hleft := dist_le l
    omega
  have he : s(x, y) ∈ p.edges := by simp [hsplit, Walk.edges_append, Walk.edges_cons]
  refine ⟨x, y, e, fun v => ?_⟩
  obtain ⟨q, hq⟩ := hT.isConnected.exists_walk_length_eq_dist a v
  obtain ⟨s, hs⟩ := hT.isConnected.exists_walk_length_eq_dist v b
  have hpath := (hT.existsUnique_path a b).unique hp (q.append s).bypass_isPath
  have hmem : s(x, y) ∈ (q.append s).edges :=
    (q.append s).edges_bypass_subset (hpath ▸ he)
  rw [Walk.edges_append, List.mem_append] at hmem
  rcases hmem with h | h
  · right
    have hvia := via_vertex q (q.snd_mem_support_of_mem_edges h)
    have hdiam := T.dist_le_diam (u := a) (v := v) hfin
    omega
  · left
    have hvia := via_vertex s (s.fst_mem_support_of_mem_edges h)
    have hdiam := T.dist_le_diam (u := v) (v := b) hfin
    rw [dist_comm (G := T) (u := x) (v := v)]
    omega

omit [DecidableEq V] in
/-- If two adjacent vertices jointly cover to distance `r`, each has eccentricity
at most `r+1`. Either the radius is already at most `r`, or both are centers. -/
private theorem centerDepth_le_of_edge_cover {G : SimpleGraph V} (hG : G.Connected)
    {x y : V} {r : ℕ} (hxy : G.Adj x y) (hcover : ∀ v, G.dist x v ≤ r ∨ G.dist y v ≤ r) :
    centerDepth G ≤ r := by
  haveI : Nonempty V := hG.nonempty
  have hfin : G.radius ≠ ⊤ := radius_ne_top_iff.mpr hG
  by_cases hsmall : G.radius.toNat ≤ r
  · obtain ⟨c, hc⟩ := G.exists_eccent_eq_radius
    apply centerDepth_le
    intro v
    refine ⟨c, hc, ?_⟩
    have h : G.edist c v ≤ G.radius := (edist_le_eccent (G := G)).trans_eq hc
    exact (ENat.toNat_le_toNat h hfin).trans hsmall
  · have center_of_bound (w : V) (hb : ∀ v, G.dist w v ≤ r + 1) : w ∈ G.center := by
      rw [mem_center_iff]
      apply le_antisymm _ G.radius_le_eccent
      rw [← ENat.coe_toNat hfin]
      apply iSup_le
      intro v
      rw [← ENat.coe_toNat (edist_ne_top_iff_reachable.mpr (hG w v))]
      apply ENat.coe_le_coe.mpr
      change G.dist w v ≤ G.radius.toNat
      have := hb v
      omega
    have h1 : G.dist x y = 1 := dist_eq_one_iff_adj.mpr hxy
    have h2 : G.dist y x = 1 := dist_eq_one_iff_adj.mpr hxy.symm
    have hx : x ∈ G.center := center_of_bound x fun v => by
      rcases hcover v with h | h
      · omega
      · have := hG.dist_triangle (u := x) (v := y) (w := v)
        omega
    have hy : y ∈ G.center := center_of_bound y fun v => by
      rcases hcover v with h | h
      · have := hG.dist_triangle (u := y) (v := x) (w := v)
        omega
      · omega
    apply centerDepth_le
    intro v
    exact (hcover v).elim (fun h => ⟨x, hx, h⟩) (fun h => ⟨y, hy, h⟩)

theorem centerDepth_le_tree_diam (G T : SimpleGraph V) (hTG : T ≤ G) (hT : T.IsTree) :
    2 * centerDepth G ≤ T.diam := by
  haveI : Nonempty V := hT.isConnected.nonempty
  have hanti (u v : V) : G.dist u v ≤ T.dist u v := (hT.isConnected u v).dist_anti hTG
  suffices h : centerDepth G ≤ T.diam / 2 by omega
  by_cases hzero : T.diam = 0
  · obtain ⟨c, hc⟩ := G.center_nonempty
    apply centerDepth_le
    intro v
    refine ⟨c, hc, ?_⟩
    have h := T.dist_le_diam (u := c) (v := v) (connected_iff_ediam_ne_top.mp hT.isConnected)
    have := hanti c v
    omega
  · obtain ⟨x, y, he, hcover⟩ := tree_middle_edge hT (Nat.pos_of_ne_zero hzero)
    apply centerDepth_le_of_edge_cover (hT.isConnected.mono hTG) (hTG he)
    intro v
    exact (hcover v).imp ((hanti x v).trans ·) ((hanti y v).trans ·)

end Graffiti
