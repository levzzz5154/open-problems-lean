import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Data.Set.Card

namespace Graffiti

open SimpleGraph

variable {V : Type*} {T : SimpleGraph V}

private theorem dist_via_support {a b m : V} (p : T.Walk a b) (hm : m ∈ p.support) :
    T.dist a m + T.dist m b ≤ p.length := by
  obtain ⟨q, r, rfl⟩ := Walk.mem_support_iff_exists_append.mp hm
  rw [Walk.length_append]
  exact Nat.add_le_add (dist_le q) (dist_le r)

/-- Removing an interior vertex of a tree path separates its endpoints: from
any `v`, one endpoint is strictly farther than the interior vertex. -/
theorem tree_interior_dist_lt (ht : T.IsTree) {a b m : V} {p : T.Walk a b}
    (hp : p.IsPath) (hm : m ∈ p.support) (hma : m ≠ a) (hmb : m ≠ b) (v : V) :
    T.dist m v < T.dist a v ∨ T.dist m v < T.dist b v := by
  classical
  obtain ⟨q, hq⟩ := ht.isConnected.exists_walk_length_eq_dist a v
  obtain ⟨s, hs⟩ := ht.isConnected.exists_walk_length_eq_dist v b
  have he := (ht.existsUnique_path a b).unique hp (q.append s).bypass_isPath
  have h := (q.append s).support_bypass_subset (he ▸ hm)
  rcases (q.mem_support_append_iff s).mp h with h | h
  · left
    have := dist_via_support q h
    have := ht.isConnected.pos_dist_of_ne hma.symm
    omega
  · right
    have := dist_via_support s h
    have := ht.isConnected.pos_dist_of_ne hmb
    rw [dist_comm (G := T) (u := m) (v := v), dist_comm (G := T) (u := b) (v := v)]
    omega

/-- The middle of a two-edge tree path is the only vertex within distance
one of both endpoints. This excludes triangles as well as quadrilaterals. -/
theorem eq_middle_of_dist_le_one (ht : T.IsTree) {a m b x : V}
    (ha : T.Adj m a) (hb : T.Adj m b) (hne : a ≠ b)
    (hax : T.dist a x ≤ 1) (hbx : T.dist b x ≤ 1) : x = m := by
  let p : T.Walk a b := .cons ha.symm (.cons hb .nil)
  have hp : p.IsPath := by simp [p, Walk.isPath_def, ha.ne.symm, hne, hb.ne]
  have h := tree_interior_dist_lt ht hp (show m ∈ p.support by simp [p]) ha.ne hb.ne x
  exact (ht.isConnected.dist_eq_zero_iff.mp (show T.dist m x = 0 by omega)).symm

variable [Finite V]

/-- Choosing a farthest vertex from `r` realizes a bound on all distances
from every center simultaneously. -/
theorem exists_dist_bound_for_centers (ht : T.IsTree) (r : V) :
    ∃ w, ∀ c ∈ T.center, ∀ v, T.dist c v ≤ T.dist r w := by
  obtain ⟨w, hw⟩ := T.exists_edist_eq_eccent_of_finite r
  refine ⟨w, fun c hc v => ?_⟩
  apply ENat.toNat_le_toNat _ (edist_ne_top_iff_reachable.mpr (ht.isConnected r w))
  rw [hw]
  exact (edist_le_eccent (G := T)).trans ((show T.eccent c = T.radius from hc).le.trans
    T.radius_le_eccent)

/-- Any two distinct center vertices of a finite tree are adjacent. -/
theorem tree_center_adj (ht : T.IsTree) {a b : V} (ha : a ∈ T.center) (hb : b ∈ T.center)
    (hne : a ≠ b) : T.Adj a b := by
  by_contra hnon
  have hdist := ht.isConnected.one_lt_dist_of_ne_of_not_adj hne hnon
  obtain ⟨p, hp, hl⟩ := ht.isConnected.exists_path_of_dist a b
  let m := p.getVert 1
  have hma : m ≠ a := fun h => by have := (hp.getVert_eq_start_iff (by omega)).mp h; omega
  have hmb : m ≠ b := fun h => by have := (hp.getVert_eq_end_iff (by omega)).mp h; omega
  obtain ⟨w, hw⟩ := exists_dist_bound_for_centers ht m
  exact (tree_interior_dist_lt ht hp (p.getVert_mem_support 1) hma hmb w).elim
    (not_lt_of_ge (hw a ha w)) (not_lt_of_ge (hw b hb w))

/-- The center of a finite tree has at most two vertices. -/
theorem tree_center_ncard_le_two (ht : T.IsTree) : T.center.ncard ≤ 2 := by
  by_contra! h
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := (Set.two_lt_ncard_iff T.center.toFinite).mp h
  have e₁ := tree_center_adj ht ha hb hab
  have e₂ := tree_center_adj ht ha hc hac
  have e₃ := tree_center_adj ht hc hb hbc.symm
  exact e₁.ne.symm (eq_middle_of_dist_le_one ht e₁ e₂ hbc (by simp [dist_self])
    (dist_eq_one_iff_adj.mpr e₃).le)

end Graffiti
