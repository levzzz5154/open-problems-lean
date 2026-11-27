import Graffiti363

namespace Graffiti

open Finset SimpleGraph

/-- Round a three-side budget in the graph of relays. A diametral side is
strictly longer than the distance of a nonperipheral vertex to the periphery. -/
private theorem round_perimeter {s r u v w : ℕ} (h : u + v + w + 2 ≤ 2*r)
    (hu : s < 5*u + 4) (hv : s ≤ 5*v + 4) (hw : s ≤ 5*w + 4) : 3*s ≤ 10*r := by
  have eu : s / 5 ≤ u := by omega
  have ev : s / 5 ≤ v := by omega
  have ew : s / 5 ≤ w := by omega
  by_cases rem : s % 5 = 4
  · have : s / 5 < u := by omega
    omega
  · omega

/-- A radius-two cover bounds the distance of every vertex to the periphery.
Project a diametral pair and the given vertex onto the five-step relay graph;
its three-point perimeter costs at most twice the number of relays minus two. -/
theorem peripheral_distance_budget {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hc : G.Connected) {R : Finset V}
    (cover : ∀ x, ∃ r ∈ R, G.dist x r ≤ 2) (x : V) :
    3 * distanceToVertices G (peripheralVertices G) x ≤ 10 * R.card := by
  classical
  haveI : Nonempty V := ⟨x⟩
  choose g hg hgdist using cover
  let f (a : V) : R := if h : a ∈ R then ⟨a,h⟩ else ⟨g a,hg a⟩
  have fix (a : R) : f a.val = a := by simp [f,a.property]
  have near (a : V) : G.dist a (f a).val ≤ 2 := by
    by_cases ha : a ∈ R
    · simp [f,ha,dist_self]
    · simpa [f,ha] using hgdist a
  let H : SimpleGraph R := {
    Adj := fun a b => a ≠ b ∧ G.dist a.val b.val ≤ 5
    symm := fun a b h => ⟨h.1.symm, (dist_comm (u := b.val) (v := a.val)) ▸ h.2⟩
    loopless := fun _ h => h.1 rfl }
  have edge {a b : V} (hab : G.Adj a b) : H.Reachable (f a) (f b) := by
    by_cases he : f a = f b
    · rw [he]
    apply Adj.reachable (G := H)
    refine ⟨he, ?_⟩
    have h₁ := hc.dist_triangle (u := (f a).val) (v := a) (w := (f b).val)
    have h₂ := hc.dist_triangle (u := a) (v := b) (w := (f b).val)
    rw [dist_comm (u := (f a).val) (v := a)] at h₁
    rw [dist_eq_one_iff_adj.mpr hab] at h₂
    have := near a; have := near b; omega
  have reach {a b : V} (p : G.Walk a b) : H.Reachable (f a) (f b) := by
    induction p with
    | nil => exact Reachable.rfl
    | cons e _ ih => exact (edge e).trans ih
  haveI : Nonempty R := ⟨f x⟩
  have hH : H.Connected := by
    constructor
    intro a b
    obtain ⟨p⟩ := hc a.val b.val
    simpa only [fix] using reach p
  have along {a b : R} (p : H.Walk a b) : G.dist a.val b.val ≤ 5 * p.length := by
    induction p with
    | nil => simp [dist_self]
    | @cons a b c e _ ih =>
      have h₁ := hc.dist_triangle (u := a.val) (v := b.val) (w := c.val)
      have h₂ : G.dist a.val b.val ≤ 5 := e.2
      simp only [Walk.length_cons]; omega
  have liftDist (a b : V) : G.dist a b ≤ 5 * H.dist (f a) (f b) + 4 := by
    obtain ⟨p,hp⟩ := hH.exists_walk_length_eq_dist (f a) (f b)
    have h := along p
    rw [hp] at h
    have h₁ := hc.dist_triangle (u := a) (v := (f a).val) (w := b)
    have h₂ := hc.dist_triangle (u := (f a).val) (v := (f b).val) (w := b)
    rw [dist_comm (u := (f b).val) (v := b)] at h₂
    have := near a; have := near b; omega
  let s := distanceToVertices G (peripheralVertices G) x
  change 3*s ≤ 10*R.card
  by_cases hs : s = 0
  · simp [hs]
  have far {p : V} (hp : p ∈ peripheralVertices G) : s ≤ G.dist x p :=
    Nat.sInf_le (s := {k | ∃ y ∈ peripheralVertices G, G.dist x y = k}) ⟨p,hp,rfl⟩
  have hn : x ∉ peripheralVertices G := by
    intro hx; have h := far hx; rw [dist_self] at h; omega
  obtain ⟨p,q,hpq⟩ := G.exists_dist_eq_diam
  have hxp := far (peripheral_of_dist_eq_diam hc hpq)
  have hqx := far (peripheral_of_dist_eq_diam hc ((dist_comm (u := q) (v := p)).trans hpq))
  rw [dist_comm (u := x) (v := q)] at hqx
  have strict : G.dist x p < G.diam := lt_of_le_of_ne
    (dist_le_diam (connected_iff_ediam_ne_top.mp hc))
    (fun eq => hn (peripheral_of_dist_eq_diam hc eq))
  have induced : (H.induce ((univ : Finset R) : Set R)).Connected := by
    rw [coe_univ]; exact (H.induceUnivIso.connected_iff).mpr hH
  have per := connected_perimeter hH induced (f p) (mem_univ _) (f q) (mem_univ _)
    (f x) (mem_univ _)
  rw [card_univ, Fintype.card_coe] at per
  apply round_perimeter per
  · have := liftDist p q; omega
  · exact hqx.trans (liftDist q x)
  · exact hxp.trans (liftDist x p)

end Graffiti
