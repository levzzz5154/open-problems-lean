import Graffiti.TripleRadius
import Graffiti.TreeCenters
import Graffiti169
import Mathlib.Tactic.Ring

/-! # Written on the Wall II, conjecture 356

Catalog definition 109 averages the positive distances to the *set* of leaves.
We prove the inequality with its denominator cleared. The main estimate uses
vertex-disjoint chains directed away from the center. A chain of `j` nonleaves
can contribute at most `j(j+1)/2` to the distance sum.

https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json
https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/definitions.json
-/

namespace Graffiti

open Finset SimpleGraph

variable {V : Type*} [Fintype V] {G T : SimpleGraph V}

/-- Radius is a lower bound for the size of any total dominating set. -/
theorem radius_le_total_set (hc : G.Connected) {D : Finset V} (hd : TotallyDominates G D) :
    G.radius.toNat ≤ D.card := by
  classical
  obtain ⟨C,hs,hC,cost⟩ := exists_connected_total_superset hc hd
  obtain ⟨U,hU,ht⟩ := hC.exists_isTree_le
  obtain ⟨c,cover⟩ := tree_half_order_center ht
  obtain ⟨w,hw⟩ := G.exists_edist_eq_eccent_of_finite c.val
  obtain ⟨v,hv,hvw⟩ := hd w
  let u : (C : Set V) := ⟨v,hs hv⟩
  have half := cover u
  rw [← Nat.card_eq_fintype_card,Set.Nat.card_coe_set_eq,Set.ncard_coe_Finset] at half
  obtain ⟨p,hp⟩ := ht.isConnected.exists_walk_length_eq_dist c u
  let f : U →g G := { toFun := Subtype.val, map_rel' := fun h => hU h }
  have hdist : G.dist c.val v ≤ U.dist c u := by simpa only [Walk.length_map,hp] using dist_le (p.map f)
  have tri := hc.dist_triangle (u := c.val) (v := v) (w := w)
  rw [dist_eq_one_iff_adj.mpr hvw.symm] at tri
  have bound : G.radius.toNat ≤ G.dist c.val w := ENat.toNat_le_toNat
    ((G.radius_le_eccent (u := c.val)).trans_eq hw.symm) (edist_ne_top_iff_reachable.mpr (hc c.val w))
  omega

/-- Minimum distance to a degree-one vertex (not distance to a chosen leaf). -/
noncomputable def leafDistance (T : SimpleGraph V) [DecidableRel T.Adj] (v : V) : ℕ :=
  sInf {k | ∃ l ∈ pendantVertices T, T.dist v l = k}

omit [Fintype V] in
private theorem level_increases (ht : T.IsTree) (a b : V) {v x y : V}
    (hx : T.Adj v x) (hy : T.Adj v y) (hne : x ≠ y) :
    let h z := max (T.dist z a) (T.dist z b)
    h v < h x ∨ h v < h y := by
  let p : T.Walk x y := .cons hx.symm (.cons hy .nil)
  have hp : p.IsPath := by simp [p, Walk.isPath_def, hx.ne.symm,hne,hy.ne]
  have step (r : V) := tree_interior_dist_lt ht hp (show v ∈ p.support by simp [p]) hx.ne hy.ne r
  dsimp only
  rcases le_total (T.dist v a) (T.dist v b) with h | h
  · rw [max_eq_right h]
    exact (step b).imp (fun q => q.trans_le (le_max_right ..)) (fun q => q.trans_le (le_max_right ..))
  · rw [max_eq_left h]
    exact (step a).imp (fun q => q.trans_le (le_max_left ..)) (fun q => q.trans_le (le_max_left ..))

private noncomputable def chainLength [DecidableEq V] (S : Finset V) (f : V → V)
    (h : V → ℕ) (R : ℕ) (up : ∀ v ∈ S, h v < h (f v)) (cap : ∀ v, h v ≤ R)
    (v : V) : ℕ :=
  if hv : v ∈ S then chainLength S f h R up cap (f v) + 1 else 0
termination_by R - h v
decreasing_by have := up v hv; have := cap (f v); omega

private theorem charge_identity {n H : ℕ} (hn : n+1 ≤ H) :
    2*(n+1) + (n+1)*(H-(n+1)) = H+1 + n*(H-n) := by
  obtain ⟨w,rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show n+1+w-(n+1) = w by omega, show n+1+w-n = w+1 by omega]
  ring

variable [DecidableEq V] [DecidableRel T.Adj]

/-- Choose an outward neighbor at each nonleaf. The strict two-neighbor
inequality forces each vertex to be chosen at most once, so the chains do
not merge. The potential `j(H-j)` sums their triangular costs without
explicitly indexing the chains. -/
private theorem leaf_chain_budget [Nontrivial V] (ht : T.IsTree) (a b : V) (lo R : ℕ)
    (lower : ∀ v, lo ≤ max (T.dist v a) (T.dist v b))
    (upper : ∀ v, max (T.dist v a) (T.dist v b) ≤ R) :
    let S := (pendantVertices T)ᶜ
    (∑ v ∈ S, leafDistance T v) ≤ R*S.card ∧
      2*(∑ v ∈ S, leafDistance T v) ≤ (R-lo+1)*S.card := by
  classical
  let S := (pendantVertices T)ᶜ
  let h v := max (T.dist v a) (T.dist v b)
  have outward (v : V) (hv : v ∈ S) : ∃ w, T.Adj v w ∧ h v < h w := by
    have hd : T.degree v ≠ 1 := fun e =>
      (mem_compl.mp hv) (mem_filter.mpr ⟨mem_univ _,e⟩)
    have pos := degree_pos_of_connected ht.isConnected v
    have big : 1 < (T.neighborFinset v).card := by rw [card_neighborFinset_eq_degree]; omega
    obtain ⟨x,hx,y,hy,ne⟩ := one_lt_card.mp big
    obtain hx := (T.mem_neighborFinset v x).mp hx
    obtain hy := (T.mem_neighborFinset v y).mp hy
    exact (level_increases ht a b hx hy ne).elim (fun e => ⟨_,hx,e⟩) (fun e => ⟨_,hy,e⟩)
  let f (v : V) := if hv : v ∈ S then (outward v hv).choose else v
  have step (v : V) (hv : v ∈ S) : T.Adj v (f v) ∧ h v < h (f v) := by
    simpa only [f,dif_pos hv] using (outward v hv).choose_spec
  have up (v : V) (hv : v ∈ S) := (step v hv).2
  have inj : ∀ x ∈ S, ∀ y ∈ S, f x = f y → x = y := by
    intro x hx y hy eq
    apply Classical.byContradiction
    intro ne
    have e : T.Adj (f x) y := eq ▸ (step y hy).1.symm
    have u : h y < h (f x) := eq ▸ up y hy
    exact (level_increases ht a b (step x hx).1.symm e ne).elim
      (not_lt_of_ge (up x hx).le) (not_lt_of_ge u.le)
  let j := chainLength S f h R up upper
  have next (v : V) (hv : v ∈ S) : j v = j (f v)+1 := by
    change chainLength .. = _
    rw [chainLength]; exact dif_pos hv
  have stop (v : V) (hv : v ∉ S) : j v = 0 := by
    change chainLength .. = _
    rw [chainLength]; exact dif_neg hv
  let rec reaches (v : V) : (∃ l ∈ pendantVertices T, T.dist v l ≤ j v) ∧ h v + j v ≤ R := by
    by_cases hv : v ∈ S
    · obtain ⟨⟨l,hl,hd⟩,cap⟩ := reaches (f v)
      have tri := ht.isConnected.dist_triangle (u := v) (v := f v) (w := l)
      rw [dist_eq_one_iff_adj.mpr (step v hv).1] at tri
      rw [next v hv]
      have := up v hv
      exact ⟨⟨l,hl,by omega⟩,by omega⟩
    · rw [stop v hv]
      exact ⟨⟨v,by simpa [S] using hv,by simp [dist_self]⟩,by simpa only [Nat.add_zero] using upper v⟩
  termination_by R - max (T.dist v a) (T.dist v b)
  decreasing_by exact Nat.sub_lt_sub_left ((up v hv).trans_le (upper (f v))) (up v hv)
  have near (v : V) : leafDistance T v ≤ j v := by
    obtain ⟨l,hl,hd⟩ := (reaches v).1
    exact (Nat.sInf_le (s := {k | ∃ l ∈ pendantVertices T, T.dist v l = k}) ⟨l,hl,rfl⟩).trans hd
  let H := R-lo
  have bounded (v : V) : j v ≤ H := by
    have := (reaches v).2
    have hh : lo ≤ h v := lower v
    dsimp [H]; omega
  let W (v : V) := j v*(H-j v)
  have telescopes : ∑ v ∈ S, W (f v) ≤ ∑ v ∈ S, W v := by
    calc ∑ v ∈ S, W (f v) = ∑ w ∈ S.image f, W w := (sum_image inj).symm
         _ ≤ ∑ w ∈ S, W w := sum_le_sum_of_ne_zero fun x _ hx => by
           apply Classical.byContradiction
           intro out
           exact hx (by simp [W,stop x out])
  have point (v : V) (hv : v ∈ S) : 2*j v + W v = H+1 + W (f v) := by
    have hb := bounded v
    simp only [W,next v hv] at hb ⊢
    exact charge_identity hb
  have sumcost := sum_congr rfl point
  simp only [sum_add_distrib,← mul_sum,sum_const,smul_eq_mul] at sumcost
  have le := Finset.sum_le_sum (s := S) (fun v _ => near v)
  constructor
  · calc ∑ v ∈ S, leafDistance T v ≤ ∑ _v ∈ S, R := sum_le_sum fun v _ =>
           (near v).trans ((bounded v).trans (Nat.sub_le ..))
         _ = R*S.card := by simp [Nat.mul_comm]
  · change 2*(∑ v ∈ S, leafDistance T v) ≤ (H+1)*S.card
    rw [Nat.mul_comm (H+1),Nat.mul_add,Nat.mul_one]
    simp only [Nat.mul_add,Nat.mul_one] at sumcost
    omega

omit [DecidableEq V] in
/-- Positive distances are exactly those at nonleaves. In particular the
domain in the sum is exactly the one in catalog definition 109. -/
theorem leafDistance_pos_iff [Nontrivial V] (ht : T.IsTree) (v : V) :
    0 < leafDistance T v ↔ v ∉ pendantVertices T := by
  classical
  have leaves : (pendantVertices T).Nonempty := by
    by_contra empty
    have large (x : V) : 2 ≤ T.degree x := by
      have ne : T.degree x ≠ 1 := fun e => empty ⟨x,mem_filter.mpr ⟨mem_univ _,e⟩⟩
      have := degree_pos_of_connected ht.isConnected x
      omega
    have h := Finset.sum_le_sum (s := (univ : Finset V)) (fun x _ => large x)
    rw [T.sum_degrees_eq_twice_card_edges] at h
    simp only [sum_const,card_univ,smul_eq_mul] at h
    have := ht.card_edgeFinset
    omega
  constructor
  · intro hp hv
    have h : leafDistance T v ≤ 0 := Nat.sInf_le ⟨v,hv,dist_self⟩
    omega
  · intro hv
    obtain ⟨l,hl⟩ := leaves
    have hnon : {k | ∃ l ∈ pendantVertices T, T.dist v l = k}.Nonempty := ⟨_,l,hl,rfl⟩
    obtain ⟨x,hx,eq⟩ := Nat.sInf_mem hnon
    change T.dist v x = leafDistance T v at eq
    rw [← eq]
    exact ht.isConnected.pos_dist_of_ne (fun e => hv (e ▸ hx))

/-- For the catalog's domain the number of terms in the mean is positive. -/
theorem nonleaf_count_pos (ht : T.IsTree) (hn : 2 < Fintype.card V) :
    0 < (pendantVertices T)ᶜ.card := by
  have h := (leaves_le_maxLeafCount (G := T) le_rfl ht).trans_lt (maxLeafCount_lt_order hn)
  have := card_add_card_compl (pendantVertices T)
  omega

/-- The geometric strengthening: radius itself bounds center size times
mean positive distance to the leaves. -/
theorem center_leafDistance_sum_le_radius [Nontrivial V] (ht : T.IsTree) :
    T.center.ncard * (∑ v ∈ (pendantVertices T)ᶜ, leafDistance T v) ≤
      T.radius.toNat * (pendantVertices T)ᶜ.card := by
  classical
  have bound (x : V) (hx : x ∈ T.center) (v : V) : T.dist v x ≤ T.radius.toNat := by
    rw [dist_comm]
    exact ENat.toNat_le_toNat ((edist_le_eccent (G := T) (u := x) (v := v)).trans_eq hx)
      (radius_ne_top_iff.mpr ht.isConnected)
  obtain ⟨a,ha⟩ := T.center_nonempty
  by_cases small : T.center.ncard ≤ 1
  · have card := Nat.mul_le_mul_right (∑ v ∈ (pendantVertices T)ᶜ, leafDistance T v) small
    rw [Nat.one_mul] at card
    exact card.trans (leaf_chain_budget ht a a 0 _ (fun _ => Nat.zero_le _)
      (fun v => max_le (bound a ha v) (bound a ha v))).1
  · obtain ⟨b,hb,hba⟩ := Set.exists_ne_of_one_lt_ncard (s := T.center) (by omega) a
    have lower (v : V) : 1 ≤ max (T.dist v a) (T.dist v b) := by
      by_cases e : v = a
      · subst v; exact (ht.isConnected.pos_dist_of_ne hba.symm).trans_le (le_max_right ..)
      · exact (ht.isConnected.pos_dist_of_ne e).trans_le (le_max_left ..)
    have hc := tree_center_ncard_le_two ht
    rw [show T.center.ncard = 2 by omega]
    have pos := (lower a).trans (max_le (bound a ha a) (bound b hb a))
    have h := (leaf_chain_budget ht a b 1 _ lower (fun v => max_le (bound a ha v) (bound b hb v))).2
    rwa [show T.radius.toNat-1+1 = T.radius.toNat by omega] at h

/-- WOWII 356, for every finite tree of order greater than two.
The denominator is the number of nonleaves, not the number of leaf pairs. -/
theorem graffiti356 (ht : T.IsTree) (hn : 2 < Fintype.card V) :
    T.center.ncard * (∑ v ∈ (pendantVertices T)ᶜ, leafDistance T v) ≤
      totalDominationNumber T * (pendantVertices T)ᶜ.card := by
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨D,hd,hmin⟩ := exists_min_total_set ht.isConnected
  exact (center_leafDistance_sum_le_radius ht).trans
    (Nat.mul_le_mul_right _ ((radius_le_total_set ht.isConnected hd).trans_eq hmin))

end Graffiti
