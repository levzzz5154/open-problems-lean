import Graffiti258
import Graffiti434d
import Mathlib.Combinatorics.SimpleGraph.ConcreteColorings

/-! # Written on the Wall II, Graffiti.pc 235

The periphery includes **all** vertices of maximum eccentricity. Its set
 eccentricity is the maximum distance to the nearest peripheral vertex, zero
 when the whole graph is peripheral (definitions 52 and 55). The bipartite
 indicator and total domination number are definitions 84 and 94.[24][25]
 A connected singleton has no total dominating set, so we assume order ≥ 2.

The three pairwise distances between any three vertices sum to at most four
 times the total domination number. For the bipartite correction, the only
 exceptional integer pairs are ruled out by parity and disjoint radius-two
 balls, respectively.

Sources:
* [24] https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json
* [25] https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/definitions.json
-/

namespace Graffiti

open SimpleGraph Finset
open scoped Classical

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Maximum of the minimum distances to the periphery. Including peripheral
vertices in the maximum adds only zeros. -/
noncomputable def peripheryDepth (G : SimpleGraph V) : ℕ :=
  univ.sup fun v => sInf {k : ℕ | ∃ p ∈ peripheralVertices G, G.dist v p = k}

theorem farthest_from_periphery (hc : G.Connected) :
    ∃ v, ∀ p ∈ peripheralVertices G, peripheryDepth G ≤ G.dist v p := by
  classical
  haveI : Nonempty V := hc.nonempty
  obtain ⟨v,_,hv⟩ := univ.exists_mem_eq_sup univ_nonempty
    (fun v => sInf {k : ℕ | ∃ p ∈ peripheralVertices G, G.dist v p = k})
  refine ⟨v,fun p hp => ?_⟩
  rw [show peripheryDepth G = _ from hv]
  exact Nat.sInf_le (s := {k : ℕ | ∃ p ∈ peripheralVertices G, G.dist v p = k}) ⟨p, hp, rfl⟩

theorem peripheral_of_dist_eq_diam (hc : G.Connected) {x y : V} (h : G.dist x y = G.diam) :
    x ∈ peripheralVertices G := by
  classical
  haveI : Nonempty V := hc.nonempty
  have eq : G.edist x y = G.ediam := by
    rw [← ENat.coe_toNat (edist_ne_top_iff_reachable.mpr (hc x y)),
      ← ENat.coe_toNat (connected_iff_ediam_ne_top.mp hc)]
    exact congrArg Nat.cast h
  exact mem_filter.mpr ⟨mem_univ _, le_antisymm eccent_le_ediam (eq ▸ edist_le_eccent)⟩

omit [Fintype V] in
/-- Adding one adjacent vertex increases the maximum three-point perimeter by
at most two: only the two sides crossing between old and new can lengthen. -/
theorem connected_perimeter (hc : G.Connected) {C : Finset V}
    (hC : (G.induce (C : Set V)).Connected) :
    ∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C,
      G.dist a b + G.dist b c + G.dist c a + 2 ≤ 2 * C.card := by
  classical
  let P (S : Finset V) := ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S,
    G.dist a b + G.dist b c + G.dist c a + 2 ≤ 2 * S.card
  let rec grow (S : Finset V) (hs : S ⊆ C) (hne : S.Nonempty) (hp : P S) : P C := by
    by_cases he : C ⊆ S
    · exact (Subset.antisymm hs he) ▸ hp
    obtain ⟨a, ha⟩ := hne
    obtain ⟨b, hb, hbs⟩ := not_subset.mp he
    obtain ⟨p⟩ := hC (⟨a, hs ha⟩ : (C : Set V)) ⟨b, hb⟩
    obtain ⟨d, _, hy, hx⟩ := p.exists_boundary_dart {u | u.val ∈ S} ha hbs
    let x := d.snd.val
    let y := d.fst.val
    have hx' : x ∉ S := hx
    have hy' : y ∈ S := hy
    have hed : G.Adj y x := d.adj
    let f (u : V) := if u = x then y else u
    have hf {u} (hu : u ∈ insert x S) : f u ∈ S := by
      rcases mem_insert.mp hu with rfl | h
      · simpa [f] using hy'
      · simpa [f, show u ≠ x from fun e => hx' (e ▸ h)] using h
    let extra (u v : V) : ℕ := if (u = x ↔ v = x) then 0 else 1
    have liftDist (u v : V) : G.dist u v ≤ G.dist (f u) (f v) + extra u v := by
      by_cases hu : u = x <;> by_cases hv : v = x <;> simp [f, extra, hu, hv, dist_self]
      · have h := hc.dist_triangle (u := x) (v := y) (w := v)
        rw [dist_eq_one_iff_adj.mpr hed.symm] at h
        omega
      · have h := hc.dist_triangle (u := u) (v := y) (w := x)
        rwa [dist_eq_one_iff_adj.mpr hed] at h
    apply grow (insert x S) (insert_subset d.snd.property hs) (insert_nonempty ..)
    intro u hu v hv w hw
    have h := hp _ (hf hu) _ (hf hv) _ (hf hw)
    have h1 := liftDist u v
    have h2 := liftDist v w
    have h3 := liftDist w u
    have ex : extra u v + extra v w + extra w u ≤ 2 := by
      by_cases h : u = x <;> by_cases k : v = x <;> by_cases l : w = x <;> simp [extra, h, k, l]
    rw [card_insert_of_not_mem hx']
    omega
  termination_by C.card - S.card
  decreasing_by
    have lt' : S.card < C.card := card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨hs, fun h => he (h ▸ Subset.rfl)⟩)
    rw [card_insert_of_not_mem hx']
    omega
  obtain ⟨⟨v, hv⟩⟩ := hC.nonempty
  apply grow {v} (singleton_subset_iff.mpr hv) (singleton_nonempty v)
  simp [P, dist_self]

omit [Fintype V] in
/-- Three-point and two-point metric budgets for any total dominating set. -/
theorem total_domination_distance_budget (hc : G.Connected) {D : Finset V}
    (hD : TotallyDominates G D) :
    (∀ a b c, G.dist a b + G.dist b c + G.dist c a ≤ 4 * D.card) ∧
    (∀ a b, G.dist a b + 1 ≤ 2 * D.card) := by
  obtain ⟨C, hDC, hC, hcost⟩ := exists_connected_total_superset hc hD
  choose f hf he using hD
  have liftDist (u v : V) : G.dist u v ≤ G.dist (f u) (f v) + 2 := by
    have h := hc.dist_triangle (u := u) (v := f u) (w := v)
    have k := hc.dist_triangle (u := f u) (v := f v) (w := v)
    rw [dist_eq_one_iff_adj.mpr (he u)] at h
    rw [dist_eq_one_iff_adj.mpr (he v).symm] at k
    omega
  have per (a b c : V) := connected_perimeter hc hC _ (hDC (hf a)) _ (hDC (hf b)) _ (hDC (hf c))
  constructor
  · intro a b c
    have := per a b c
    have := liftDist a b
    have := liftDist b c
    have := liftDist c a
    omega
  · intro a b
    have h := per a b a
    rw [dist_self, dist_comm (u := f b) (v := f a)] at h
    have := liftDist a b
    omega

omit [Fintype V] in
/-- Three mutually five-separated vertices require six total dominators:
each radius-two ball contains a dominator and one of its own neighbors in `D`. -/
private theorem six_le_of_separated (hc : G.Connected) {D : Finset V} (hD : TotallyDominates G D)
    {a b c : V} (hab : 5 ≤ G.dist a b) (hbc : 5 ≤ G.dist b c) (hac : 5 ≤ G.dist a c) :
    6 ≤ D.card := by
  classical
  let ball (x : V) := D.filter fun y => G.dist x y ≤ 2
  have two (x : V) : 2 ≤ (ball x).card := by
    obtain ⟨y, hy, hxy⟩ := hD x
    obtain ⟨z, hz, hyz⟩ := hD y
    have h := hc.dist_triangle (u := x) (v := y) (w := z)
    rw [dist_eq_one_iff_adj.mpr hxy, dist_eq_one_iff_adj.mpr hyz] at h
    exact one_lt_card.mpr ⟨y, mem_filter.mpr ⟨hy, by simp [dist_eq_one_iff_adj.mpr hxy]⟩,
      z, mem_filter.mpr ⟨hz, h⟩, hyz.ne⟩
  have sep {x y : V} (hxy : 5 ≤ G.dist x y) : Disjoint (ball x) (ball y) := by
    apply disjoint_left.mpr
    intro z hx hy
    have h := hc.dist_triangle (u := x) (v := z) (w := y)
    rw [dist_comm (u := z) (v := y)] at h
    have hz : G.dist x z ≤ 2 := (mem_filter.mp hx).2
    have hz' : G.dist y z ≤ 2 := (mem_filter.mp hy).2
    omega
  have sub (x : V) : ball x ⊆ D := filter_subset ..
  have h := card_le_card (union_subset (union_subset (sub a) (sub b)) (sub c))
  rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨sep hac, sep hbc⟩),
    card_union_of_disjoint (sep hab)] at h
  have := two a
  have := two b
  have := two c
  omega

/-- Catalog inequality, scaled by three to avoid division. -/
theorem graffiti235 [Nontrivial V] (hc : G.Connected) :
    2 * peripheryDepth G + (if G.Colorable 2 then 3 else 0) ≤ 3 * totalDominationNumber G := by
  classical
  obtain ⟨D, hD, hmin⟩ := exists_min_total_set hc
  have htwo := two_le_totalDominationNumber hc
  rw [← hmin] at htwo ⊢
  let r := peripheryDepth G
  change 2 * r + _ ≤ _
  by_cases h0 : r = 0
  · split <;> omega
  obtain ⟨v,far⟩ := farthest_from_periphery hc
  have hn : v ∉ peripheralVertices G := by
    intro h
    have := far v h
    rw [dist_self] at this
    omega
  have hfin := connected_iff_ediam_ne_top.mp hc
  have strict (x : V) : G.dist v x < G.diam :=
    lt_of_le_of_ne (dist_le_diam hfin) (fun e => hn (peripheral_of_dist_eq_diam hc e))
  obtain ⟨a, b, hab⟩ := G.exists_dist_eq_diam
  have ha : r ≤ G.dist v a := far a (peripheral_of_dist_eq_diam hc hab)
  have hb : r ≤ G.dist v b := far b (peripheral_of_dist_eq_diam hc ((dist_comm (u := b) (v := a)).trans hab))
  obtain ⟨per, pair⟩ := total_domination_distance_budget hc hD
  have bound := per v a b
  rw [dist_comm (u := b) (v := v)] at bound
  have dab := pair a b
  have sva := strict a
  have svb := strict b
  split
  · rename_i bip
    apply of_not_not
    intro bad
    have cases : (r = 2 ∧ D.card = 2) ∨ (r = 5 ∧ D.card = 4) := by
      have small : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 := by omega
      rcases small with h | h | h | h | h <;> omega
    rcases cases with ⟨hr, hd⟩ | ⟨hr, hd⟩
    · let col : G.Coloring Bool := recolorOfEquiv G finTwoEquiv bip.some
      have parity (x y : V) : Even (G.dist x y) ↔ (col x ↔ col y) := by
        obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist x y
        exact hp ▸ col.even_length_iff_congr p
      have ea := (parity v a).mp (by rw [show G.dist v a = 2 by omega]; decide)
      have eb := (parity v b).mp (by rw [show G.dist v b = 2 by omega]; decide)
      have e := (parity a b).mpr (ea.symm.trans eb)
      rw [show G.dist a b = 3 by omega] at e
      exact (by decide : ¬ Even (3 : ℕ)) e
    · have := six_le_of_separated hc hD (a := v) (b := a) (c := b) (by omega) (by omega) (by omega)
      omega
  · omega

end Graffiti

#print axioms Graffiti.graffiti235
