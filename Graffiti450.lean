import Graffiti.Dissociation
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Path

/-! # Written on the Wall II, Graffiti.pc 446 and 450

An unpaid support selected in a dissociation set can be charged to an omitted
leaf, or (in 450) to two omitted vertices of degree two. A leaf can pay for
only one support; a degree-two vertex can supply two half-payments.
Prior proofs of both catalog rows appear in the WoW / West dossier:
https://gist.github.com/siddhantdubey/22f22a7a23db5174ee59e32eaa8724aa
-/

namespace Graffiti.SupportCounting

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def degreeClass (k : ℕ) : Finset V := univ.filter fun v => G.degree v = k

def supportVertices : Finset V := univ.filter fun v => 0 < withinDegree G (degreeClass G 1) v

def privateNeighborhood (X : Finset V) : Finset V := univ.filter fun v => withinDegree G X v = 1

def lowVertices : Finset V := univ \ highVertices G

omit [DecidableEq V] in
@[simp] theorem mem_degreeClass {v : V} {k : ℕ} : v ∈ degreeClass G k ↔ G.degree v = k := by
  simp [degreeClass]

@[simp] theorem mem_lowVertices {v : V} : v ∈ lowVertices G ↔ G.degree v ≤ 2 := by
  simp only [lowVertices, highVertices, mem_sdiff, mem_univ, mem_filter, true_and]
  omega

omit [DecidableEq V] in
@[simp] theorem mem_privateNeighborhood {v : V} {X : Finset V} :
    v ∈ privateNeighborhood G X ↔ withinDegree G X v = 1 := by simp [privateNeighborhood]

omit [DecidableEq V] in
private theorem support_leaf {v : V} (h : v ∈ supportVertices G) :
    ∃ z ∈ degreeClass G 1, G.Adj v z := by
  have hp := (mem_filter.mp h).2
  obtain ⟨z, hz⟩ := card_pos.mp (show 0 < ((degreeClass G 1).filter (G.Adj v)).card from hp)
  exact ⟨z, (mem_filter.mp hz).1, (mem_filter.mp hz).2⟩

omit [DecidableEq V] in
private theorem nbr_subset (X : Finset V) (v : V) : X.filter (G.Adj v) ⊆ G.neighborFinset v :=
  fun w hw => (G.mem_neighborFinset v w).mpr (mem_filter.mp hw).2

omit [DecidableEq V] in
private theorem within_le_degree (X : Finset V) (v : V) : withinDegree G X v ≤ G.degree v :=
  card_le_card (nbr_subset G X v)

omit [DecidableEq V] in
/-- Count incidences from `D` to `W` in both directions. -/
private theorem charge (D W : Finset V) (k : ℕ) (hk : 0 < k)
    (hd : ∀ x ∈ D, k ≤ withinDegree G W x) (hw : ∀ y ∈ W, G.degree y ≤ k) :
    D.card ≤ W.card := by
  refine Nat.le_of_mul_le_mul_right ?_ hk
  apply Finset.card_mul_le_card_mul (s := D) (t := W) G.Adj hd
  intro y hy
  refine le_trans ?_ (hw y hy)
  apply card_le_card (t := G.neighborFinset y)
  intro x hx
  exact (G.mem_neighborFinset y x).mpr (mem_filter.mp hx).2.symm

/-- Unselected unpaid supports pay for themselves. The hypothesis deals only
with selected unpaid supports, using omitted vertices outside that set. -/
private theorem finish (s S P : Finset V)
    (h : ((S \ P) ∩ s).card ≤ ((univ \ s) \ (S \ P)).card) :
    s.card ≤ (univ \ S).card + P.card := by
  let H := S \ P
  have hpart := card_sdiff_add_card_inter H s
  have hmiss := card_sdiff_add_card_inter (univ \ s) H
  have hself : (H \ s).card ≤ ((univ \ s) ∩ H).card := by
    apply card_le_card
    intro x hx
    exact mem_inter.mpr ⟨mem_sdiff.mpr ⟨mem_univ _, (mem_sdiff.mp hx).2⟩, (mem_sdiff.mp hx).1⟩
  have hp : S.card ≤ H.card + P.card := card_le_card_sdiff_add_card
  have hs := card_sdiff_add_card_eq_card (subset_univ s)
  have hS := card_sdiff_add_card_eq_card (subset_univ S)
  change (H ∩ s).card ≤ ((univ \ s) \ H).card at h
  omega

/-- UHD Graffiti.pc 446: minimum-degree private neighbors pay for the supports
with just one leaf. All remaining selected supports have an omitted leaf. -/
theorem graffiti446 (hG : G.Connected) (hn : 3 < Fintype.card V) :
    dissociationNumber G ≤ (univ \ supportVertices G).card +
      (privateNeighborhood G (degreeClass G G.minDegree)).card := by
  letI : Nonempty V := hG.nonempty
  have hmin : 1 ≤ G.minDegree := by
    apply G.le_minDegree_of_forall_le_degree
    intro x
    have hcard : 1 < (univ : Finset V).card := by simpa only [card_univ] using (show 1 < Fintype.card V by omega)
    obtain ⟨y, _, hy⟩ := exists_ne_of_one_lt_card hcard x
    obtain ⟨p⟩ := hG.preconnected x y
    exact (G.degree_pos_iff_exists_adj x).mpr ⟨_, p.adj_snd (Walk.not_nil_of_ne hy.symm)⟩
  let P := privateNeighborhood G (degreeClass G G.minDegree)
  let H := supportVertices G \ P
  have many (x : V) (hx : x ∈ H) : 2 ≤ withinDegree G (degreeClass G 1) x := by
    obtain ⟨hs, hnP⟩ := mem_sdiff.mp hx
    obtain ⟨z, hz, _⟩ := support_leaf G hs
    have hle := G.minDegree_le_degree z
    have hz' := (mem_degreeClass G).mp hz
    have he : G.minDegree = 1 := by omega
    have hne : withinDegree G (degreeClass G G.minDegree) x ≠ 1 :=
      fun h => hnP ((mem_privateNeighborhood G).mpr h)
    rw [he] at hne
    have hp : 0 < withinDegree G (degreeClass G 1) x := (mem_filter.mp hs).2
    omega
  apply dissociationNumber_le
  intro s hdis
  apply finish
  let M := (univ \ s) \ H
  let W := M ∩ degreeClass G 1
  apply le_trans (charge G (H ∩ s) W 1 (by decide) ?_ ?_) (card_le_card inter_subset_left)
  · intro x hx
    obtain ⟨hh, hxs⟩ := mem_inter.mp hx
    have hm := many x hh
    have hd := hdis x hxs
    obtain ⟨y, hy, hnot⟩ := exists_mem_not_mem_of_card_lt_card
      (s := s.filter (G.Adj x)) (t := (degreeClass G 1).filter (G.Adj x))
      (show withinDegree G s x < withinDegree G (degreeClass G 1) x by omega)
    obtain ⟨hl, ha⟩ := mem_filter.mp hy
    have hys : y ∉ s := fun h => hnot (mem_filter.mpr ⟨h, ha⟩)
    have hyH : y ∉ H := by
      intro h
      have := (many y h).trans (within_le_degree G _ y)
      have := (mem_degreeClass G).mp hl
      omega
    exact card_pos.mpr ⟨y, mem_filter.mpr ⟨mem_inter.mpr
      ⟨mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨mem_univ _, hys⟩, hyH⟩, hl⟩, ha⟩⟩
  · intro y hy
    exact ((mem_degreeClass G).mp (mem_inter.mp hy).2).le

/-- UHD Graffiti.pc 450. The counting bound itself needs no connectivity or
order restriction: a vertex adjacent to a support already has positive degree. -/
theorem graffiti450 :
    dissociationNumber G ≤ (univ \ supportVertices G).card +
      (privateNeighborhood G (degreeClass G 2)).card + (privateNeighborhood G (lowVertices G)).card := by
  let P₂ := privateNeighborhood G (degreeClass G 2)
  let Pₗ := privateNeighborhood G (lowVertices G)
  let H := supportVertices G \ (P₂ ∪ Pₗ)
  have many (x : V) (hx : x ∈ H) : 2 ≤ withinDegree G (lowVertices G) x := by
    obtain ⟨hs, hnot⟩ := mem_sdiff.mp hx
    obtain ⟨z, hz, ha⟩ := support_leaf G hs
    have hz' := (mem_degreeClass G).mp hz
    have hp : 0 < withinDegree G (lowVertices G) x := card_pos.mpr
      ⟨z, mem_filter.mpr ⟨(mem_lowVertices G).mpr (by omega), ha⟩⟩
    have hne : withinDegree G (lowVertices G) x ≠ 1 :=
      fun h => hnot (mem_union_right P₂ ((mem_privateNeighborhood G).mpr h))
    omega
  have hardDegree (x : V) (hx : x ∈ H) : 2 ≤ G.degree x :=
    (many x hx).trans (within_le_degree G _ x)
  apply dissociationNumber_le
  intro s hdis
  have bound : s.card ≤ (univ \ supportVertices G).card + (P₂ ∪ Pₗ).card := by
    apply finish
    let D := H ∩ s
    let M := (univ \ s) \ H
    let W₁ := M ∩ degreeClass G 1
    let W₂ := M ∩ degreeClass G 2
    let T := D.filter fun x => 0 < withinDegree G W₁ x
    have ht : T.card ≤ W₁.card := charge G T W₁ 1 (by decide)
      (fun _ hx => (mem_filter.mp hx).2)
      (fun _ hy => ((mem_degreeClass G).mp (mem_inter.mp hy).2).le)
    have hu : (D \ T).card ≤ W₂.card := by
      refine charge G (D \ T) W₂ 2 (by decide) ?_ (fun _ hy => ((mem_degreeClass G).mp (mem_inter.mp hy).2).le)
      intro x hx
      obtain ⟨hxD, hxT⟩ := mem_sdiff.mp hx
      obtain ⟨hxH, hxs⟩ := mem_inter.mp hxD
      have hd := hdis x hxs
      have keepLeaf (y : V) (h1 : y ∈ degreeClass G 1) (ha : G.Adj x y) : y ∈ s := by
        by_contra hys
        have hyH : y ∉ H := by
          intro h
          have := hardDegree y h
          have := (mem_degreeClass G).mp h1
          omega
        have hw : y ∈ W₁ := mem_inter.mpr
          ⟨mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨mem_univ _, hys⟩, hyH⟩, h1⟩
        exact hxT (mem_filter.mpr ⟨hxD, card_pos.mpr ⟨y, mem_filter.mpr ⟨hw, ha⟩⟩⟩)
      have twoPos : 0 < withinDegree G (degreeClass G 2) x := by
        by_contra hzero
        have hsub : (lowVertices G).filter (G.Adj x) ⊆ s.filter (G.Adj x) := by
          intro y hy
          obtain ⟨hl, ha⟩ := mem_filter.mp hy
          have hle := (mem_lowVertices G).mp hl
          have hp := (G.degree_pos_iff_exists_adj y).mpr ⟨x, ha.symm⟩
          have hne : G.degree y ≠ 2 := fun h => hzero (card_pos.mpr
            ⟨y, mem_filter.mpr ⟨(mem_degreeClass G).mpr h, ha⟩⟩)
          exact mem_filter.mpr ⟨keepLeaf y ((mem_degreeClass G).mpr (by omega)) ha, ha⟩
        have hc : withinDegree G (lowVertices G) x ≤ withinDegree G s x := card_le_card hsub
        have := many x hxH
        omega
      have hne : withinDegree G (degreeClass G 2) x ≠ 1 := fun h =>
        (mem_sdiff.mp hxH).2 (mem_union_left Pₗ ((mem_privateNeighborhood G).mpr h))
      have htwo : 2 ≤ withinDegree G (degreeClass G 2) x := by omega
      obtain ⟨z, hz, haz⟩ := support_leaf G (mem_sdiff.mp hxH).1
      have hdegz := (mem_degreeClass G).mp hz
      have hzs := keepLeaf z hz haz
      let N₂ := (degreeClass G 2).filter (G.Adj x)
      have hzN : z ∉ N₂ := fun h => by
        have := (mem_degreeClass G).mp (mem_filter.mp h).1
        omega
      have hhigh : 2 < G.degree x := by
        have hsub : insert z N₂ ⊆ G.neighborFinset x := by
          intro a ha
          rcases mem_insert.mp ha with rfl | hm
          · exact (G.mem_neighborFinset _ _).mpr haz
          · exact nbr_subset G _ _ hm
        have hc := card_le_card hsub
        rw [card_insert_of_not_mem hzN, card_neighborFinset_eq_degree] at hc
        change 2 ≤ N₂.card at htwo
        omega
      apply htwo.trans
      apply card_le_card
      intro y hy
      obtain ⟨hy2, hxy⟩ := mem_filter.mp hy
      have hdegy := (mem_degreeClass G).mp hy2
      have hys : y ∉ s := by
        intro h
        have he := card_le_one_iff.mp hd (mem_filter.mpr ⟨h, hxy⟩) (mem_filter.mpr ⟨hzs, haz⟩)
        exact (show G.degree y ≠ G.degree z by omega) (congrArg (fun v => G.degree v) he)
      have hyH : y ∉ H := by
        intro hyhard
        have hall : (lowVertices G).filter (G.Adj y) = G.neighborFinset y := by
          apply eq_of_subset_of_card_le (nbr_subset G _ _)
          change G.degree y ≤ withinDegree G (lowVertices G) y
          have := many y hyhard
          omega
        have hxall : x ∈ (lowVertices G).filter (G.Adj y) := hall.symm ▸ (G.mem_neighborFinset _ _).mpr hxy.symm
        exact (Nat.not_le_of_lt hhigh) ((mem_lowVertices G).mp (mem_filter.mp hxall).1)
      exact mem_filter.mpr ⟨mem_inter.mpr
        ⟨mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨mem_univ _, hys⟩, hyH⟩, hy2⟩, hxy⟩
    have hdisj : Disjoint W₁ W₂ := by
      apply Finset.disjoint_left.mpr
      intro y h1 h2
      have := (mem_degreeClass G).mp (mem_inter.mp h1).2
      have := (mem_degreeClass G).mp (mem_inter.mp h2).2
      omega
    have hw : (W₁ ∪ W₂).card ≤ M.card := card_le_card (union_subset inter_subset_left inter_subset_left)
    rw [card_union_of_disjoint hdisj] at hw
    have htD : T ⊆ D := filter_subset _ _
    have hp := card_sdiff_add_card_eq_card htD
    change D.card ≤ M.card
    omega
  have hp := card_union_le P₂ Pₗ
  change s.card ≤ (univ \ supportVertices G).card + P₂.card + Pₗ.card
  omega

end Graffiti.SupportCounting
