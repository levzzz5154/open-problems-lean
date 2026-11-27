import Graffiti.DomConnectCost
import Graffiti.LeafBounds
import Graffiti.ParityLeaves
import Mathlib.Data.Nat.Lattice
import Mathlib.Tactic.Linarith

/-! # Written on the Wall II, Graffiti.pc 258

`L` is the maximum leaf count over spanning trees (catalog definition 1).
The root counts as being at even distance from itself. Total domination is
only defined, in the catalog's minimum-set sense, if the graph has no isolate.
For connected graphs this excludes only the singleton.
https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json
-/

namespace Graffiti

open Finset SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable def totalDominationNumber (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ D : Finset V, TotallyDominates G D ∧ D.card = k}

noncomputable def maxEvenLayerCount (G : SimpleGraph V) : ℕ := by
  classical
  exact (univ : Finset V).sup (fun r => (univ.filter fun v => Even (G.dist r v)).card)

variable [Nontrivial V]

theorem exists_min_total_set (hG : G.Connected) :
    ∃ D : Finset V, TotallyDominates G D ∧ D.card = totalDominationNumber G := by
  classical
  apply Nat.sInf_mem (s := {k | ∃ D : Finset V, TotallyDominates G D ∧ D.card = k})
  refine ⟨_, univ, fun x => ?_, rfl⟩
  obtain ⟨y,hxy⟩ := (G.degree_pos_iff_exists_adj x).mp (degree_pos_of_connected hG x)
  exact ⟨y, mem_univ _, hxy⟩

theorem two_le_totalDominationNumber (hG : G.Connected) : 2 ≤ totalDominationNumber G := by
  obtain ⟨D,hD,he⟩ := exists_min_total_set hG
  obtain ⟨v⟩ := hG.nonempty
  obtain ⟨x,hx,_⟩ := hD v
  obtain ⟨y,hy,hxy⟩ := hD x
  rw [← he]
  exact one_lt_card.mpr ⟨x,hx,y,hy,hxy.ne⟩

/-- Connecting a minimum total dominating set charges at most two extra
vertices per pair beyond the first; all vertices outside can become leaves. -/
theorem order_total_leaves (hG : G.Connected) :
    Fintype.card V + 2 ≤ maxLeafCount G + totalDominationNumber G +
      2 * (totalDominationNumber G / 2) := by
  obtain ⟨D,hD,he⟩ := exists_min_total_set hG
  obtain ⟨C,hsub,hc,hcost⟩ := exists_connected_total_superset hG hD
  have hdom : TotallyDominates G C := fun x => by
    obtain ⟨y,hy,hxy⟩ := hD x
    exact ⟨y,hsub hy,hxy⟩
  have hord := order_le_connected_dominating_add_leaves hc hdom
  omega

/-- Stronger additive version of 258. -/
theorem evenMax_add_two (hG : G.Connected) :
    maxEvenLayerCount G + 2 ≤ totalDominationNumber G + maxLeafCount G := by
  classical
  have h := order_total_leaves hG
  have h₂ := two_le_maxLeafCount hG
  have he : maxEvenLayerCount G ≤ totalDominationNumber G + maxLeafCount G - 2 := by
    apply Finset.sup_le
    intro r _
    have hr := even_card_le_order_add_leaves hG r
    omega
  omega

/-- Exact catalog inequality in denominator-free form. -/
theorem graffiti258 (hG : G.Connected) :
    2 * maxEvenLayerCount G ≤ totalDominationNumber G * maxLeafCount G := by
  have hd := two_le_totalDominationNumber hG
  have hl := two_le_maxLeafCount hG
  have he := evenMax_add_two hG
  obtain ⟨d,hd'⟩ := Nat.exists_eq_add_of_le hd
  obtain ⟨l,hl'⟩ := Nat.exists_eq_add_of_le hl
  rw [hd',hl'] at he ⊢
  nlinarith [Nat.zero_le (d*l)]

end Graffiti
