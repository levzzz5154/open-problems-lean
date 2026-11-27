import Graffiti258
import Graffiti450

namespace Graffiti

open Finset SimpleGraph SupportCounting

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem support_iff_pendant {x : V} : x ∈ supportVertices G ↔ ∃ l, G.degree l = 1 ∧ G.Adj x l := by
  classical simp [supportVertices, withinDegree, card_pos, Finset.Nonempty]

theorem unique_neighbor_at_leaf {x a b : V} (hx : G.degree x = 1)
    (ha : G.Adj x a) (hb : G.Adj x b) : a = b :=
  card_le_one.mp (show (G.neighborFinset x).card ≤ 1 from hx.le)
    _ ((G.mem_neighborFinset _ _).mpr ha) _ ((G.mem_neighborFinset _ _).mpr hb)

theorem support_forced {D : Finset V} (hd : TotallyDominates G D) : supportVertices G ⊆ D := by
  intro x hx
  obtain ⟨l,hl,hxl⟩ := (support_iff_pendant G).mp hx
  obtain ⟨y,hy,hly⟩ := hd l
  exact (unique_neighbor_at_leaf G hl hly hxl.symm) ▸ hy

omit [Fintype V] [DecidableRel G.Adj] in
/-- Vertices with pairwise disjoint open neighborhoods outside a forced set
require distinct additional total dominators. -/
theorem forced_plus_disjoint_neighborhoods {S W D : Finset V} (hd : TotallyDominates G D)
    (forced : S ⊆ D) (outside : ∀ x ∈ W, ∀ y, G.Adj x y → y ∉ S)
    (sep : ∀ x ∈ W, ∀ z ∈ W, ∀ y, G.Adj x y → G.Adj z y → x = z) :
    S.card + W.card ≤ D.card := by
  classical
  choose f hf ha using hd
  have inj : Set.InjOn f (W : Set V) := by
    intro x hx z hz h
    exact sep x hx z hz _ (ha x) (h ▸ ha z)
  have sub : W.image f ⊆ D \ S := by
    intro y hy; obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
    exact mem_sdiff.mpr ⟨hf x,outside x hx _ (ha x)⟩
  have lower := card_le_card sub
  rw [card_image_of_injOn inj] at lower
  have := card_sdiff_add_card_eq_card forced
  omega

end Graffiti
