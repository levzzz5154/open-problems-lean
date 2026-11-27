import Graffiti.TripleRadius
import Graffiti235

/-! # Written on the Wall II, conjecture 232

The catalog asks whether `2γₜ ≥ radius + ecc(B)` for the full periphery `B`.
In fact `radius + ecc(B) ≤ γₜ + 2⌊γₜ/2⌋`, with one unit to spare when the
minimum total dominating set has odd size. For a one-vertex graph no total
dominating set exists. Sources: UHD catalog conjecture 232 and definitions 52,55.

https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json
-/

namespace Graffiti

open SimpleGraph Finset

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- The two endpoints of a diameter and a vertex farthest from the periphery
are three pairwise `peripheryDepth`-separated vertices. -/
theorem exists_periphery_separated (hc : G.Connected) :
    ∃ a b v, peripheryDepth G ≤ G.dist a b ∧ peripheryDepth G ≤ G.dist a v ∧
      peripheryDepth G ≤ G.dist b v := by
  classical
  haveI : Nonempty V := hc.nonempty
  obtain ⟨a,b,hab⟩ := G.exists_dist_eq_diam
  obtain ⟨v,hv⟩ := farthest_from_periphery hc
  have ha := hv a (peripheral_of_dist_eq_diam hc hab)
  have hb := hv b (peripheral_of_dist_eq_diam hc ((dist_comm (u := b) (v := a)).trans hab))
  refine ⟨a,b,v,?_,(dist_comm (u := v) (v := a)) ▸ ha,(dist_comm (u := v) (v := b)) ▸ hb⟩
  rw [hab]; exact ha.trans (dist_le_diam (connected_iff_ediam_ne_top.mp hc))

/-- The parity-strengthened bound for every total dominating set. -/
theorem radius_periphery_budget (hc : G.Connected) {D : Finset V} (hD : TotallyDominates G D) :
    G.radius.toNat + peripheryDepth G ≤ D.card + 2*(D.card/2) := by
  obtain ⟨C,hs,hC,hcost⟩ := exists_connected_total_superset hc hD
  obtain ⟨a,b,v,hab,hav,hbv⟩ := exists_periphery_separated hc
  exact (radius_separation_core hc hC (fun x => by
    obtain ⟨y,hy,hxy⟩ := hD x; exact ⟨y,hs hy,hxy⟩) hab hav hbv).trans hcost

theorem graffiti232 [Nontrivial V] (hc : G.Connected) :
    G.radius.toNat + peripheryDepth G ≤ 2*totalDominationNumber G := by
  obtain ⟨D,hD,hd⟩ := exists_min_total_set hc
  have h := radius_periphery_budget hc hD
  omega

end Graffiti
