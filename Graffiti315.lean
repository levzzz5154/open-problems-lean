import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Path

/-! # Pendant vertices and well total dominated graphs

Written on the Wall II, Graffiti.pc no. 315 (definitions 5, 94, 99 and 123).
The star case includes the two-vertex graph: either endpoint may serve as its center.
-/

namespace Graffiti

open SimpleGraph Finset

variable {V : Type*}

/-- Every vertex, including each member of `D`, has a neighbor in `D`. -/
def TotallyDominates (G : SimpleGraph V) (D : Finset V) : Prop :=
  ∀ v, ∃ w ∈ D, G.Adj v w

/-- Inclusion minimality, rather than minimum cardinality. -/
def MinimalTotalDominatingSet (G : SimpleGraph V) (D : Finset V) : Prop :=
  TotallyDominates G D ∧ ∀ E ⊆ D, TotallyDominates G E → E = D

def WellTotalDominated (G : SimpleGraph V) : Prop :=
  ∀ D, MinimalTotalDominatingSet G D → ∀ E, TotallyDominates G E → D.card ≤ E.card

variable [Fintype V]

def pendantVertices (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter fun v => G.degree v = 1

variable {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem pendant_adj_unique {v a b : V} (hv : v ∈ pendantVertices G)
    (ha : G.Adj v a) (hb : G.Adj v b) : a = b := by
  have hdeg : G.degree v = 1 := (mem_filter.mp hv).2
  have hle : (G.neighborFinset v).card ≤ 1 := hdeg.le
  exact (card_le_one.mp hle) a ((G.mem_neighborFinset v a).mpr ha)
    b ((G.mem_neighborFinset v b).mpr hb)

/-- If every neighbor of `c` is pendant, its closed neighborhood is a whole
connected component. Every minimal total dominating set in this star is a pair. -/
private theorem wellTotalDominated_star (hG : G.Preconnected) (c : V)
    (hleaf : ∀ w, G.Adj c w → w ∈ pendantVertices G) : WellTotalDominated G := by
  classical
  have hclosed (v : V) : v = c ∨ G.Adj c v := by
    have hr := (reachable_iff_reflTransGen (G := G) c v).mp (hG c v)
    induction hr with
    | refl => exact Or.inl rfl
    | tail _ hxy ih =>
      rcases ih with h | h
      · exact Or.inr (h ▸ hxy)
      · exact Or.inl (pendant_adj_unique (hleaf _ h) hxy h.symm)
  intro D hD E hE
  obtain ⟨z, hz, hcz⟩ := hD.1 c
  have hforced {S : Finset V} (hS : TotallyDominates G S) : c ∈ S := by
    obtain ⟨y, hy, hzy⟩ := hS z
    exact (pendant_adj_unique (hleaf _ hcz) hzy hcz.symm) ▸ hy
  have hpair : TotallyDominates G ({c, z} : Finset V) := by
    intro v
    rcases hclosed v with rfl | hcv
    · exact ⟨z, by simp, hcz⟩
    · exact ⟨c, by simp, hcv.symm⟩
  have heq := hD.2 {c, z} (insert_subset (hforced hD.1) (singleton_subset_iff.mpr hz)) hpair
  obtain ⟨w, hw, hcw⟩ := hE c
  calc
    D.card = ({c, z} : Finset V).card := congrArg Finset.card heq.symm
    _ = 2 := card_pair hcz.ne
    _ ≤ E.card := one_lt_card.mpr ⟨c, hforced hE, w, hw, hcw.ne⟩

/-- Outside the star case, the nonpendants form a total dominating set. The
independence bound forces each nonpendant to have a pendant neighbor, so this
set is contained in every total dominating set. -/
theorem wellTotalDominated_of_indepNum_le_pendants (hG : G.Preconnected)
    (hα : G.indepNum ≤ (pendantVertices G).card) : WellTotalDominated G := by
  classical
  by_cases hstar : ∃ c, ∀ w, G.Adj c w → w ∈ pendantVertices G
  · obtain ⟨c, hc⟩ := hstar
    exact wellTotalDominated_star hG c hc
  have hcore : TotallyDominates G (pendantVertices G)ᶜ := by
    intro v
    by_contra hn
    apply hstar
    refine ⟨v, fun w hvw => ?_⟩
    by_contra hw
    exact hn ⟨w, mem_compl.mpr hw, hvw⟩
  have hind : G.IsIndepSet (pendantVertices G : Set V) := by
    intro v hv w hw _ hvw
    obtain ⟨a, ha, hva⟩ := hcore v
    exact (mem_compl.mp ha) ((pendant_adj_unique hv hvw hva) ▸ hw)
  have hforced {S : Finset V} (hS : TotallyDominates G S) : (pendantVertices G)ᶜ ⊆ S := by
    intro v hv
    by_contra hmiss
    have hins : G.IsIndepSet ((insert v (pendantVertices G) : Finset V) : Set V) := by
      rw [Finset.coe_insert]
      apply hind.insert_of_symmetric (fun _ _ hn ha => hn ha.symm)
      intro w hw _ hvw
      obtain ⟨a, ha, hwa⟩ := hS w
      exact hmiss ((pendant_adj_unique hw hwa hvw.symm) ▸ ha)
    have hcard := hins.card_le_indepNum.trans hα
    rw [card_insert_of_not_mem (mem_compl.mp hv)] at hcard
    omega
  intro D hD E hE
  have heq := hD.2 _ (hforced hD.1) hcore
  exact heq ▸ card_le_card (hforced hE)

/-- Graffiti.pc conjecture 315. -/
theorem conjecture315 (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (_hn : 1 < Fintype.card V) (hα : G.indepNum = (pendantVertices G).card) :
    WellTotalDominated G :=
  wellTotalDominated_of_indepNum_le_pendants hG.preconnected hα.le

end Graffiti
