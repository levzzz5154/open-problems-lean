import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Lattice

/-! # Independent domination and the neighborhood of a set

Written on the Wall II, no. 426 (2010); DeLaViña, Pepper and Waller,
*Graffiti.pc on the Independent-Domination Number of a Graph*, Conjecture 3.1:
https://www.uhd.edu/documents/academics/sciences/dpw-cn2011.pdf.
Definition 46 of the UHD list uses the union of the open vertex neighborhoods:
two adjacent members of `A` do belong to `N(A)`.
An earlier proof of the catalog row is recorded in the WoW / West dossier:
https://gist.github.com/siddhantdubey/22f22a7a23db5174ee59e32eaa8724aa
-/

namespace Graffiti

variable {V : Type*}

def Dominates (G : SimpleGraph V) (D : Finset V) : Prop :=
  ∀ v, v ∈ D ∨ ∃ w ∈ D, G.Adj v w

noncomputable def dominationNumber (G : SimpleGraph V) : ℕ :=
  sInf {n | ∃ D : Finset V, Dominates G D ∧ D.card = n}

noncomputable def independentDominationNumber (G : SimpleGraph V) : ℕ :=
  sInf {n | ∃ D : Finset V, G.IsIndepSet D ∧ Dominates G D ∧ D.card = n}

variable [Fintype V] [DecidableEq V]

/-- Extend any independent set to an inclusion-maximal one. -/
theorem extend_independent (G : SimpleGraph V) {C : Finset V} (hc : G.IsIndepSet C) :
    ∃ I : Finset V, C ⊆ I ∧ G.IsIndepSet I ∧ Dominates G I := by
  classical
  let F := Finset.univ.filter (fun I : Finset V => C ⊆ I ∧ G.IsIndepSet I)
  have hC : C ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.Subset.rfl, hc⟩
  obtain ⟨I,hI,hbest⟩ := F.exists_max_image Finset.card ⟨C,hC⟩
  obtain ⟨hsub,hind⟩ := (Finset.mem_filter.mp hI).2
  refine ⟨I, hsub, hind, ?_⟩
  intro v
  by_cases hv : v ∈ I
  · exact Or.inl hv
  right
  by_contra hn
  have hplus : G.IsIndepSet ((insert v I : Finset V) : Set V) := by
    rw [Finset.coe_insert]
    exact hind.insert_of_symmetric (fun _ _ h ha => h ha.symm)
      (fun w hw _ ha => hn ⟨w,hw,ha⟩)
  have hi : insert v I ∈ F := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,hsub.trans (Finset.subset_insert _ _),hplus⟩
  have hcard := hbest _ hi
  rw [Finset.card_insert_of_not_mem hv] at hcard
  omega

/-- The source's open neighborhood of a *set*, not its external boundary. -/
noncomputable def neighborhood (G : SimpleGraph V) (A : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => ∃ w ∈ A, G.Adj v w)

omit [DecidableEq V] in
theorem mem_neighborhood_iff {G : SimpleGraph V} {A : Finset V} {v : V} :
    v ∈ neighborhood G A ↔ ∃ w ∈ A, G.Adj v w := by classical simp [neighborhood]

/-- Stronger than no. 426: the subset is arbitrary and there is no hypothesis
on the order, connectivity, or degrees of the graph. -/
theorem independent_domination_add_neighborhood (G : SimpleGraph V) (A : Finset V) :
    independentDominationNumber G + dominationNumber (G.induce (neighborhood G A : Set V)) ≤
      Fintype.card V := by
  classical
  let H := neighborhood G A
  have hcore : G.IsIndepSet ((A \ H : Finset V) : Set V) := by
    intro x hx y hy _ hadj
    exact (Finset.mem_sdiff.mp hx).2 (mem_neighborhood_iff.mpr ⟨y,(Finset.mem_sdiff.mp hy).1,hadj⟩)
  obtain ⟨I,hcoreI,hind,hdom⟩ := extend_independent G hcore
  have h₁ : independentDominationNumber G ≤ I.card := Nat.sInf_le ⟨I,hind,hdom,rfl⟩
  let D := Iᶜ.subtype (fun v => v ∈ H)
  have hD : Dominates (G.induce (H : Set V)) D := by
    intro x
    by_cases hx : x.val ∈ I
    · right
      obtain ⟨y,hyA,hxy⟩ := mem_neighborhood_iff.mp x.property
      have hy : y ∉ I := fun hy => hind hx hy hxy.ne hxy
      have hyH : y ∈ H := by
        by_contra hmiss
        exact hy (hcoreI (Finset.mem_sdiff.mpr ⟨hyA,hmiss⟩))
      exact ⟨⟨y,hyH⟩,Finset.mem_subtype.mpr (Finset.mem_compl.mpr hy),hxy⟩
    · exact Or.inl (Finset.mem_subtype.mpr (Finset.mem_compl.mpr hx))
  have h₂ : dominationNumber (G.induce (H : Set V)) ≤ D.card := Nat.sInf_le ⟨D,hD,rfl⟩
  have hcard : D.card ≤ Iᶜ.card := by rw [Finset.card_subtype]; exact Finset.card_filter_le _ _
  have hsum : I.card + Iᶜ.card = Fintype.card V := Finset.card_add_card_compl I
  change independentDominationNumber G + dominationNumber (G.induce (H : Set V)) ≤ Fintype.card V
  omega

/-- DeLaViña–Pepper–Waller Conjecture 3.1 / Graffiti.pc 426. -/
theorem conjecture426 (G : SimpleGraph V) [DecidableRel G.Adj] :
    let M := Finset.univ.filter (fun v => G.degree v = G.maxDegree)
    independentDominationNumber G ≤ Fintype.card V - dominationNumber (G.induce (neighborhood G M : Set V)) := by
  dsimp only
  have hb := independent_domination_add_neighborhood G (Finset.univ.filter (fun v => G.degree v = G.maxDegree))
  omega

end Graffiti
