import Graffiti434
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting

/-! # Written on the Wall II, 434d

The number of components of the closed neighborhood of the peripheral set
may be replaced by the size of any packing of nonisolated vertices at pairwise
distance at least four. The proof uses just one application of degeneracy.
-/

namespace Graffiti

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Membership in the closed neighborhood of one vertex. -/
def InZone (G : SimpleGraph V) (b x : V) : Prop := x = b ∨ G.Adj b x

omit [Fintype V] in
private theorem extend_inside (G : SimpleGraph V) (T C : Finset V) (hCT : C ⊆ T)
    (hC : G.IsIndepSet C) : ∃ I : Finset V, C ⊆ I ∧ I ⊆ T ∧ G.IsIndepSet I ∧
      ∀ x ∈ T, x ∈ I ∨ ∃ w ∈ I, G.Adj x w := by
  classical
  let H := G.induce (T : Set V)
  let D : Finset (T : Set V) := C.subtype (fun x => x ∈ (T : Set V))
  have hD : H.IsIndepSet D := by
    intro x hx y hy hxy
    exact hC (Finset.mem_subtype.mp hx) (Finset.mem_subtype.mp hy)
      (fun e => hxy (Subtype.ext e))
  obtain ⟨J,hDJ,hJ,hd⟩ := extend_independent H hD
  let I := J.map (Function.Embedding.subtype (T : Set V))
  have memI (x : (T : Set V)) : x.val ∈ I ↔ x ∈ J := by
    change x.val ∈ J.map (Function.Embedding.subtype (T : Set V)) ↔ x ∈ J
    constructor
    · rintro h
      obtain ⟨y,hy,e⟩ := Finset.mem_map.mp h
      exact (show y = x from Subtype.ext e) ▸ hy
    · exact fun h => Finset.mem_map.mpr ⟨x,h,rfl⟩
  have hIT : I ⊆ T := by
    intro x hx
    obtain ⟨y,_,rfl⟩ := Finset.mem_map.mp hx
    exact y.property
  refine ⟨I,fun x hx => (memI ⟨x,hCT hx⟩).mpr (hDJ (Finset.mem_subtype.mpr hx)),hIT,?_,?_⟩
  · intro x hx y hy hxy
    exact hJ ((memI ⟨x,hIT hx⟩).mp hx) ((memI ⟨y,hIT hy⟩).mp hy)
      (fun e => hxy (congrArg Subtype.val e))
  · intro x hx
    rcases hd ⟨x,hx⟩ with h | ⟨w,hw,he⟩
    · exact Or.inl ((memI ⟨x,hx⟩).mpr h)
    · exact Or.inr ⟨w.val,(memI w).mpr hw,he⟩

/-- A family of nonisolated vertices whose closed neighborhoods are disjoint
and have no edges between them saves one vertex per neighborhood after the first. -/
theorem independent_domination_add_packing (G : SimpleGraph V) {K : Type*} [Fintype K]
    [Nonempty K] (b : K → V) (hn : ∀ i, ∃ y, G.Adj (b i) y)
    (hsep : ∀ {i j : K}, i ≠ j → ∀ {x y : V}, InZone G (b i) x → InZone G (b j) y →
      x ≠ y ∧ ¬ G.Adj x y) :
    independentDominationNumber G + Fintype.card K ≤ degeneracy Gᶜ + 2 := by
  classical
  -- A vertex is eligible if we can select neighbors of all but one center
  -- alongside it, excluding those same centers from its complement room.
  let T := Finset.univ.filter (fun v : V => ∃ p : K, ∀ i, i ≠ p →
    ¬G.Adj v (b i) ∧ ∃ y, G.Adj (b i) y ∧ ¬G.Adj v y)
  have memT {v : V} : v ∈ T ↔ ∃ p : K, ∀ i, i ≠ p →
      ¬G.Adj v (b i) ∧ ∃ y, G.Adj (b i) y ∧ ¬G.Adj v y := by simp [T]
  have zoneT {j : K} {v : V} (hv : InZone G (b j) v) : v ∈ T := by
    refine memT.mpr ⟨j,fun i hi => ?_⟩
    obtain ⟨y,hy⟩ := hn i
    exact ⟨(hsep (Ne.symm hi) hv (Or.inl rfl)).2,y,hy,(hsep (Ne.symm hi) hv (Or.inr hy)).2⟩
  let j₀ : K := Classical.arbitrary K
  obtain ⟨v,hv,hs⟩ := peel_univ G T (Finset.subset_univ _)
    ⟨b j₀,zoneT (j := j₀) (Or.inl rfl)⟩
  obtain ⟨p,hp⟩ := memT.mp hv
  let O := (Finset.univ : Finset K).erase p
  have memO {i : K} : i ∈ O ↔ i ≠ p := by simp [O]
  let y (i : K) := if h : i ≠ p then ((hp i h).2).choose else v
  have spec {i : K} (hi : i ∈ O) : G.Adj (b i) (y i) ∧ ¬G.Adj v (y i) := by
    have h := memO.mp hi
    simpa only [y,dif_pos h] using ((hp i h).2).choose_spec
  let C := insert v (O.image y)
  have seed (i : K) (hi : i ∈ O) : y i ∈ C :=
    Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
  have hvC : v ∈ C := Finset.mem_insert_self _ _
  have hCT : C ⊆ T := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | h
    · exact hv
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
      exact zoneT (j := i) (Or.inr (spec hi).1)
  have hC : G.IsIndepSet C := by
    intro x hx z hz hne e
    rcases Finset.mem_insert.mp hx with rfl | hx <;> rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hne rfl
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hz
      exact (spec hj).2 e
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      exact (spec hi).2 e.symm
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hz
      exact (hsep (fun h => hne (congrArg y h)) (Or.inr (spec hi).1) (Or.inr (spec hj).1)).2 e
  obtain ⟨I,hCI,hIT,hI,hd⟩ := extend_inside G T C hCT hC
  have dom : Dominates G I := by
    intro w
    by_cases hw : w ∈ T
    · exact hd w hw
    · right
      by_contra hmiss
      -- If w misses the selected neighbors, eligibility follows: it also
      -- misses every center, since a neighbor of a center belongs to T.
      apply hw
      refine memT.mpr ⟨p,fun i hi => ?_⟩
      have hi' := memO.mpr hi
      exact ⟨fun e => hw (zoneT (j := i) (Or.inr e.symm)),y i,(spec hi').1,
        fun e => hmiss ⟨y i,hCI (seed i hi'),e⟩⟩
  let B := O.image b
  have inj : Function.Injective b := by
    intro i j h
    by_contra hne
    exact (hsep hne (Or.inl rfl) (Or.inl rfl)).1 h
  have hdis : Disjoint I B := by
    apply Finset.disjoint_left.mpr
    intro x hx hb
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hb
    exact independent_nonadj G hI hx (hCI (seed i hi)) (spec hi).1
  have sub : I ∪ B ⊆ room G T v := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact (mem_room G).mpr ⟨hIT h,independent_nonadj G hI (hCI hvC) h⟩
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
      exact (mem_room G).mpr ⟨zoneT (j := i) (Or.inl rfl),(hp i (memO.mp hi)).1⟩
  have hsize := (Finset.card_le_card sub).trans hs
  rw [Finset.card_union_of_disjoint hdis] at hsize
  have hB : B.card = O.card := Finset.card_image_of_injective O inj
  have hO : O.card + 1 = Fintype.card K := Finset.card_erase_add_one (Finset.mem_univ p)
  have hmin : independentDominationNumber G ≤ I.card := Nat.sInf_le ⟨I,hI,dom,rfl⟩
  omega

/-- The union of the closed neighborhoods of the vertices in `B`. -/
noncomputable def closedNeighborhood (G : SimpleGraph V) (B : Finset V) : Finset V :=
  B ∪ neighborhood G B

private theorem mem_closed {G : SimpleGraph V} {B : Finset V} {x : V} :
    x ∈ closedNeighborhood G B ↔ ∃ b ∈ B, InZone G b x := by
  classical
  rw [closedNeighborhood,Finset.mem_union,mem_neighborhood_iff]
  constructor
  · rintro (hx | ⟨b,hb,he⟩)
    · exact ⟨x,hx,Or.inl rfl⟩
    · exact ⟨b,hb,Or.inr he.symm⟩
  · rintro ⟨b,hb,rfl | he⟩
    · exact Or.inl hb
    · exact Or.inr ⟨b,hb,he.symm⟩

/-- Pick one seed per closed-neighborhood component. Distinct seeds have
disjoint closed neighborhoods with no edge between those neighborhoods. -/
theorem closed_component_packing (G : SimpleGraph V) (B : Finset V) :
    ∃ b : (G.induce (closedNeighborhood G B : Set V)).ConnectedComponent → V,
      (∀ c, b c ∈ B) ∧ ∀ {i j}, i ≠ j → ∀ {x y : V}, InZone G (b i) x →
        InZone G (b j) y → x ≠ y ∧ ¬ G.Adj x y := by
  classical
  let U := closedNeighborhood G B
  let H := G.induce (U : Set V)
  have hU {b x : V} (hb : b ∈ B) (hx : InZone G b x) : x ∈ U := mem_closed.mpr ⟨b,hb,hx⟩
  have has (c : H.ConnectedComponent) : ∃ z : (U : Set V), z.val ∈ B ∧ H.connectedComponentMk z = c := by
    induction c using SimpleGraph.ConnectedComponent.ind with
    | _ x =>
      obtain ⟨b,hb,hz⟩ := mem_closed.mp x.property
      let z : (U : Set V) := ⟨b,hU hb (Or.inl rfl)⟩
      refine ⟨z,hb,?_⟩
      rcases hz with h | e
      · exact congrArg H.connectedComponentMk (Subtype.ext h.symm)
      · exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj (show H.Adj z x from e)
  let rep (c : H.ConnectedComponent) := (has c).choose
  let b (c : H.ConnectedComponent) := (rep c).val
  have hb (c : H.ConnectedComponent) : b c ∈ B := ((has c).choose_spec).1
  have classOf {c : H.ConnectedComponent} {x : V} (hx : InZone G (b c) x) :
      H.connectedComponentMk ⟨x,hU (hb c) hx⟩ = c := by
    have e : H.connectedComponentMk (rep c) = c := ((has c).choose_spec).2
    refine Eq.trans ?_ e
    rcases hx with hx | hx
    · exact congrArg H.connectedComponentMk (Subtype.ext hx)
    · exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        (show H.Adj ⟨x,_⟩ (rep c) from hx.symm)
  have sep {i j : H.ConnectedComponent} (hij : i ≠ j) {x y : V}
      (hx : InZone G (b i) x) (hy : InZone G (b j) y) : x ≠ y ∧ ¬G.Adj x y := by
    have link (e : H.connectedComponentMk ⟨x,hU (hb i) hx⟩ =
        H.connectedComponentMk ⟨y,hU (hb j) hy⟩) : False := hij ((classOf hx).symm.trans (e.trans (classOf hy)))
    exact ⟨fun e => link (congrArg H.connectedComponentMk (Subtype.ext e)),
      fun e => link (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        (show H.Adj ⟨x,_⟩ ⟨y,_⟩ from e))⟩
  exact ⟨b,hb,@sep⟩

/-- A vertex set may replace the peripheral set provided its vertices are
nonisolated. We count actual connected components of its closed neighborhood. -/
theorem independent_domination_add_components (G : SimpleGraph V) (B : Finset V)
    (hB : B.Nonempty) (hn : ∀ b ∈ B, ∃ y, G.Adj b y) :
    independentDominationNumber G + Nat.card (G.induce (closedNeighborhood G B : Set V)).ConnectedComponent
      ≤ degeneracy Gᶜ + 2 := by
  classical
  let H := G.induce (closedNeighborhood G B : Set V)
  obtain ⟨a,ha⟩ := hB
  letI : Nonempty H.ConnectedComponent := ⟨H.connectedComponentMk ⟨a,Finset.mem_union_left _ ha⟩⟩
  obtain ⟨b,hb,sep⟩ := closed_component_packing G B
  change independentDominationNumber G + Nat.card H.ConnectedComponent ≤ _
  rw [Nat.card_eq_fintype_card]
  exact independent_domination_add_packing G b (fun c => hn _ (hb c)) @sep

/-- The vertices of maximum eccentricity. -/
noncomputable def peripheralVertices (G : SimpleGraph V) : Finset V := by
  classical exact Finset.univ.filter (fun v => G.eccent v = G.ediam)

/-- Graffiti.pc 434d, in equivalent additive form to avoid truncated subtraction. -/
theorem conjecture434d (G : SimpleGraph V) (hc : G.Connected) (hn : 3 < Fintype.card V) :
    independentDominationNumber G + Nat.card (G.induce (closedNeighborhood G (peripheralVertices G) : Set V)).ConnectedComponent
      ≤ degeneracy Gᶜ + 2 := by
  classical
  letI : Nonempty V := hc.nonempty
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a,ha⟩ := G.exists_eccent_eq_ediam_of_finite
  apply independent_domination_add_components G _ ⟨a,by simpa [peripheralVertices] using ha⟩
  intro b _
  obtain ⟨z,hz⟩ := exists_ne b
  obtain ⟨w⟩ := hc.preconnected b z
  cases w with
  | nil => exact False.elim (hz rfl)
  | cons e _ => exact ⟨_,e⟩

end Graffiti
