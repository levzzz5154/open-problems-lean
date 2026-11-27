import Graffiti.ForcedSupports

/-! # Written on the Wall II, Graffiti.pc 365

The catalog counts isolated vertices in the graph induced by the supports, and
edges whose *both* endpoints have degree two (definition 33).[24][25]

For a total dominating set `D`, choose a neighbor `f x ∈ D` of each vertex.
Write `I` for the isolated supports and `R = D ∖ I`. The edges `x -- f x`
for `x ∉ R` are distinct: an arc starting in `I` ends in `R`, and an arc
starting outside `D` ends in `D`. This leaves at most `|R| - 1` other edges
in a tree. Each chosen edge of type 2--2 is charged to a vertex of `R`,
with at most two charges per vertex. The exceptional case `f x ∈ I` is
paid for by its pendant neighbor, which must equal `f (f x)`.

Sources:
* [24] https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json
* [25] https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/definitions.json
-/

namespace Graffiti

open Finset SimpleGraph SupportCounting

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Isolates of the induced subgraph on the support vertices. -/
def isolatedSupports : Finset V :=
  (supportVertices G).filter fun v => withinDegree G (supportVertices G) v = 0

/-- Ambient edges induced by the class of vertices of degree two. -/
noncomputable def degreeTwoEdges : Finset (Sym2 V) := by
  classical exact G.edgeFinset.filter fun e => ∀ v ∈ e, G.degree v = 2

omit [DecidableEq V] in
private theorem isolated_not_adj {x y : V} (hx : x ∈ isolatedSupports G)
    (hy : y ∈ isolatedSupports G) (ha : G.Adj x y) : False := by
  have hp := card_pos.mpr (show ((supportVertices G).filter (G.Adj x)).Nonempty from
    ⟨y, mem_filter.mpr ⟨(mem_filter.mp hy).1, ha⟩⟩)
  have hz : ((supportVertices G).filter (G.Adj x)).card = 0 := (mem_filter.mp hx).2
  omega

/-- The other neighbor of a degree-two support adjacent to a degree-two vertex
is a leaf. -/
private theorem other_is_leaf {s x y : V} (hs : s ∈ isolatedSupports G)
    (ds : G.degree s = 2) (dx : G.degree x = 2) (hx : G.Adj s x)
    (hy : G.Adj s y) (hne : x ≠ y) : G.degree y = 1 := by
  obtain ⟨l, dl, hl⟩ := (support_iff_pendant G).mp (mem_filter.mp hs).1
  have sub : ({x,y} : Finset V) ⊆ G.neighborFinset s := by
    simp only [insert_subset_iff, singleton_subset_iff, mem_neighborFinset]
    exact ⟨hx, hy⟩
  have eq := eq_of_subset_of_card_le sub (show (G.neighborFinset s).card ≤ ({x,y} : Finset V).card by
    rw [card_pair hne, card_neighborFinset_eq_degree, ds])
  have hm := (G.mem_neighborFinset s l).mpr hl
  rw [← eq, mem_insert, mem_singleton] at hm
  rcases hm with rfl | rfl <;> omega

/-- In every finite graph the potential excess over the tree bound is paid
for by the number of edges relative to the number of vertices. -/
theorem support_edge_budget {D : Finset V} (hd : TotallyDominates G D) :
    3 * (isolatedSupports G).card + (degreeTwoEdges G).card + Fintype.card V ≤
      3 * D.card + G.edgeFinset.card := by
  classical
  let I := isolatedSupports G
  let R := D \ I
  have hin : I ⊆ D := fun _ hx => support_forced G hd (mem_filter.mp hx).1
  choose f hf ha using hd
  have step {x} (hx : x ∈ I) : f x ∈ R :=
    mem_sdiff.mpr ⟨hf x, fun h => isolated_not_adj G hx h (ha x)⟩
  have selected {x} (hx : x ∈ Rᶜ) (h : x ∈ D) : x ∈ I := by
    by_contra hn
    exact (mem_compl.mp hx) (mem_sdiff.mpr ⟨h,hn⟩)
  let edge (x : V) := s(x, f x)
  let C := Rᶜ.image edge
  have ccard : C.card = Rᶜ.card := by
    apply card_image_of_injOn
    intro x hx y hy he
    rcases Sym2.eq_iff.mp he with h | ⟨hxy, hyx⟩
    · exact h.1
    · have hxD : x ∈ D := hxy ▸ hf y
      exact False.elim ((mem_compl.mp hy) (hyx ▸ step (selected hx hxD)))
  have csub : C ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨x, _, rfl⟩ := mem_image.mp he
    exact mem_edgeFinset.mpr (ha x)
  let Q := Rᶜ.filter fun x => G.degree x = 2 ∧ G.degree (f x) = 2
  have qsub : degreeTwoEdges G ∩ C ⊆ Q.image edge := by
    intro e he
    obtain ⟨he, hc⟩ := mem_inter.mp he
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hc
    have h : ∀ v ∈ edge x, G.degree v = 2 := (mem_filter.mp he).2
    exact mem_image.mpr ⟨x, mem_filter.mpr ⟨hx, h _ (Sym2.mem_iff.mpr (Or.inl rfl)),
      h _ (Sym2.mem_iff.mpr (Or.inr rfl))⟩, rfl⟩
  let pay (x : V) := if f x ∈ I then f (f x) else f x
  have paid (x : V) : pay x ∈ R := by
    dsimp only [pay]
    split
    · exact step ‹_›
    · exact mem_sdiff.mpr ⟨hf _, ‹_›⟩
  have exceptional {x} (hx : x ∈ Q) (hi : f x ∈ I) : G.degree (f (f x)) = 1 := by
    obtain ⟨hx', dx, ds⟩ := mem_filter.mp hx
    apply other_is_leaf G hi ds dx (ha x).symm (ha (f x))
    intro he
    exact (mem_compl.mp hx') (he ▸ step hi)
  have qcard : Q.card ≤ R.card * 2 := by
    let rel (x y : V) := pay x = y
    have above : ∀ x ∈ Q, 1 ≤ (R.bipartiteAbove rel x).card := by
      intro x _
      exact card_pos.mpr ⟨pay x, (mem_bipartiteAbove rel).mpr ⟨paid x, rfl⟩⟩
    have below (y : V) (_hy : y ∈ R) : (Q.bipartiteBelow rel y).card ≤ 2 := by
      by_cases dy : G.degree y = 2
      · apply le_trans (card_le_card (t := G.neighborFinset y) ?_) dy.le
        intro x hx
        obtain ⟨hq, he⟩ := (mem_bipartiteBelow rel).mp hx
        change pay x = y at he
        by_cases hi : f x ∈ I
        · have eq : f (f x) = y := by simpa [pay,hi] using he
          have d := exceptional hq hi
          rw [eq,dy] at d
          contradiction
        · have eq : f x = y := by simpa [pay,hi] using he
          exact (G.mem_neighborFinset _ _).mpr (eq ▸ (ha x).symm)
      · have via {x : V} (hx : x ∈ Q.bipartiteBelow rel y) : G.Adj y (f x) ∧ G.degree y = 1 := by
          obtain ⟨hq, he⟩ := (mem_bipartiteBelow rel).mp hx
          change pay x = y at he
          by_cases hi : f x ∈ I
          · have eq : f (f x) = y := by simpa [pay,hi] using he
            exact eq ▸ ⟨(ha (f x)).symm, exceptional hq hi⟩
          · have eq : f x = y := by simpa [pay,hi] using he
            exact False.elim (dy (eq ▸ (mem_filter.mp hq).2.2))
        by_cases hn : (Q.bipartiteBelow rel y).Nonempty
        · obtain ⟨z,hz⟩ := hn
          have dz := (mem_filter.mp ((mem_bipartiteBelow rel).mp hz).1).2.2
          apply le_trans (card_le_card (t := G.neighborFinset (f z)) ?_) dz.le
          intro x hx
          have eq := unique_neighbor_at_leaf G (via hz).2 (via hx).1 (via hz).1
          exact (G.mem_neighborFinset _ _).mpr (eq ▸ (ha x).symm)
        · simp [not_nonempty_iff_eq_empty.mp hn]
    simpa only [Nat.mul_one] using card_mul_le_card_mul rel above below
  have h₁ := (card_le_card qsub).trans card_image_le
  have h₂ : (degreeTwoEdges G \ C).card ≤ (G.edgeFinset \ C).card := by
    apply card_le_card
    intro e he
    exact mem_sdiff.mpr ⟨(mem_filter.mp (mem_sdiff.mp he).1).1, (mem_sdiff.mp he).2⟩
  have h₃ := card_sdiff_add_card_inter (degreeTwoEdges G) C
  have h₄ := card_sdiff_add_card_eq_card csub
  have h₅ : R.card + I.card = D.card := card_sdiff_add_card_eq_card hin
  have h₆ := card_add_card_compl R
  change 3 * I.card + _ + _ ≤ _
  omega

/-- WoW II 365, strengthened by one unit in the integer-scaled inequality. -/
theorem graffiti365 {T : SimpleGraph V} [DecidableRel T.Adj] (ht : T.IsTree)
    (hn : 2 < Fintype.card V) :
    3 * (isolatedSupports T).card + (degreeTwoEdges T).card + 1 ≤
      3 * totalDominationNumber T := by
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨D, hd, hmin⟩ := exists_min_total_set ht.isConnected
  have h := support_edge_budget T hd
  have he := ht.card_edgeFinset
  rw [hmin] at h
  omega

end Graffiti

#print axioms Graffiti.graffiti365
