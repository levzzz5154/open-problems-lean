import Graffiti342
import Graffiti.PrunedTreeColors
import Graffiti.DegreeTwoEnds

/-! # Written on the Wall II, conjecture 343

One private leaf of each support of degree at least three can be omitted from
*both* of two total dominating sets. This leaves only degree-two supports as
an extra cost over the order. Each component of the degree-two vertices pays
for at most one such support, except for a chain terminating in leaves at both
ends, which then contains every nonleaf of the tree. This gives the catalog
bound even with `floor(n/2)` in place of the annihilation number of the
**complement**. No degree-two nonemptiness assumption is needed.

https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json
https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/definitions.json
-/

namespace Graffiti
open Finset SimpleGraph SupportCounting
variable {V : Type*} [Fintype V] [DecidableEq V] {T : SimpleGraph V} [DecidableRel T.Adj]

/-- In a tree of order at least three, twice the total domination number costs
at most the order plus the number of supports of ambient degree exactly two. -/
theorem degree_two_support_budget (ht : T.IsTree) (hn : 2 < Fintype.card V) :
    2 * totalDominationNumber T ≤ Fintype.card V + (supportVertices T ∩ degreeClass T 2).card := by
  classical
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  let S := supportVertices T
  let H := S \ degreeClass T 2
  have wit (s : H) : ∃ l, T.degree l = 1 ∧ T.Adj s.val l :=
    (support_iff_pendant T).mp (mem_sdiff.mp s.property).1
  choose f deg adj using wit
  have inj : Function.Injective f := by
    intro s t e; exact Subtype.ext (unique_neighbor_at_leaf T (deg s) (adj s).symm (e ▸ (adj t).symm))
  let R := H.attach.image f
  have size : R.card = H.card := (card_image_of_injective _ inj).trans card_attach
  have leaf {l} (hl : l ∈ R) : T.degree l = 1 := by
    obtain ⟨s,_,rfl⟩ := mem_image.mp hl; exact deg s
  have owner {x l : V} (hl : l ∈ R) (e : T.Adj x l) : ∃ s : H, s.val = x ∧ f s = l := by
    obtain ⟨s,_,rfl⟩ := mem_image.mp hl
    exact ⟨s,unique_neighbor_at_leaf T (deg s) (adj s).symm e.symm,rfl⟩
  have dis : Disjoint S R := disjoint_left.mpr (fun _ hs hr => leaf_not_support ht.isConnected hn (leaf hr) hs)
  have available (x : V) (miss : ¬ ∃ z ∈ S, T.Adj x z) : x ∉ R ∧ 2 ≤ (T.neighborFinset x \ R).card := by
    have pos := degree_pos_of_connected ht.isConnected x
    have ne : T.degree x ≠ 1 := by
      intro ex
      obtain ⟨y,ey⟩ := (T.degree_pos_iff_exists_adj x).mp pos
      exact miss ⟨y,(support_iff_pendant T).mpr ⟨x,ex,ey.symm⟩,ey⟩
    refine ⟨fun hx => ne (leaf hx),?_⟩
    have part := card_sdiff_add_card_inter (T.neighborFinset x) R
    rw [card_neighborFinset_eq_degree] at part
    by_cases he : (T.neighborFinset x ∩ R).Nonempty
    · obtain ⟨l,hl⟩ := he
      obtain ⟨s,ex,_⟩ := owner (mem_inter.mp hl).2 ((T.mem_neighborFinset _ _).mp (mem_inter.mp hl).1)
      have htwo : T.degree x ≠ 2 := fun e => (mem_sdiff.mp s.property).2 ((mem_degreeClass T).mpr (ex ▸ e))
      have cap : (T.neighborFinset x ∩ R).card ≤ 1 := by
        apply card_le_one.mpr
        intro a ha b hb
        obtain ⟨u,hu,fu⟩ := owner (mem_inter.mp ha).2 ((T.mem_neighborFinset _ _).mp (mem_inter.mp ha).1)
        obtain ⟨v,hv,fv⟩ := owner (mem_inter.mp hb).2 ((T.mem_neighborFinset _ _).mp (mem_inter.mp hb).1)
        exact fu.symm.trans ((congrArg f (Subtype.ext (hu.trans hv.symm))).trans fv)
      omega
    · have eq := not_nonempty_iff_eq_empty.mp he
      rw [eq,card_empty] at part; omega
  obtain ⟨K,clr⟩ := split_after_pruning ht R
  let U := (S ∪ R)ᶜ
  let A := U ∩ K
  let B := U \ K
  have body (x : V) : (∃ z ∈ S, T.Adj x z) ∨ ((∃ z ∈ A, T.Adj x z) ∧ (∃ z ∈ B, T.Adj x z)) := by
    by_cases h : ∃ z ∈ S, T.Adj x z
    · exact Or.inl h
    have hx := available x h
    obtain ⟨⟨a,ar,ak,ae⟩,⟨b,br,bk,be⟩⟩ := clr x hx.1 hx.2
    have rem {z} (hz : z ∉ R) (e : T.Adj x z) : z ∈ U := by
      apply mem_compl.mpr
      intro hs; exact (mem_union.mp hs).elim (fun inside => h ⟨z,inside,e⟩) hz
    exact Or.inr ⟨⟨a,mem_inter.mpr ⟨rem ar ae,ak⟩,ae⟩,⟨b,mem_sdiff.mpr ⟨rem br be,bk⟩,be⟩⟩
  have cost {X : Finset V} (h : ∀ x, (∃ z ∈ S, T.Adj x z) ∨ (∃ z ∈ X, T.Adj x z)) :
      totalDominationNumber T ≤ S.card + X.card := by
    have dom : TotallyDominates T (S ∪ X) := by
      intro x; rcases h x with ⟨z,hz,e⟩ | ⟨z,hz,e⟩
      · exact ⟨z,mem_union_left _ hz,e⟩
      · exact ⟨z,mem_union_right _ hz,e⟩
    exact (show totalDominationNumber T ≤ (S∪X).card from Nat.sInf_le ⟨_,dom,rfl⟩).trans (card_union_le _ _)
  have hA := cost (X := A) (fun x => (body x).imp_right And.left)
  have hB := cost (X := B) (fun x => (body x).imp_right And.right)
  have halve : B.card + A.card = U.card := card_sdiff_add_card_inter U K
  have full := card_add_card_compl (S ∪ R)
  rw [card_union_of_disjoint dis] at full
  change S.card+R.card+U.card = Fintype.card V at full
  have cut : H.card + (S ∩ degreeClass T 2).card = S.card := card_sdiff_add_card_inter S _
  change _ ≤ _ + (S ∩ degreeClass T 2).card
  omega

/-- Bound with no annihilation invariant and no exception for an empty degree class. -/
theorem half_order_component_bound (ht : T.IsTree) (hn : 2 < Fintype.card V) :
    totalDominationNumber T ≤ Fintype.card V / 2 + (degreeTwoComponents T + 1) / 2 := by
  have h := degree_two_support_budget ht hn
  rcases two_support_ends ht hn with count | ⟨one, count⟩ <;> omega

/-- The catalog's `A(Tᶜ)`, not `A(T)`. -/
theorem graffiti343 (ht : T.IsTree) (hn : 2 < Fintype.card V) :
    totalDominationNumber T ≤ annihilationNumber Tᶜ + (degreeTwoComponents T + 1)/2 :=
  (half_order_component_bound ht hn).trans (Nat.add_le_add_right (half_order_le_annihilationNumber Tᶜ) _)

end Graffiti

#print axioms Graffiti.degree_two_support_budget
#print axioms Graffiti.graffiti343
