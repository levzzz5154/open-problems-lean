import Graffiti365
import Graffiti.AnnihilationDegree

/-! # Written on the Wall II, 332 and 342

The catalog records 332 as a consequence of a stronger bound of DeLaViña,
Larson, Pepper and Waller, *On total domination and support vertices of a tree*
(see the catalog comments on 332). Here we give a direct two-color proof.
Color consecutive pairs of distance layers alternately, starting at a leaf.
Put every support in both sets, and discard one leaf at every nonisolated
support. The two resulting total dominating sets together cost at most n+i.
The overline in 342 means the annihilation number is taken in the complement.

https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/comments.json
https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json
-/

namespace Graffiti
open SimpleGraph Finset SupportCounting
variable {V : Type*} [Fintype V] [DecidableEq V] {T : SimpleGraph V} [DecidableRel T.Adj]

/-- A non-root nonleaf has both an inward and an outward neighbor. Counting
parent edges shows that every edge is used, without a uniqueness-of-paths argument. -/
theorem exists_straddling_neighbors (ht : T.IsTree) {r x : V} (hx : x ≠ r) (hd : 1 < T.degree x) :
    ∃ a b, T.Adj x a ∧ T.Adj x b ∧ T.dist a r + 1 = T.dist x r ∧ T.dist x r + 1 = T.dist b r := by
  classical
  let U := (univ : Finset V).erase r
  have step (v : ↥U) : ∃ y, T.Adj v.val y ∧ T.dist y r + 1 = T.dist v.val r := by
    obtain ⟨p,hp⟩ := ht.isConnected.exists_walk_length_eq_dist v.val r
    have ne : v.val ≠ r := (mem_erase.mp v.property).1
    have hn := Walk.not_nil_of_ne (p := p) ne
    have adj := p.adj_snd hn
    have hl := p.length_tail_add_one hn
    have lo := dist_le p.tail
    have hi := ht.isConnected.dist_triangle (u := v.val) (v := p.snd) (w := r)
    rw [dist_eq_one_iff_adj.mpr adj] at hi
    exact ⟨_,adj,by omega⟩
  choose f ha hh using step
  let edge (v : ↥U) := s(v.val, f v)
  have inj : Function.Injective edge := by
    intro v w he
    rcases Sym2.eq_iff.mp he with h | ⟨h,k⟩
    · exact Subtype.ext h.1
    · have hv := hh v
      have hw := hh w
      rw [k,h] at hv
      omega
  have eq : U.attach.image edge = T.edgeFinset := by
    apply eq_of_subset_of_card_le
    · intro e he; obtain ⟨v,_,rfl⟩ := mem_image.mp he
      exact mem_edgeFinset.mpr (ha v)
    · rw [card_image_of_injective _ inj,card_attach]
      have hu := card_erase_add_one (mem_univ r)
      rw [card_univ] at hu
      have := ht.card_edgeFinset
      change _ ≤ (univ.erase r).card
      omega
  let v : ↥U := ⟨x,mem_erase.mpr ⟨hx,mem_univ _⟩⟩
  obtain ⟨b,hb,ne⟩ := exists_ne_of_one_lt_card (s := T.neighborFinset x) hd (f v)
  have adj := (T.mem_neighborFinset x b).mp hb
  have hm : s(x,b) ∈ T.edgeFinset := mem_edgeFinset.mpr adj
  rw [←eq] at hm
  obtain ⟨w,_,he⟩ := mem_image.mp hm
  rcases Sym2.eq_iff.mp he with ⟨h,k⟩ | ⟨h,k⟩
  · have e : w = v := Subtype.ext h
    exact False.elim (ne (e ▸ k.symm))
  · refine ⟨f v,b,ha v,adj,hh v,?_⟩
    simpa only [h,k] using hh w

theorem leaf_not_support (hc : T.Connected) (hn : 2 < Fintype.card V) {l : V}
    (hl : T.degree l = 1) : l ∉ supportVertices T := by
  intro hs
  obtain ⟨y,hy,e⟩ := (support_iff_pendant T).mp hs
  have sub : (univ : Finset V) ⊆ {l,y} := by
    intro v _
    have hr := (reachable_iff_reflTransGen (G := T) l v).mp (hc l v)
    induction hr with
    | refl => simp
    | tail _ hab ih =>
      rcases mem_insert.mp (ih (mem_univ _)) with rfl | hm
      · exact mem_insert_of_mem (mem_singleton.mpr (unique_neighbor_at_leaf T hl hab e))
      · obtain rfl := mem_singleton.mp hm
        exact mem_insert.mpr (Or.inl (unique_neighbor_at_leaf T hy hab e.symm))
  have h := card_le_card sub
  rw [card_univ,card_pair e.ne] at h
  omega

/-- The published isolate-of-support bound, via two total dominating sets. -/
theorem graffiti332 (ht : T.IsTree) (hn : 2 < Fintype.card V) :
    2 * totalDominationNumber T ≤ Fintype.card V + (isolatedSupports T).card := by
  classical
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨v⟩ := ht.isConnected.nonempty
  have count := tree_leaf_bounds ht v
  obtain ⟨r,hr⟩ := card_pos.mp (show 0 < (pendantVertices T).card by omega)
  have dr : T.degree r = 1 := (mem_filter.mp hr).2
  let S := supportVertices T
  let I := isolatedSupports T
  let C := S \ I
  have wit (x : ↥C) : ∃ l, T.degree l = 1 ∧ T.Adj x.val l :=
    (support_iff_pendant T).mp (mem_sdiff.mp x.property).1
  choose f dl adj using wit
  have inj : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    exact unique_neighbor_at_leaf T (dl x) (adj x).symm (he ▸ (adj y).symm)
  let R := C.attach.image f
  have dis : Disjoint S R := by
    apply disjoint_left.mpr; intro l hs hl
    obtain ⟨x,_,rfl⟩ := mem_image.mp hl
    exact leaf_not_support ht.isConnected hn (dl x) hs
  have covered {x : V} (hx : x ∈ C) : ∃ z ∈ S, T.Adj x z := by
    have hi := (mem_sdiff.mp hx).2
    have hs := (mem_sdiff.mp hx).1
    have nz : ((supportVertices T).filter (T.Adj x)).card ≠ 0 :=
      fun h => hi (mem_filter.mpr ⟨hs,h⟩)
    obtain ⟨z,hz⟩ := card_pos.mp (Nat.pos_of_ne_zero nz)
    exact ⟨z,(mem_filter.mp hz).1,(mem_filter.mp hz).2⟩
  let U := (S ∪ R)ᶜ
  let K := univ.filter fun a => T.dist a r % 4 < 2
  let A := U ∩ K
  let B := U \ K
  have body (x : V) : (∃ z ∈ S, T.Adj x z) ∨
      ((∃ z ∈ A, T.Adj x z) ∧ (∃ z ∈ B, T.Adj x z)) := by
    by_cases h : ∃ z ∈ S, T.Adj x z
    · exact Or.inl h
    right
    have hd : 1 < T.degree x := by
      have hp := degree_pos_of_connected ht.isConnected x
      by_contra! le
      have dx : T.degree x = 1 := by omega
      obtain ⟨y,ey⟩ := (T.degree_pos_iff_exists_adj x).mp hp
      exact h ⟨y,(support_iff_pendant T).mpr ⟨x,dx,ey.symm⟩,ey⟩
    have hx : x ≠ r := fun e => by rw [e,dr] at hd; omega
    obtain ⟨a,b,ea,eb,da,db⟩ := exists_straddling_neighbors ht hx hd
    have avail {z} (ez : T.Adj x z) : z ∈ U := by
      apply mem_compl.mpr; intro hz
      rcases mem_union.mp hz with hs | hr'
      · exact h ⟨z,hs,ez⟩
      · obtain ⟨c,_,he⟩ := mem_image.mp hr'
        subst z
        have eq := unique_neighbor_at_leaf T (dl c) ez.symm (adj c).symm
        exact h (eq ▸ covered c.property)
    have key : a ∈ K ↔ b ∉ K := by
      simp only [K,mem_filter,mem_univ,true_and]; omega
    by_cases hk : a ∈ K
    · exact ⟨⟨a,mem_inter.mpr ⟨avail ea,hk⟩,ea⟩,⟨b,mem_sdiff.mpr ⟨avail eb,key.mp hk⟩,eb⟩⟩
    · have hb : b ∈ K := by by_contra h'; exact hk (key.mpr h')
      exact ⟨⟨b,mem_inter.mpr ⟨avail eb,hb⟩,eb⟩,⟨a,mem_sdiff.mpr ⟨avail ea,hk⟩,ea⟩⟩
  have dom {D : Finset V} (p : ∀ x, (∃ z ∈ S, T.Adj x z) ∨ (∃ z ∈ D, T.Adj x z)) :
      totalDominationNumber T ≤ S.card + D.card := by
    have hd : TotallyDominates T (S ∪ D) := by
      intro x; rcases p x with ⟨z,hz,e⟩ | ⟨z,hz,e⟩
      · exact ⟨z,mem_union_left _ hz,e⟩
      · exact ⟨z,mem_union_right _ hz,e⟩
    exact (show totalDominationNumber T ≤ (S ∪ D).card from Nat.sInf_le ⟨_,hd,rfl⟩).trans (card_union_le _ _)
  have hA := dom (fun x => (body x).imp_right And.left)
  have hB := dom (fun x => (body x).imp_right And.right)
  have part : B.card + A.card = U.card := card_sdiff_add_card_inter U K
  have hU := card_add_card_compl (S ∪ R)
  rw [card_union_of_disjoint dis] at hU
  have sum : S.card + R.card + U.card = Fintype.card V := hU
  have num : R.card = C.card := (card_image_of_injective _ inj).trans card_attach
  have rem : C.card + I.card = S.card := card_sdiff_add_card_eq_card (fun _ hi => (mem_filter.mp hi).1)
  change _ ≤ _ + I.card
  omega

/-- WoW II 342, with the annihilation number of the complement. -/
theorem graffiti342 (ht : T.IsTree) (hn : 2 < Fintype.card V) :
    totalDominationNumber T ≤ annihilationNumber Tᶜ + ((isolatedSupports T).card + 1) / 2 := by
  have := graffiti332 ht hn
  have := half_order_le_annihilationNumber Tᶜ
  omega

end Graffiti

#print axioms Graffiti.graffiti332
#print axioms Graffiti.graffiti342
