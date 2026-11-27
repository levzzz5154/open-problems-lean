import Graffiti.ForcedSupports
import Graffiti.MaxLeafStar

/-! # The cost of omitting an independent high-degree vertex

For total dominators `D` in a tree, the excess degrees outside `D` and
excess domination multiplicities everywhere sum to `|D|−2`. If `I` is
independent, the selected members of `I` each need a neighbor in `D ∖ I`.
An omitted member of degree at least three uses two excess-degree units,
and cannot be tight: either it has an unselected nonleaf neighbor outside
`I`, or it is dominated several times. This isolates the equality case
needed by Written on the Wall II 376 and 377.
-/

namespace Graffiti

open Finset SimpleGraph SupportCounting

variable {V : Type*} [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj]

omit [Fintype V] [DecidableEq V] in
private theorem incidence_swap (A B : Finset V) :
    (∑ x ∈ A, withinDegree T B x) = ∑ y ∈ B, withinDegree T A y := by
  refine (sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow T.Adj (s := A) (t := B)).trans ?_
  apply sum_congr rfl; intro y _
  apply congrArg Finset.card
  ext x
  simp only [mem_bipartiteBelow,mem_filter]
  exact and_congr_right fun _ => T.adj_comm x y

omit [Fintype V] [DecidableEq V] in
private theorem positive_split (X : Finset V) (f : V → ℕ) (pos : ∀ v, 0 < f v) :
    (∑ v ∈ X, (f v-1)) + X.card = ∑ v ∈ X, f v := by
  calc
    _ = (∑ v ∈ X, (f v-1)) + ∑ _ ∈ X, 1 := by simp
    _ = ∑ v ∈ X, (f v-1+1) := sum_add_distrib.symm
    _ = _ := sum_congr rfl fun v _ => Nat.sub_add_cancel (pos v)

omit [Fintype V] [DecidableEq V] in
private theorem dom_pos {D : Finset V} (hd : TotallyDominates T D) (v : V) : 0 < withinDegree T D v := by
  obtain ⟨y,hy,ha⟩ := hd v
  exact card_pos.mpr ⟨y,mem_filter.mpr ⟨hy,ha⟩⟩

/-- Exact slack identity for every total dominating set of a finite tree. -/
theorem domination_excess_identity (ht : T.IsTree) {D : Finset V} (hd : TotallyDominates T D) :
    (∑ v ∈ Dᶜ, (T.degree v-1)) + (∑ v, (withinDegree T D v-1)) + 2 = D.card := by
  have full (v : V) : withinDegree T univ v = T.degree v := by
    rw [withinDegree,← T.neighborFinset_eq_filter,card_neighborFinset_eq_degree]
  have mult := positive_split univ (withinDegree T D) (dom_pos T hd)
  rw [card_univ,incidence_swap] at mult
  simp_rw [full] at mult
  have pos (v : V) : 0 < T.degree v := by
    obtain ⟨y,_,ha⟩ := hd v; exact (T.degree_pos_iff_exists_adj v).mpr ⟨y,ha⟩
  have out := positive_split Dᶜ (fun v => T.degree v) pos
  have cut := D.sum_add_sum_compl (fun v => T.degree v)
  rw [T.sum_degrees_eq_twice_card_edges] at cut
  change (∑ v ∈ Dᶜ, (T.degree v-1)) + Dᶜ.card = ∑ v ∈ Dᶜ, T.degree v at out
  change (∑ v ∈ D, T.degree v) + (∑ v ∈ Dᶜ, T.degree v) = 2*T.edgeFinset.card at cut
  have := card_add_card_compl D
  have := ht.card_edgeFinset
  omega

omit [Fintype V] in
private theorem selected_cost {D I : Finset V} (hd : TotallyDominates T D) (hi : T.IsIndepSet (I : Set V)) :
    (I ∩ D).card ≤ (∑ y ∈ D \ I, (withinDegree T D y-1)) + (D \ I).card := by
  rw [positive_split _ _ (dom_pos T hd)]
  calc
    _ = ∑ _ ∈ I ∩ D, 1 := by simp
    _ ≤ ∑ i ∈ I ∩ D, withinDegree T (D \ I) i := by
      apply sum_le_sum; intro i h
      obtain ⟨y,hy,ha⟩ := hd i
      exact card_pos.mpr ⟨y,mem_filter.mpr ⟨mem_sdiff.mpr ⟨hy,fun h' => hi (mem_inter.mp h).1 h' ha.ne ha⟩,ha⟩⟩
    _ = _ := incidence_swap T _ _
    _ ≤ ∑ y ∈ D \ I, withinDegree T D y := by
      apply sum_le_sum; intro y _
      exact card_le_card (filter_subset_filter _ inter_subset_right)

/-- Omitting any member of an independent set whose omitted vertices all
have degree at least three requires two additional total dominators. -/
theorem two_extra_of_omitted {I D : Finset V} (ht : T.IsTree) (hd : TotallyDominates T D)
    (hi : T.IsIndepSet (I : Set V)) (om : (I \ D).Nonempty)
    (high : ∀ x ∈ I \ D, 3 ≤ T.degree x) : I.card + 2 ≤ D.card := by
  let A := I \ D
  let K := D \ I
  let f (v : V) := T.degree v-1
  let g (v : V) := withinDegree T D v-1
  have sub : A ⊆ Dᶜ := fun _ h => mem_compl.mpr (mem_sdiff.mp h).2
  have count : 2*A.card ≤ ∑ v ∈ A, f v := by
    calc _ = ∑ _ ∈ A, 2 := by simp [Nat.mul_comm]
         _ ≤ _ := sum_le_sum fun v hv => by have := high v hv; dsimp [f]; omega
  have left := sum_le_sum_of_subset_of_nonneg (f := f) sub (fun _ _ _ => Nat.zero_le _)
  have right := sum_le_sum_of_subset_of_nonneg (f := g) (subset_univ K) (fun _ _ _ => Nat.zero_le _)
  have strict : (∑ v ∈ A, f v) + (∑ v ∈ K, g v) < (∑ v ∈ Dᶜ, f v) + ∑ v, g v := by
    obtain ⟨x,hx⟩ := om
    obtain ⟨hxI,hxD⟩ := mem_sdiff.mp hx
    by_cases b : ∃ z ∉ D, T.Adj x z
    · obtain ⟨z,hz,ha⟩ := b
      have zi : z ∉ I := fun h => hi hxI h ha.ne ha
      have za : z ∉ A := fun h => zi (mem_sdiff.mp h).1
      have more := sum_le_sum_of_subset_of_nonneg (f := f)
        (show insert z A ⊆ Dᶜ from insert_subset (mem_compl.mpr hz) sub) (fun _ _ _ => Nat.zero_le _)
      rw [sum_insert za] at more
      have ne : T.degree z ≠ 1 := fun ez => hxD (support_forced T hd ((support_iff_pendant T).mpr ⟨z,ez,ha⟩))
      have pos := (T.degree_pos_iff_exists_adj z).mpr ⟨x,ha.symm⟩
      have : 0 < f z := by dsimp [f]; omega
      omega
    · have eq : D.filter (T.Adj x) = T.neighborFinset x := by
        ext z; rw [mem_filter,mem_neighborFinset]
        exact ⟨And.right,fun ha => ⟨Classical.byContradiction (fun h => b ⟨z,h,ha⟩),ha⟩⟩
      have hdg : withinDegree T D x = T.degree x := by rw [withinDegree,eq,card_neighborFinset_eq_degree]
      have ga : 0 < g x := by dsimp [g]; rw [hdg]; have := high x hx; omega
      have xk : x ∉ K := fun h => hxD (mem_sdiff.mp h).1
      have more := sum_le_sum_of_subset_of_nonneg (f := g) (subset_univ (insert x K)) (fun _ _ _ => Nat.zero_le _)
      rw [sum_insert xk] at more
      omega
  have eq := domination_excess_identity T ht hd
  have sel := selected_cost T hd hi
  change (∑ v ∈ Dᶜ, f v) + (∑ v, g v) + 2 = D.card at eq
  change (I ∩ D).card ≤ (∑ v ∈ K, g v)+K.card at sel
  have iPart : A.card+(I ∩ D).card = I.card := card_sdiff_add_card_inter I D
  have dPart : K.card+(I ∩ D).card = D.card := by rw [inter_comm]; exact card_sdiff_add_card_inter D I
  omega

/-- The only possible shortfall from `|I|+2`, where `I` consists of the
isolated maximum-degree vertices, is a star of equal maximum-degree branches. -/
theorem isolated_max_dichotomy (ht : T.IsTree) (hn : 2 < Fintype.card V) :
    (isolatedMaxVertices T).card+2 ≤ totalDominationNumber T ∨
      ∃ r, MaxLeafStar T (isolatedMaxVertices T) r ∧ totalDominationNumber T = (isolatedMaxVertices T).card+1 := by
  classical
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  let I := isolatedMaxVertices T
  obtain ⟨D,hd,hm⟩ := exists_min_total_set ht.isConnected
  have maxDeg {i : V} (h : i ∈ I) : T.degree i = T.maxDegree := mem_maxVertices.mp (mem_filter.mp h).1
  have avoids {i y : V} (h : i ∈ I) (ha : T.Adj i y) : y ∉ maxVertices T := fun hy => (mem_filter.mp h).2 y hy ha
  have independent : T.IsIndepSet (I : Set V) := fun _ hi _ hy _ ha => avoids hi ha (mem_filter.mp hy).1
  have high (x : V) (hx : x ∈ I \ D) : 3 ≤ T.degree x := by
    obtain ⟨hi,hout⟩ := mem_sdiff.mp hx
    obtain ⟨y,_,ha⟩ := hd x
    have lt : T.degree y < T.maxDegree := lt_of_le_of_ne (T.degree_le_maxDegree _) (fun e => avoids hi ha (mem_maxVertices.mpr e))
    have ne : T.degree y ≠ 1 := fun e => hout (support_forced T hd ((support_iff_pendant T).mpr ⟨y,e,ha⟩))
    have pos := (T.degree_pos_iff_exists_adj y).mpr ⟨x,ha.symm⟩
    rw [maxDeg hi]; omega
  by_cases big : I.card+2 ≤ D.card
  · exact Or.inl (big.trans_eq hm)
  right
  have forced : I ⊆ D := by
    intro x hx; by_contra h
    exact big (two_extra_of_omitted T ht hd independent ⟨x,mem_sdiff.mpr ⟨hx,h⟩⟩ high)
  have htwo := two_le_totalDominationNumber ht.isConnected
  have hI : I.Nonempty := card_pos.mp (by omega)
  obtain ⟨i,hi⟩ := hI
  obtain ⟨x,hx,ex⟩ := hd i
  have hxK : x ∈ D \ I := mem_sdiff.mpr ⟨hx,fun h => independent hi h ex.ne ex⟩
  have hKpos := card_pos.mpr ⟨x,hxK⟩
  have cut := card_sdiff_add_card_eq_card forced
  obtain ⟨r,hr⟩ := card_eq_one.mp (show (D \ I).card = 1 by omega)
  have split {x} (hx : x ∈ D) : x ∈ I ∨ x = r := by
    by_cases h : x ∈ I
    · exact Or.inl h
    · exact Or.inr (mem_singleton.mp (hr ▸ mem_sdiff.mpr ⟨hx,h⟩))
  have hrK : r ∈ D \ I := hr ▸ mem_singleton_self _
  have around (i : V) (hi : i ∈ I) : T.Adj r i := by
    obtain ⟨y,hy,ha⟩ := hd i
    rcases split hy with h | rfl
    · exact False.elim (independent hi h ha.ne ha)
    · exact ha.symm
  have kcard : (D \ I).card = 1 := by rw [hr,card_singleton]
  have sel := selected_cost T hd independent
  rw [inter_eq_left.mpr forced,kcard] at sel
  have spent := sum_le_sum_of_subset_of_nonneg (f := fun v => withinDegree T D v-1)
    (subset_univ (D \ I)) (fun _ _ _ => Nat.zero_le _)
  change (∑ v ∈ D \ I, (withinDegree T D v-1)) ≤ ∑ v, (withinDegree T D v-1) at spent
  have eq := domination_excess_identity T ht hd
  have zero : (∑ v ∈ Dᶜ, (T.degree v-1)) = 0 := by omega
  refine ⟨r,⟨(mem_sdiff.mp hrK).2,⟨i,hi⟩,around,fun _ h => maxDeg h,?_,?_⟩,by change totalDominationNumber T=I.card+1; omega⟩
  · exact lt_of_le_of_ne (T.degree_le_maxDegree _) (fun e => avoids hi (around i hi).symm (mem_maxVertices.mpr e))
  · intro v hv ne
    have hnot : v ∉ D := fun h => (split h).elim hv ne
    have one := single_le_sum (f := fun w => T.degree w-1) (fun _ _ => Nat.zero_le _) (mem_compl.mpr hnot)
    change T.degree v-1 ≤ ∑ y ∈ Dᶜ, (T.degree y-1) at one
    have pos := degree_pos_of_connected ht.isConnected v
    omega

end Graffiti
