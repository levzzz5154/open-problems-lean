import Graffiti.PeripheralTripod
import Graffiti365
import Mathlib.Algebra.BigOperators.Fin

namespace Graffiti.PeripheralTripod
open Finset SimpleGraph SupportCounting
open scoped Classical

variable {m N : ℕ}

private abbrev atStem (a : Fin 3) (i : ℕ) (h : i < 5 * blocks m a + 1) : Vertex m N :=
  stem ⟨a, ⟨i,h⟩⟩

private theorem stepAdj {a : Fin 3} {i : ℕ} (h : i+1 < 5 * blocks m a + 1) :
    (tree m N).Adj (atStem a i (by omega)) (atStem a (i+1) h) := by
  refine ⟨fun eq => ?_, Or.inr ?_⟩
  · have e := congrArg depth eq
    change i+1 = i+1+1 at e
    omega
  · simp [atStem, parent]

private theorem firstAdj (a : Fin 3) : (tree m N).Adj root (atStem a 0 (by omega)) :=
  ⟨by simp [atStem], Or.inr (by simp [atStem,parent])⟩

private theorem leafParent {x : Vertex m N} (h : ∀ y, parent y ≠ x) :
    ∀ y, (tree m N).Adj x y ↔ parent x = y := by
  intro y
  exact ⟨fun e => e.2.resolve_right (h y), fun e => ⟨fun eq => h x (e.trans eq.symm), Or.inl e⟩⟩

private theorem notChildLeaf (x : Vertex m N) :
    (∀ z : Marked m, parent x ≠ sprout z) ∧ (∀ j : Fin N, parent x ≠ bunch j) := by
  rcases x with ((_|⟨a,i⟩)|z)|j <;> simp [parent]
  split <;> simp

private theorem sproutAdj (z : Marked m) (y : Vertex m N) :
    (tree m N).Adj (sprout z) y ↔ stem z.val = y :=
  leafParent (fun x => (notChildLeaf x).1 z) y

private theorem sproutDegree (z : Marked m) : (tree m N).degree (sprout z) = 1 := by
  have e : (tree m N).neighborFinset (sprout z) = {stem z.val} := by
    ext y
    simp only [mem_neighborFinset, sproutAdj, mem_singleton, eq_comm]
  rw [← card_neighborFinset_eq_degree,e,card_singleton]

private theorem stemNonleaf (a : Fin 3) (i : Fin (5 * blocks m a + 1)) :
    (tree m N).degree (atStem a i i.isLt) ≠ 1 := by
  let x : Vertex m N := atStem a i i.isLt
  have hd := parent_depth x (by simp [x,atStem])
  have hp : (tree m N).Adj x (parent x) := ⟨fun eq => by rw [← eq] at hd; omega, Or.inl rfl⟩
  intro hl
  by_cases h : i.val+1 < 5 * blocks m a + 1
  · have e := unique_neighbor_at_leaf _ hl hp (stepAdj h)
    have d := congrArg depth e
    change depth (parent x) = i.val+1+1 at d
    change depth (parent x)+1 = i.val+1 at hd
    omega
  · have hm : MarkedAt i.val := Or.inl (by have := i.isLt; omega)
    let z : Marked m := ⟨⟨a,i⟩,hm⟩
    have e := unique_neighbor_at_leaf _ hl hp ((sproutAdj z x).mpr rfl).symm
    have d := congrArg depth e
    change depth (parent x) = i.val+2 at d
    change depth (parent x)+1 = i.val+1 at hd
    omega

private theorem supportShape {y : Vertex m N} (hy : y ∈ supportVertices (tree m N)) :
    ∃ z : Marked m, stem z.val = y := by
  obtain ⟨l,hl,e⟩ := (support_iff_pendant _).mp hy
  rcases l with ((_|⟨a,i⟩)|z)|j
  · have bad := congrArg arm (unique_neighbor_at_leaf _ hl (firstAdj 0) (firstAdj 1))
    exact False.elim ((by decide : (some (0 : Fin 3)) ≠ some 1) bad)
  · exact False.elim (stemNonleaf a i hl)
  · exact ⟨z,(sproutAdj z y).mp e.symm⟩
  · exact ⟨⟨lastSeg m 2,Or.inl (by simp [lastSeg])⟩,
      (leafParent (fun x => (notChildLeaf x).2 j) y).mp e.symm⟩

private theorem markIsolated (z : Marked m) : stem z.val ∈ isolatedSupports (tree m N) := by
  refine mem_filter.mpr ⟨(support_iff_pendant _).mpr ⟨sprout z,sproutDegree z,((sproutAdj z _).mpr rfl).symm⟩,?_⟩
  apply card_eq_zero.mpr
  apply not_nonempty_iff_eq_empty.mp
  rintro ⟨y,hy⟩
  obtain ⟨hs,e⟩ := mem_filter.mp hy
  obtain ⟨w,rfl⟩ := supportShape hs
  have d : depth (stem (N := N) z.val) + 1 = depth (stem (N := N) w.val) ∨
      depth (stem (N := N) w.val) + 1 = depth (stem (N := N) z.val) := by
    rcases e.2 with h|h
    · exact Or.inr (h ▸ parent_depth (stem (N := N) z.val) (by simp))
    · exact Or.inl (h ▸ parent_depth (stem (N := N) w.val) (by simp))
  change z.val.2.val+1+1 = w.val.2.val+1 ∨ w.val.2.val+1+1 = z.val.2.val+1 at d
  have hz := z.property
  have hw := w.property
  unfold MarkedAt at hz hw
  omega

private abbrev Slot (m : ℕ) := (a : Fin 3) × Fin (blocks m a)
private def relay (s : Slot m) : Vertex m N :=
  atStem s.1 (5*s.2.val+4) (by have := s.2.isLt; omega)

set_option maxHeartbeats 800000 in
/-- The marked stems and one relay per five-edge block, plus the root, suffice. -/
theorem relay_cost (m N : ℕ) : totalDominationNumber (tree m N) ≤
    (isolatedSupports (tree m N)).card + (3*m+3) := by
  classical
  let R := insert (root (m := m) (N := N)) (univ.image (@relay m N))
  let D := isolatedSupports (tree m N) ∪ R
  have rootIn : root ∈ D := mem_union_right _ (mem_insert_self ..)
  have markIn (a : Fin 3) (i : ℕ) (hi : i < 5 * blocks m a + 1) (hm : MarkedAt i) :
      atStem a i hi ∈ D := mem_union_left _ (markIsolated ⟨⟨a,⟨i,hi⟩⟩,hm⟩)
  have relayIn (a : Fin 3) (i : ℕ) (hi : i < 5 * blocks m a + 1) (hr : i%5 = 4) :
      atStem a i hi ∈ D := by
    apply mem_union_right
    apply mem_insert_of_mem
    refine mem_image.mpr ⟨⟨a,⟨i/5,by omega⟩⟩,mem_univ _,?_⟩
    simp only [relay,atStem,stem,Sum.inl.injEq,Option.some.injEq]
    congr 2
    omega
  have dom : TotallyDominates (tree m N) D := by
    intro v
    rcases v with ((_|⟨a,i⟩)|z)|j
    · exact ⟨_,markIn 0 0 (by omega) (Or.inl rfl),firstAdj 0⟩
    · have hi := i.isLt
      by_cases hz : i.val = 0
      · exact ⟨_,rootIn,⟨by simp, Or.inl (by simp [parent,hz])⟩⟩
      by_cases hm : i.val%5 = 2 ∨ i.val%5 = 3
      · have h : i.val+1 < 5 * blocks m a + 1 := by omega
        refine ⟨_,?_,stepAdj h⟩
        rcases hm with h|h
        · exact markIn _ _ _ (Or.inr (by omega))
        · exact relayIn _ _ _ (by omega)
      · let k := i.val-1
        have hk : k+1 = i.val := by dsimp [k]; omega
        have e := stepAdj (m := m) (a := a) (N := N) (i := k) (by omega)
        have eq : (⟨k+1,by omega⟩ : Fin (5 * blocks m a + 1)) = i := Fin.ext hk
        change (tree m N).Adj _ (stem ⟨a,⟨k+1,_⟩⟩) at e
        rw [eq] at e
        refine ⟨_,?_,e.symm⟩
        by_cases h : k%5 = 4
        · exact relayIn _ _ _ h
        · exact markIn _ _ _ (by unfold MarkedAt; omega)
    · exact ⟨_,mem_union_left _ (markIsolated z),(sproutAdj z _).mpr rfl⟩
    · exact ⟨_,markIn 2 _ _ (Or.inl (by simp [lastSeg])),⟨by simp,Or.inl rfl⟩⟩
  have n : Fintype.card (Slot m) = 3*m+2 := by
    simp [Slot,Fintype.card_sigma,Fin.sum_univ_succ,blocks]
    omega
  have r : R.card ≤ 3*m+3 := by
    have a := card_insert_le (root (m := m) (N := N)) (univ.image (@relay m N))
    have b := card_image_le (s := (univ : Finset (Slot m))) (f := @relay m N)
    rw [card_univ,n] at b
    dsimp only [R]; omega
  exact (show totalDominationNumber (tree m N) ≤ D.card from Nat.sInf_le ⟨D,dom,rfl⟩).trans
    ((card_union_le ..).trans (Nat.add_le_add_left r _))

end Graffiti.PeripheralTripod
