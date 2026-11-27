import DivisorAdj.Basic

/-! Consecutive elements of an ordered finite set, indexed by either endpoint. -/

namespace DivisorAdj

open Finset

def steps (s : Finset ℕ) : Finset (ℕ × ℕ) :=
  (s ×ˢ s).filter fun e => e.1 < e.2 ∧ ∀ z ∈ s, z ≤ e.1 ∨ e.2 ≤ z

theorem mem_steps {s : Finset ℕ} {x y : ℕ} : (x,y) ∈ steps s ↔
    x ∈ s ∧ y ∈ s ∧ x < y ∧ ∀ z ∈ s, z ≤ x ∨ y ≤ z := by
  simp only [steps, mem_filter, mem_product, and_assoc]

def weight (e : ℕ × ℕ) : ℚ := 1 / ((e.1 : ℚ) * e.2)

private theorem steps_insert_min {s : Finset ℕ} {x y : ℕ} (hy : y ∈ s)
    (hxy : x < y) (hl : ∀ z ∈ s, y ≤ z) :
    steps (insert x s) = insert (x,y) (steps s) := by
  ext ⟨a,b⟩
  rw [mem_steps, show ((a,b) ∈ insert (x,y) (steps s)) ↔ (a,b) = (x,y) ∨ (a,b) ∈ steps s from mem_insert]
  constructor
  · rintro ⟨ha,hb,hab,hgap⟩
    have hxb : x < b := by
      rcases mem_insert.mp ha with rfl | ha
      · exact hab
      · exact (hxy.trans_le (hl a ha)).trans hab
    have hbs := (mem_insert.mp hb).resolve_left hxb.ne'
    rcases mem_insert.mp ha with rfl | ha
    · left
      have hby := (hgap y (mem_insert_of_mem hy)).resolve_left (not_le_of_gt hxy)
      simp [le_antisymm hby (hl b hbs)]
    · exact Or.inr (mem_steps.mpr ⟨ha,hbs,hab,fun z hz => hgap z (mem_insert_of_mem hz)⟩)
  · rintro (e|h)
    · cases e
      exact ⟨mem_insert_self _ _,mem_insert_of_mem hy,hxy,fun z hz =>
        (mem_insert.mp hz).elim (fun ez => Or.inl (le_of_eq ez)) (fun hz' => Or.inr (hl z hz'))⟩
    · obtain ⟨ha,hb,hab,hgap⟩ := mem_steps.mp h
      refine ⟨mem_insert_of_mem ha,mem_insert_of_mem hb,hab,fun z hz => ?_⟩
      rcases mem_insert.mp hz with rfl | hz
      · exact Or.inl (hxy.le.trans (hl a ha))
      · exact hgap z hz

theorem recipSum_steps : ∀ l : List ℕ, l.Sorted (· < ·) →
    recipSum l = ∑ e ∈ steps l.toFinset, weight e
  | [], _ => by simp [recipSum,steps]
  | [x], _ => by
    have he : steps {x} = ∅ := by
      apply eq_empty_of_forall_not_mem
      rintro ⟨a,b⟩ h
      obtain ⟨ha,hb,hab,_⟩ := mem_steps.mp h
      simp only [mem_singleton] at ha hb
      omega
    simp [recipSum,he]
  | x :: y :: t, hs => by
    have ht := (List.sorted_cons.mp hs).2
    have hxy := List.rel_of_pairwise_cons hs (List.mem_cons_self : y ∈ y :: t)
    let s := (y :: t).toFinset
    have hy : y ∈ s := List.mem_toFinset.mpr List.mem_cons_self
    have hl : ∀ z ∈ s, y ≤ z := by
      intro z hz
      rcases List.mem_cons.mp (List.mem_toFinset.mp hz) with rfl | hz
      · exact le_rfl
      · exact (List.rel_of_pairwise_cons ht hz).le
    have hn : (x,y) ∉ steps s := fun h => (not_le_of_gt hxy) (hl x (mem_steps.mp h).1)
    rw [recipSum, List.toFinset_cons, steps_insert_min hy hxy hl, sum_insert hn,
      recipSum_steps (y :: t) ht]
    rfl

theorem divisor_steps (n : ℕ) : recipSum (divs n) = ∑ e ∈ steps n.divisors, weight e := by
  simpa [divs] using recipSum_steps (divs n) (sort_sorted_lt _)

theorem same_step_of_end {s : Finset ℕ} {a b c d : ℕ} (h : (a,b) ∈ steps s)
    (j : (c,d) ∈ steps s) (e : b = d) : (a,b) = (c,d) := by
  subst d
  obtain ⟨ha,_,hab,hgap⟩ := mem_steps.mp h
  obtain ⟨hc,_,hcb,jgap⟩ := mem_steps.mp j
  rw [le_antisymm ((jgap a ha).resolve_right (not_le_of_gt hab)) ((hgap c hc).resolve_right (not_le_of_gt hcb))]

theorem exists_step_before {s : Finset ℕ} {y z : ℕ} (hy : y ∈ s) (hz : z ∈ s) (hzy : z < y) :
    ∃ x, (x,y) ∈ steps s := by
  let A := s.filter (· < y)
  have hn : A.Nonempty := ⟨z,mem_filter.mpr ⟨hz,hzy⟩⟩
  have hx := mem_filter.mp (A.max'_mem hn)
  refine ⟨_,mem_steps.mpr ⟨hx.1,hy,hx.2,fun t ht => ?_⟩⟩
  by_cases he : t < y
  · exact Or.inl (A.le_max' t (mem_filter.mpr ⟨ht,he⟩))
  · exact Or.inr (Nat.le_of_not_gt he)

theorem exists_step_after {s : Finset ℕ} {x z : ℕ} (hx : x ∈ s) (hz : z ∈ s) (hxz : x < z) :
    ∃ y, (x,y) ∈ steps s := by
  let A := s.filter (x < ·)
  have hn : A.Nonempty := ⟨z,mem_filter.mpr ⟨hz,hxz⟩⟩
  have hy := mem_filter.mp (A.min'_mem hn)
  refine ⟨_,mem_steps.mpr ⟨hx,hy.1,hy.2,fun t ht => ?_⟩⟩
  by_cases he : x < t
  · exact Or.inr (A.min'_le t (mem_filter.mpr ⟨ht,he⟩))
  · exact Or.inl (Nat.le_of_not_gt he)

end DivisorAdj
