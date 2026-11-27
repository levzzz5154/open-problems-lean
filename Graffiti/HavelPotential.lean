import Graffiti.FirstZeroStats

namespace Graffiti.FirstZero

/-- Each selected two disappears from the nonleaf statistics. Larger selected
entries remain nonleaves and lose one unit of weight instead of two. -/
private theorem selected_stats (u : List ℕ) (h : ∀ a ∈ u, 2 ≤ a) :
    nonleafCount u = u.length ∧ nonleafCount (u.map Nat.pred) = branchCount u ∧
    branchCount (u.map Nat.pred) ≤ branchCount u ∧ branchCount u ≤ u.length ∧
    nonleafWeight (u.map Nat.pred) + 2 * u.length ≤ nonleafWeight u + branchCount u := by
  induction u with
  | nil => simp [nonleafCount, branchCount, nonleafWeight]
  | cons a u ih =>
    have ha := h a (by simp)
    obtain ⟨hn, hm, hb, hl, hw⟩ := ih (fun x hx => h x (by simp [hx]))
    match a with
    | 0 | 1 => omega
    | 2 | 3 | n + 4 =>
      simp [nonleafCount, branchCount, nonleafWeight, Nat.pred] at hn hm hb hl hw ⊢
      exact ⟨hn, hm, by omega, by omega, by omega⟩

private theorem branch_zero (u : List ℕ) (h : ∀ a ∈ u, a ≤ 2) : branchCount u = 0 := by
  induction u with
  | nil => rfl
  | cons a u ih =>
    have ha := h a (by simp)
    have hu := ih (fun x hx => h x (by simp [hx]))
    simpa [branchCount, Nat.not_lt.mpr ha] using hu

theorem safe_step {ds : List ℕ} (hs : ds.Pairwise (· ≥ ·)) (hl : 2 ≤ ds.count 1)
    (safe : 0 ∉ step ds) : (step ds).Pairwise (· ≥ ·) ∧ 2 ≤ (step ds).count 1 ∧
    nonleafWeight (step ds) + 6 ≤ nonleafWeight ds ∧ branchBudget (step ds) + 3 ≤ branchBudget ds := by
  cases ds with
  | nil => simp at hl
  | cons d xs =>
    let u := xs.take d
    let w := xs.drop d
    have splitxs : u ++ w = xs := List.take_append_drop ..
    have p : (step (d :: xs)).Perm (u.map Nat.pred ++ w) := List.perm_insertionSort _ _
    have lower : ∀ a ∈ u, 2 ≤ a := by
      intro a ha
      by_contra! h
      have hp : a.pred = 0 := by rw [Nat.pred_eq_sub_one]; omega
      apply safe
      apply p.mem_iff.mpr
      exact List.mem_append_left _ (hp ▸ List.mem_map_of_mem ha : (0 : ℕ) ∈ u.map Nat.pred)
    have upper : ∀ a ∈ u, a ≤ d := fun a ha => (List.pairwise_cons.mp hs).1 a (List.take_subset d xs ha)
    have one : 1 ∈ xs := by
      apply List.count_pos_iff.mp
      rw [List.count_cons] at hl
      split at hl <;> omega
    have len : u.length = d := by
      by_cases h : d ≤ xs.length
      · exact List.length_take.trans (Nat.min_eq_left h)
      · have eq := List.take_of_length_le (show xs.length ≤ d by omega)
        have bad := lower 1 (show 1 ∈ u by simpa only [u, eq] using one)
        omega
    have hdpos := (List.pairwise_cons.mp hs).1 1 one
    obtain ⟨a, ha⟩ := List.length_pos_iff_exists_mem.mp (show 0 < u.length by omega)
    have hd : 2 ≤ d := (lower a ha).trans (upper a ha)
    have u1 : u.count 1 = 0 := List.count_eq_zero.mpr (fun hm => by have := lower 1 hm; omega)
    have leaves : 2 ≤ w.count 1 := by
      rw [List.count_cons_of_ne (by omega : d ≠ 1), ← splitxs, List.count_append, u1] at hl
      omega
    refine ⟨List.sorted_insertionSort _ _, ?_, ?_⟩
    · rw [p.count_eq, List.count_append]; omega
    obtain ⟨hn, hm, hb, hl', hw⟩ := selected_stats u lower
    have wn : nonleafCount (step (d :: xs)) = nonleafCount (u.map Nat.pred) + nonleafCount w := by
      simpa [nonleafCount] using (p.filter (fun a => decide (1 < a))).length_eq
    have wb : branchCount (step (d :: xs)) = branchCount (u.map Nat.pred) + branchCount w := by
      simpa [branchCount] using (p.filter (fun a => decide (2 < a))).length_eq
    have ww : nonleafWeight (step (d :: xs)) = nonleafWeight (u.map Nat.pred) + nonleafWeight w := by
      simpa [nonleafWeight] using (p.filter (fun a => decide (1 < a))).sum_eq
    have nx : nonleafCount (d :: xs) = nonleafCount u + nonleafCount w + 1 := by
      rw [← splitxs]; simp [nonleafCount, show 1 < d by omega]
    have wx : nonleafWeight (d :: xs) = d + (nonleafWeight u + nonleafWeight w) := by
      rw [← splitxs]; simp [nonleafWeight, show 1 < d by omega]
    unfold branchBudget
    by_cases h2 : d = 2
    · have bu := branch_zero u (h2 ▸ upper)
      have bx : branchCount (d :: xs) = branchCount u + branchCount w := by
        rw [← splitxs]; simp [branchCount, h2]
      constructor <;> omega
    · have bx : branchCount (d :: xs) = branchCount u + branchCount w + 1 := by
        rw [← splitxs]; simp [branchCount, show 2 < d by omega]
      constructor <;> omega

end Graffiti.FirstZero
