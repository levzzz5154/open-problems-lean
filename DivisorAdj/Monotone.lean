import DivisorAdj.Value

namespace DivisorAdj

/-- The contribution contributed by prefixing `x` to the list. -/
private def firstEdge (x : ℕ) : List ℕ → ℚ
  | [] => 0
  | y :: _ => 1 / ((x : ℚ) * y)

private theorem recipSum_cons (x : ℕ) (l : List ℕ) :
    recipSum (x :: l) = firstEdge x l + recipSum l := by
  cases l <;> simp [recipSum, firstEdge]

private theorem firstEdge_nonneg (x : ℕ) (l : List ℕ) : 0 ≤ firstEdge x l := by
  cases l <;> simp only [firstEdge] <;> positivity

/-- After a retained divisor, the next divisor of the longer list occurs no later
than the next retained divisor. Its edge alone pays for the old edge. -/
private theorem firstEdge_le {x : ℕ} {s t : List ℕ} (hx : 0 < x) (h : s.Sublist t)
    (hs : t.Sorted (· < ·)) (hp : ∀ y ∈ t, 0 < y) : firstEdge x s ≤ firstEdge x t := by
  cases s with
  | nil => exact firstEdge_nonneg _ _
  | cons a s =>
    have ha := h.subset (List.mem_cons_self : a ∈ a :: s)
    cases t with
    | nil => simp at ha
    | cons b t =>
      have hb := hp b List.mem_cons_self
      have hba : b ≤ a := by
        rcases List.mem_cons.mp ha with rfl | ha
        · exact le_rfl
        · exact (List.rel_of_pairwise_cons hs ha).le
      apply one_div_le_one_div_of_le (show 0 < (x : ℚ) * b by positivity)
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hba) (by positivity)

theorem recipSum_le_sublist {s t : List ℕ} (h : s.Sublist t)
    (hs : t.Sorted (· < ·)) (hp : ∀ y ∈ t, 0 < y) : recipSum s ≤ recipSum t := by
  induction h with
  | slnil => exact le_rfl
  | @cons s t x h ih =>
    rw [recipSum_cons]
    exact (ih (List.sorted_cons.mp hs).2 (fun y hy => hp y (.tail _ hy))).trans
      (le_add_of_nonneg_left (firstEdge_nonneg _ _))
  | @cons₂ s t x h ih =>
    have ht := (List.sorted_cons.mp hs).2
    have hpos : ∀ y ∈ t, 0 < y := fun y hy => hp y (.tail _ hy)
    rw [recipSum_cons, recipSum_cons x t]
    exact add_le_add (firstEdge_le (hp x List.mem_cons_self) h ht hpos) (ih ht hpos)

theorem recipSum_le_divs {s : List ℕ} {n : ℕ} (hs : s.Sorted (· < ·))
    (h : s ⊆ divs n) : recipSum s ≤ recipSum (divs n) := by
  have ht := Finset.sort_sorted_lt n.divisors
  exact recipSum_le_sublist (List.sublist_of_subperm_of_sorted
    (List.subperm_of_subset hs.nodup h) hs ht) ht
    (fun _ hy => Nat.pos_of_mem_divisors ((Finset.mem_sort (· ≤ ·)).mp hy))

/-- Including all divisors of `m` in the ordered divisor list of `n` can only
increase the sum of reciprocal adjacent products. -/
theorem recipSum_mono_dvd {m n : ℕ} (hn : 0 < n) (h : m ∣ n) :
    recipSum (divs m) ≤ recipSum (divs n) := by
  apply recipSum_le_divs (Finset.sort_sorted_lt _)
  intro y hy
  exact (Finset.mem_sort (· ≤ ·)).mpr (Nat.divisors_subset_of_dvd hn.ne' h
    ((Finset.mem_sort (· ≤ ·)).mp hy))

/-- The sequence is antitone along divisibility, away from its degenerate indices. -/
theorem a_antitone_dvd {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) (h : m ∣ n) : a n ≤ a m := by
  have hn0 : 0 < n := by omega
  have hm0 : 0 < m := by omega
  have H : (a n : ℚ) * prodSum (divs n) ≤ (n : ℚ)^2 := by
    exact_mod_cast Nat.div_mul_le_self (n^2) (prodSum (divs n))
  rw [ratio_identity hn0] at H
  have hr : (a n : ℚ) * recipSum (divs n) ≤ 1 := by
    apply (mul_le_mul_left (show 0 < (n : ℚ)^2 by positivity)).mp
    simpa [mul_comm, mul_left_comm, mul_assoc] using H
  have hrm := (mul_le_mul_of_nonneg_left (recipSum_mono_dvd hn0 h)
    (show 0 ≤ (a n : ℚ) by positivity)).trans hr
  have Hm : (a n : ℚ) * prodSum (divs m) ≤ (m : ℚ)^2 := by
    rw [ratio_identity hm0]
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left hrm (show 0 ≤ (m : ℚ)^2 by positivity)
  apply (Nat.le_div_iff_mul_le (prodSum_pos hm)).mpr
  exact_mod_cast Hm

end DivisorAdj
