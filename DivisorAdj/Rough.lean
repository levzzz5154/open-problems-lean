import DivisorAdj.Value

namespace DivisorAdj
open Finset

private def small := (Ico 11 300).filter fun d : ℕ => d.Coprime 210

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem certificate : (1:ℚ)/11 + (∑ d ∈ small, 1 / (d:ℚ)^2) + 1/299 ≤ 1/8 := by
  decide +kernel

theorem rough_lower {n : ℕ} (hn : 2 ≤ n) (hc : n.Coprime 210) : 8 ≤ a n := by
  have hpos : 0 < n := by omega
  have h1 : 1 ∈ divs n := by simp [divs, hpos.ne']
  have hnmem : n ∈ divs n := by simp [divs, hpos.ne']
  have hd (d) (h : d ∈ divs n) := Nat.dvd_of_mem_divisors ((Finset.mem_sort (· ≤ ·)).mp h)
  have hs : (divs n).Sorted (· < ·) := Finset.sort_sorted_lt _
  obtain ⟨x,b,t,he⟩ : ∃ x b t, divs n = x::b::t := by
    cases he : divs n with
    | nil => simp [he] at h1
    | cons x t =>
      cases t with
      | nil => simp [he] at h1 hnmem; omega
      | cons b t => exact ⟨x,b,t,rfl⟩
  rw [he] at hs
  have xpos := Nat.pos_of_dvd_of_pos (hd x (he ▸ List.mem_cons_self)) hpos
  have low (d) (h : d ∈ b::t) : 11 ≤ d := by
    have hx := List.rel_of_pairwise_cons hs h
    have hcop := hc.coprime_dvd_left (hd d (he ▸ .tail _ h))
    by_contra! H
    have hh : 2 ≤ d := by omega
    interval_cases d <;> exact absurd hcop (by decide)
  have hsub : (b::t).toFinset ⊆ small ∪ Ico 300 (n+300) := by
    intro d hm
    have hm' := List.mem_toFinset.mp hm
    have hdn := hd d (he ▸ .tail _ hm')
    by_cases h : d < 300
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_Ico.mpr ⟨low d hm', h⟩, hc.coprime_dvd_left hdn⟩)
    · exact mem_union_right _ (mem_Ico.mpr ⟨by omega, by have := Nat.le_of_dvd hpos hdn; omega⟩)
  have hdis : Disjoint small (Ico 300 (n+300)) := by
    apply disjoint_left.mpr
    intro d h1 h2
    exact (Nat.not_lt_of_ge (mem_Ico.mp h2).1) (mem_Ico.mp (mem_filter.mp h1).1).2
  have H := recipSum_square_bound (b::t) (List.sorted_cons.mp hs).2 (fun d h => by have := low d h; omega)
  have Hu := sum_le_sum_of_subset_of_nonneg (f := fun d : ℕ => 1/(d:ℚ)^2) hsub (by intros; positivity)
  rw [sum_union hdis] at Hu
  have hb := low b List.mem_cons_self
  have first : 1/((x:ℚ)*b) ≤ 1/11 := by
    apply one_div_le_one_div_of_le (by norm_num)
    exact_mod_cast (show 11 ≤ x*b from hb.trans (by simpa using Nat.mul_le_mul_right b xpos))
  have bound : recipSum (divs n) ≤ 1/8 := by
    rw [he, recipSum]
    have ht : ∑ d ∈ Ico 300 (n+300), 1/(d:ℚ)^2 ≤ 1/299 - 1/((n:ℚ)+299) :=
      inverse_square_tail 299 n (by decide)
    linarith [certificate, show 0 ≤ 1/((n:ℚ)+299) by positivity]
  apply (Nat.le_div_iff_mul_le (prodSum_pos hn)).2
  suffices h : (8:ℚ) * prodSum (divs n) ≤ (n:ℚ)^2 by exact_mod_cast h
  rw [ratio_identity hpos]
  nlinarith [mul_le_mul_of_nonneg_left bound (sq_nonneg (n:ℚ))]

end DivisorAdj
