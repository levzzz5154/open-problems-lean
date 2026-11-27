import SelfBanning.Row
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat

namespace SelfBanning

/-- Any `c` consecutive time slots contain at most `k` values at least `c`.
At the last such time, all `c-k` smaller labels have distinct recent witnesses. -/
theorem window_quota {k : ℕ} {a : ℕ → ℕ} (h : IsRow k a) (u c : ℕ) (hc : k ≤ c) :
    ((Finset.Ico u (u+c)).filter (fun s => c ≤ a s)).card ≤ k := by
  classical
  let H := (Finset.Ico u (u+c)).filter (fun s => c ≤ a s)
  change H.card ≤ k
  by_cases hn : H.Nonempty
  · let t := H.max' hn
    have ht : t ∈ H := Finset.max'_mem H hn
    obtain ⟨htw,htv⟩ := Finset.mem_filter.mp ht
    have htu := Finset.mem_Ico.mp htw
    let W := Finset.Ico (t+1-c) (t+1)
    let L := W.filter (fun s => a s < c)
    have hH : H ⊆ W := by
      intro s hs
      have hst : s ≤ t := Finset.le_max' H s hs
      have hsu := Finset.mem_Ico.mp (Finset.mem_filter.mp hs).1
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    have hd : Disjoint H L := Finset.disjoint_left.mpr fun _ hh hl =>
      (not_lt_of_ge (Finset.mem_filter.mp hh).2) (Finset.mem_filter.mp hl).2
    have hU : H ∪ L ⊆ W := Finset.union_subset hH (Finset.filter_subset _ _)
    have hhit : Finset.Ico k c ⊆ L.image a := by
      intro v hv
      obtain ⟨hv₁,hv₂⟩ := Finset.mem_Ico.mp hv
      obtain ⟨s,hs,hb,he⟩ := h.skipped t v hv₁ (by omega)
      exact Finset.mem_image.mpr ⟨s, Finset.mem_filter.mpr
        ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, he ▸ hv₂⟩, he⟩
    have hlo := (Finset.card_le_card hhit).trans Finset.card_image_le
    have htotal := Finset.card_le_card hU
    rw [Finset.card_union_of_disjoint hd] at htotal
    simp only [W, Nat.card_Ico] at hlo htotal
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hn]

/-- A uniform linear bound. Otherwise the `2*k+1` labels `2*k,...,4*k`
must all occur in two windows that each admit only `k` of them. -/
theorem row_le_four_mul {k : ℕ} {a : ℕ → ℕ} (h : IsRow k a) (t : ℕ) : a t ≤ 4*k := by
  classical
  by_cases hz : k = 0
  · subst k
    have hh : a t = 0 := (minimum_iff h t).2 (one_dvd t)
    omega
  by_contra! hb
  let u := t-4*k
  let H (s : ℕ) := (Finset.Ico s (s+2*k)).filter (fun j => 2*k ≤ a j)
  have quota (s : ℕ) : (H s).card ≤ k := window_quota h _ _ (by omega)
  have hhit : Finset.Icc (2*k) (4*k) ⊆ (H u ∪ H (u+2*k)).image a := by
    intro v hv
    obtain ⟨hl,hr⟩ := Finset.mem_Icc.mp hv
    obtain ⟨s,hs,ht,he⟩ := h.skipped t v (by omega) (by omega)
    have hu : u ≤ s ∧ s < u+4*k := by dsimp [u]; omega
    refine Finset.mem_image.mpr ⟨s, Finset.mem_union.mpr ?_, he⟩
    by_cases hx : s<u+2*k
    · left; exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hu.1,hx⟩, by omega⟩
    · right; exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega,by omega⟩, by omega⟩
  have hl := ((Finset.card_le_card hhit).trans Finset.card_image_le).trans (Finset.card_union_le _ _)
  simp only [Nat.card_Icc] at hl
  have h₁ := quota u
  have h₂ := quota (u+2*k)
  omega

end SelfBanning
