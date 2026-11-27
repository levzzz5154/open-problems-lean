import EvenCover.Core

namespace EvenCover

/-- If `j` is omitted, an earlier chosen offset must match the pattern;
    there is no restriction from the prefix on a later offset. -/
private def Available (N j i : ℕ) : Prop :=
  (i < j ∧ (i = 0 ∨ i % 4 = 2 ∨ i = anchor N)) ∨ j < i

/-- One even sum with no decomposition avoiding `j` certifies necessity. -/
private theorem forceAt {N j t : ℕ} {S : ℕ → Prop}
    (hc : CoversOffsets N S) (hj : j ≤ N)
    (hprefix : ∀ i < j, S i → pattern N i) (ht : t ≤ N)
    (blocked : ∀ x y : ℕ, x ≤ N → y ≤ N → Available N j x →
      Available N j y → x + y = 2 * t → False) : S j := by
  by_contra hnot
  have restrict (i : ℕ) (hi : S i) : Available N j i := by
    have hne : i ≠ j := fun e => hnot (e ▸ hi)
    by_cases h : i < j
    · refine Or.inl ⟨h, ?_⟩
      rcases (hprefix i h hi).2 with hz | hr | ha | he
      · exact Or.inl hz
      · exact Or.inr (Or.inl hr)
      · exact Or.inr (Or.inr ha)
      · omega
    · exact Or.inr (by omega)
  obtain ⟨x, y, hx, hy, hsx, hsy, hxy⟩ := hc t ht
  exact blocked x y hx hy (restrict x hsx) (restrict y hsy) hxy

/-- No cover can omit a pattern offset without first adding an earlier
    offset that the pattern omits. -/
theorem pattern_forced {N j : ℕ} {S : ℕ → Prop} (hc : CoversOffsets N S)
    (hj : pattern N j) (hprefix : ∀ i < j, S i → pattern N i) : S j := by
  obtain ⟨hjN, hkind⟩ := hj
  by_cases hend : j = 0 ∨ j = N
  · obtain ⟨x, y, hx, hy, hsx, _, hsum⟩ := hc j hjN
    have he : x = j := by omega
    exact he ▸ hsx
  by_cases ha : j = anchor N
  · by_cases hlarge : 8 ≤ j
    · -- The auxiliary sum `j + 6` exceeds N. A summand above `j`
      -- leaves only 3, 4, or 5; two earlier positive summands sum to 0 mod 4.
      have shape : N ≤ j + 3 ∧ j % 4 = 0 := by
        unfold anchor at ha
        split at ha <;> omega
      have htarget : 2 * (j / 2 + 3) = j + 6 := by omega
      apply forceAt hc hjN hprefix (t := j / 2 + 3) (by omega)
      intro x y hx hy ax ay hsum
      rw [htarget] at hsum
      simp only [Available, ← ha] at ax ay
      omega
    · -- The only nonzero short anchors are 4 (N ≤ 5) and 5 (N = 6, 7).
      have shape : (j = 4 ∧ N ≤ 5) ∨ (j = 5 ∧ N ≤ 7) := by
        unfold anchor at ha
        split at ha <;> omega
      apply forceAt hc hjN hprefix (t := j) hjN
      intro x y hx hy ax ay hsum
      simp only [Available, ← ha] at ax ay
      omega
  · have hr : j % 4 = 2 := by omega
    by_cases late : anchor N < j ∧ ¬ (N = 6 ∨ N = 7)
    · -- The final recurring offset, past the regular anchor, is at most
      -- one step from the end. Without it, `2*j` needs the forbidden `j-1`.
      have hreg : anchor N = 4 * (N / 4) := by simp [anchor, late.2]
      have bound : N ≤ j + 1 := by omega
      have hmod : anchor N % 4 = 0 := by rw [hreg]; omega
      apply forceAt hc hjN hprefix (t := j) hjN
      intro x y hx hy ax ay hsum
      unfold Available at ax ay
      omega
    · -- For sum `j` both summands are earlier. Two recurring offsets give
      -- 0 mod 4. The exceptional short anchor 5 cannot pair to give 2 or 6.
      have cutoff : j ≤ anchor N ∨ (anchor N = 5 ∧ j ≤ 7) := by
        by_cases hs : N = 6 ∨ N = 7
        · exact Or.inr ⟨by simp [anchor, hs], by omega⟩
        · exact Or.inl (by omega)
      have htarget : 2 * (j / 2) = j := by omega
      apply forceAt hc hjN hprefix (t := j / 2) (by omega)
      intro x y hx hy ax ay hsum
      rw [htarget] at hsum
      unfold Available at ax ay
      omega

end EvenCover
