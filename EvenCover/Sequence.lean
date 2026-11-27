import EvenCover.Binary
import EvenCover.Coverage
import EvenCover.Optimality

/-! # The least pair-sum covering integer (OEIS A397185)

Source: https://oeis.org/A397185. The one-based bit positions must cover
`2, 4, ..., 2n` by pair sums; the two positions need not be distinct.
The minimization below is over *all* positive integers, not just `n`-bit words.
-/

namespace EvenCover

/-- Use `p+1` and `q+1` because `Nat.testBit` counts from bit zero. -/
def Covers (n m : ℕ) : Prop := ∀ t < n, ∃ p q : ℕ,
  m.testBit p = true ∧ m.testBit q = true ∧ (p+1) + (q+1) = 2*(t+1)

private theorem bit_index_le {N m p : ℕ} (hm : m < 2^(N+1))
    (hp : m.testBit p = true) : p ≤ N := by
  by_contra! h
  have h₁ := Nat.testBit_implies_ge hp
  have h₂ : (2:ℕ)^(N+1) ≤ 2^p := Nat.pow_le_pow_right (by decide) h
  omega

/-- Reflecting a word exchanges the target `t` with `N-t`. -/
theorem covers_iff_offsets {N m : ℕ} (hm : m < 2^(N+1)) :
    Covers (N+1) m ↔ CoversOffsets N (fun d => m.testBit (N-d) = true) := by
  constructor
  · intro hc t ht
    obtain ⟨p,q,hp,hq,hs⟩ := hc (N-t) (by omega)
    have hp' := bit_index_le hm hp
    have hq' := bit_index_le hm hq
    exact ⟨N-p, N-q, by omega, by omega, by simpa only [show N-(N-p)=p by omega],
      by simpa only [show N-(N-q)=q by omega], by omega⟩
  · intro hc t ht
    obtain ⟨p,q,hp,hq,hp',hq',hs⟩ := hc (N-t) (by omega)
    exact ⟨N-p, N-q, hp', hq', by omega⟩

private theorem number_selected {N i : ℕ} (h : i ≤ N) :
    (number N).testBit (N-i) = true ↔ pattern N i := by
  rw [number_bit (Nat.sub_le N i), show N - (N-i) = i by omega, decide_eq_true_eq]

theorem number_covers (N : ℕ) : Covers (N+1) (number N) := by
  apply (covers_iff_offsets (pack_lt _ _)).2
  intro t ht
  obtain ⟨x,y,hx,hy,hpx,hpy,hs⟩ := pattern_covers N t ht
  exact ⟨x,y,hx,hy,(number_selected hx).2 hpx,(number_selected hy).2 hpy,hs⟩

/-- No smaller integer covers the target interval. At the leading differing bit,
all earlier set offsets are permitted by the pattern, so the bit is forced. -/
theorem number_le_of_covers {N m : ℕ} (hc : Covers (N+1) m) : number N ≤ m := by
  by_contra! hlt
  have hm : m < 2^(N+1) := lt_trans hlt (pack_lt _ _)
  have hcov := (covers_iff_offsets hm).1 hc
  obtain ⟨i,hi,hi',hh⟩ := leading_difference hlt
  have hbound : i ≤ N := bit_index_le (pack_lt _ _) hi'
  have hp : pattern N (N-i) := of_decide_eq_true ((number_bit hbound).symm.trans hi')
  have hf := pattern_forced (S := fun d => m.testBit (N-d) = true) hcov hp (by
    intro d hd hs
    apply (number_selected (show d ≤ N by omega)).1
    rw [← hh (N-d) (by omega)]
    exact hs)
  change m.testBit (N-(N-i)) = true at hf
  rw [show N-(N-i)=i by omega, hi] at hf
  contradiction

private theorem exists_cover (n : ℕ) : ∃ m : ℕ, 0 < m ∧ Covers n m := by
  cases n with
  | zero => exact ⟨1, by decide, fun t ht => (Nat.not_lt_zero t ht).elim⟩
  | succ n =>
    refine ⟨number n, ?_, number_covers n⟩
    have h := Nat.testBit_implies_ge (number_top n)
    exact lt_of_lt_of_le (Nat.two_pow_pos n) h

/-- A397185, extended to `n=0` by the same least-positive-integer definition. -/
noncomputable def sequence (n : ℕ) : ℕ := by
  classical
  exact Nat.find (exists_cover n)

/-- Exact bit pattern of the least covering integer for every positive index. -/
theorem sequence_succ (N : ℕ) : sequence (N+1) = number N := by
  classical
  change Nat.find (exists_cover (N+1)) = number N
  apply le_antisymm
  · exact Nat.find_min' _ ⟨lt_of_lt_of_le (Nat.two_pow_pos N)
      (Nat.testBit_implies_ge (number_top N)), number_covers N⟩
  · exact number_le_of_covers (Nat.find_spec (exists_cover (N+1))).2

private theorem even_prefix (k i : ℕ) (hi : i ≤ 2*k) :
    pattern (2*k+1) i ↔ pattern (2*k) i := by
  have ha : anchor (2*k+1) = anchor (2*k) := by
    unfold anchor
    split <;> split <;> omega
  have he : 2*k % 4 = 2 ∨ 2*k = anchor (2*k) := by
    unfold anchor
    split <;> omega
  unfold pattern
  rw [ha]
  omega

private theorem number_even_extend (k : ℕ) : number (2*k+1) = 2*number (2*k)+1 := by
  unfold number
  rw [pack]
  have hone : decide (pattern (2*k+1) (2*k+1)) = true := by simp [pattern]
  rw [hone, Nat.bit_true]
  have hp : pack (fun i => decide (pattern (2*k+1) i)) (2*k+1) =
      pack (fun i => decide (pattern (2*k) i)) (2*k+1) := by
    apply pack_congr
    intro i hi
    exact decide_eq_decide.mpr (even_prefix k i (by omega))
  rw [hp]

/-- The conjecture in the OEIS entry, at every even index. -/
theorem even_recurrence (k : ℕ) (hk : 0 < k) :
    sequence (2*k) = 2 * sequence (2*k-1) + 1 := by
  have h₁ : 2*k-1 = 2*(k-1)+1 := by omega
  have h₂ : 2*k = (2*(k-1)+1)+1 := by omega
  calc sequence (2*k) = sequence ((2*(k-1)+1)+1) := congrArg sequence h₂
       _ = number (2*(k-1)+1) := sequence_succ _
       _ = 2 * number (2*(k-1)) + 1 := number_even_extend _
       _ = 2 * sequence (2*k-1) + 1 := by rw [h₁, sequence_succ]

end EvenCover
