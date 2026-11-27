import EvenCover.Core
import Mathlib.Data.Nat.Bitwise

namespace EvenCover

/-- Read `k` bits, most significant first. -/
def pack (s : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | k + 1 => Nat.bit (s k) (pack s k)

theorem pack_congr {s t : ℕ → Bool} (k : ℕ) (h : ∀ i < k, s i = t i) :
    pack s k = pack t k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [pack, h k (by omega), ih (fun i hi => h i (by omega))]

theorem pack_lt (s : ℕ → Bool) (k : ℕ) : pack s k < 2 ^ k := by
  induction k with
  | zero => simp [pack]
  | succ k ih =>
    rw [pack, Nat.pow_succ]
    cases s k <;> simp only [Nat.bit_true, Nat.bit_false] <;> omega

theorem pack_testBit (s : ℕ → Bool) (k i : ℕ) :
    (pack s k).testBit i = if i < k then s (k - 1 - i) else false := by
  induction k generalizing i with
  | zero => simp [pack]
  | succ k ih =>
    cases i with
    | zero => simp [pack, Nat.testBit_bit_zero]
    | succ i =>
      rw [pack, Nat.testBit_bit_succ, ih]
      simp only [Nat.succ_lt_succ_iff, Nat.succ_sub_one]
      rw [show k - (i + 1) = k - 1 - i by omega]

theorem pack_append (s : ℕ → Bool) (m n : ℕ) :
    pack s (m + n) = pack s m * 2^n + pack (fun i => s (m + i)) n := by
  induction n with
  | zero => simp [pack]
  | succ n ih =>
    change Nat.bit (s (m + n)) (pack s (m + n)) =
      pack s m * 2^(n+1) + Nat.bit (s (m+n)) (pack (fun i => s (m+i)) n)
    rw [ih, Nat.pow_succ, ← Nat.mul_assoc]
    cases s (m+n) <;> simp only [Nat.bit_true, Nat.bit_false] <;> omega

/-- The integer with ones at the specified reflected offsets. -/
def number (N : ℕ) : ℕ := pack (fun i => decide (pattern N i)) (N+1)

theorem number_bit {N i : ℕ} (h : i ≤ N) :
    (number N).testBit i = decide (pattern N (N-i)) := by
  simp [number, pack_testBit, show i < N+1 by omega]

theorem number_top (N : ℕ) : (number N).testBit N = true := by
  simp [number_bit (le_refl N), pattern]

/-- An inequality has a leading differing bit, with the predicted orientation. -/
theorem leading_difference {a b : ℕ} (h : a < b) :
    ∃ i, a.testBit i = false ∧ b.testBit i = true ∧ ∀ j > i, a.testBit j = b.testBit j := by
  obtain ⟨i, hi, hhi⟩ := Nat.exists_most_significant_bit (Nat.xor_ne_zero.mpr h.ne)
  have heq (j) (hj : i < j) : a.testBit j = b.testBit j := by
    have hz := hhi j hj
    rw [Nat.testBit_xor] at hz
    cases ha : a.testBit j <;> cases hb : b.testBit j <;> simp_all
  rw [Nat.testBit_xor] at hi
  cases ha : a.testBit i <;> cases hb : b.testBit i
  · simp [ha, hb] at hi
  · exact ⟨i, ha, hb, heq⟩
  · exact (h.asymm (Nat.lt_of_testBit i hb ha (fun j hj => (heq j hj).symm))).elim
  · simp [ha, hb] at hi

end EvenCover
