import Mathlib.Data.Nat.Basic

/-! # Reflected bit positions for OEIS A397185

For a word of length `N + 1`, let offset zero be the *most* significant
bit. Reflecting the pair-sum condition in `N` leaves precisely the even
sums from zero through `2*N`. Smaller binary numbers prefer an absent bit
at the first differing offset.
-/

namespace EvenCover

def CoversOffsets (N : ℕ) (S : ℕ → Prop) : Prop :=
  ∀ t ≤ N, ∃ x y : ℕ, x ≤ N ∧ y ≤ N ∧ S x ∧ S y ∧ x + y = 2 * t

/-- End correction to the recurring offsets `2 mod 4`. -/
def anchor (N : ℕ) : ℕ := if N = 6 ∨ N = 7 then 5 else 4 * (N / 4)

/-- The proposed optimal set, including both endpoints. -/
def pattern (N i : ℕ) : Prop :=
  i ≤ N ∧ (i = 0 ∨ i % 4 = 2 ∨ i = anchor N ∨ i = N)

instance (N i : ℕ) : Decidable (pattern N i) := by
  unfold pattern
  infer_instance

end EvenCover
