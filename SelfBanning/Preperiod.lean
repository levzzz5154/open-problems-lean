import SelfBanning.Mirror
import SelfBanning.Obstruction
import Mathlib.Algebra.Ring.Periodic

namespace SelfBanning

/-- Before any label is released, the greedy algorithm takes consecutive values. -/
theorem initial_ramp {k : ℕ} {a : ℕ → ℕ} (h : IsRow k a) (i : ℕ) (hi : i ≤ k) : a i = k+i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    apply le_antisymm
    · by_contra! ht
      obtain ⟨s,hs,_,he⟩ := h.skipped i (k+i) (by omega) ht
      have hp := ih s hs (by omega)
      omega
    · by_contra! ht
      have hl := h.lower i
      let j := a i-k
      have hj : j < i := by dsimp [j]; omega
      have hj' := ih j hj (by omega)
      have he : a j = a i := hj'.trans (by dsimp [j]; omega)
      exact h.allowed i j hj (by omega) he

/-- In fact the initial run itself can never recur sufficiently late. -/
theorem no_late_ramp {k N : ℕ} {a : ℕ → ℕ} (h : IsRow k a) (hk : 3 ≤ k)
    (hN : 5*(k+2) ≤ N) : ¬ ∀ i ≤ k, a (N+i) = k+i :=
  fun hr => no_mirror h hk hN (mirror_of_ramp h (by omega) (by omega) hr)

/-- OEIS A398589's other conjecture: for `k>2` no positive period works
from time zero. This does not conflict with eventual periodicity. -/
theorem not_purely_periodic {k T : ℕ} {a : ℕ → ℕ} (h : IsRow k a) (hk : 3 ≤ k) (hT : 0 < T) :
    ¬ Function.Periodic a T := by
  intro per
  let m := 5*(k+2)
  have hN : 5*(k+2) ≤ m*T := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left m (show 1 ≤ T by omega)
  apply no_late_ramp h hk hN
  intro i hi
  have hh : a (i+m*T) = a i := by simpa using (per.nat_mul m) i
  rw [Nat.add_comm (m*T) i, hh, initial_ramp h i hi]

end SelfBanning
