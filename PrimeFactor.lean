import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.NormNum.Prime

/-! # The greatest-prime-factor prediction in OEIS A353890

The entry proposes both `φ(2^n + 1)/2 + 1` and the Jacobsthal number as the
largest prime factor of the period at prime exponents `n ≥ 5`. At `n = 29`
the two predictions are different numbers, and neither is prime. This does
not require computing, or assuming any particular value for, the period.
-/

namespace PowerDifferences

/-- `p` is the largest prime divisor of `a`. -/
def IsGreatestPrimeFactor (a p : ℕ) : Prop :=
  p.Prime ∧ p ∣ a ∧ ∀ q : ℕ, q.Prime → q ∣ a → q ≤ p

/-- The closed form for a Jacobsthal number at an odd index. -/
def oddJacobsthal (n : ℕ) : ℕ := (2 ^ n + 1) / 3

theorem totient_prediction_at_29 : (2 ^ 29 + 1).totient / 2 + 1 = 5 * 35184749 := by
  rw [show 2 ^ 29 + 1 = 3 * 59 * 3033169 by decide,
      Nat.totient_mul (show Nat.Coprime (3 * 59) 3033169 by decide),
      Nat.totient_mul (show Nat.Coprime 3 59 by decide),
      Nat.totient_prime (by norm_num : Nat.Prime 3),
      Nat.totient_prime (by norm_num : Nat.Prime 59),
      Nat.totient_prime (by norm_num : Nat.Prime 3033169)]

theorem jacobsthal_prediction_at_29 : oddJacobsthal 29 = 59 * 3033169 := by decide

/-- For *any* proposed period sequence, the same prime exponent refutes both
versions of the prediction in the entry. -/
theorem greatest_prime_factor_counterexample (a : ℕ → ℕ) :
    ∃ n : ℕ, n.Prime ∧ 5 ≤ n ∧
      ¬ IsGreatestPrimeFactor (a n) ((2 ^ n + 1).totient / 2 + 1) ∧
      ¬ IsGreatestPrimeFactor (a n) (oddJacobsthal n) := by
  refine ⟨29, by norm_num, by decide, ?_, ?_⟩
  · rw [totient_prediction_at_29]
    intro h
    exact (by norm_num : ¬ Nat.Prime (5 * 35184749)) h.1
  · rw [jacobsthal_prediction_at_29]
    intro h
    exact (by norm_num : ¬ Nat.Prime (59 * 3033169)) h.1

end PowerDifferences
