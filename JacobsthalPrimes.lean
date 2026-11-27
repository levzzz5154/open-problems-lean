import PeriodPrimes
import Mathlib.Algebra.Ring.Parity

/-! # Why Jacobsthal numbers occur in A353890

The largest-factor formula is false, but prime divisors `p > 3` of the
odd-index Jacobsthal number really do occur. The three residues come from
the arithmetic progression `-2, 1, 4`, rescaled by `1/3` in `ZMod p`.
-/

namespace PowerPeriods

/-- If `-2` is an `n`th root of unity, its square and `1` give the other two entries. -/
theorem active_of_neg_two_pow {n p : ℕ} (hp : p.Prime) (h₃ : 3 < p)
    (he : (-2 : ZMod p)^n = 1) : ActivePrime n p := by
  letI : Fact p.Prime := ⟨hp⟩
  have hn : (3 : ZMod p) ≠ 0 := by
    intro hz
    have hd := (ZMod.natCast_zmod_eq_zero_iff_dvd 3 p).mp hz
    exact (not_le_of_gt h₃) (Nat.le_of_dvd (by decide) hd)
  let z := (3 : ZMod p)⁻¹
  have hz : (3 : ZMod p)*z=1 := mul_inv_cancel₀ hn
  have e₁ : (-2 : ZMod p)*z+1=z := by linear_combination -hz
  have e₂ : (-2 : ZMod p)*z+2=(-2)^2*z := by linear_combination -2*hz
  have hpow : ((-2 : ZMod p)^2)^n=1 := by rw [← pow_mul, Nat.mul_comm 2 n, pow_mul, he, one_pow]
  refine ⟨hp, (-2)*z, ?_, ?_⟩
  · rw [e₁, mul_pow, he, one_mul]
  · rw [e₁,e₂,mul_pow,hpow,one_mul]

/-- A common criterion for prime divisors of `2^n+1` at odd exponents
and of `2^n-1` at even exponents. -/
theorem prime_factor_of_neg_two {n p : ℕ} (hn : 2 ≤ n) (hp : p.Prime) (h₃ : 3 < p)
    (hd : (p : ℤ) ∣ (-2 : ℤ)^n-1) : p ∈ (leastPeriod n hn).primeFactors := by
  apply (mem_primeFactors_iff_active _ _ _).2
  apply active_of_neg_two_pow hp h₃
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hd
  push_cast at hz
  exact sub_eq_zero.mp hz

/-- All prime factors above 3 of the odd Jacobsthal number are genuine factors
of the least period; they need not be the *largest* factor. -/
theorem odd_jacobsthal_factors {n p : ℕ} (hn : 2 ≤ n) (ho : Odd n)
    (hp : p.Prime) (h₃ : 3 < p) (hd : p ∣ (2^n+1)/3) : p ∈ (leastPeriod n hn).primeFactors := by
  have hthree : 3 ∣ 2^n+1 := by
    apply (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).1
    push_cast
    rw [show (2 : ZMod 3) = -1 by decide, ho.neg_one_pow]
    simp
  have hdiv : p ∣ 2^n+1 := hd.trans (Nat.div_dvd_of_dvd hthree)
  have haz := (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).2 hdiv
  push_cast at haz
  apply (mem_primeFactors_iff_active _ _ _).2
  apply active_of_neg_two_pow hp h₃
  rw [ho.neg_pow]
  linear_combination -haz

end PowerPeriods
