import ActivePrimes
import PowerPeriods
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Data.Nat.Factorization.Basic

/-! # Prime factors of the least period in OEIS A353890

A prime is active if it admits a triple of equal consecutive `n`-th powers.
Every period must be divisible by every active prime: otherwise multiples of
the period visit a bad residue, although the indicator at zero is one.
Conversely, a shift divisible by the active primes preserves each obstruction.
Thus the least period is their squarefree product, including the empty product.
-/

namespace PowerPeriods

open Function
open scoped BigOperators

/-- Exact translation from divisibility of both differences to a local obstruction.
Primality is not needed for this translation. -/
theorem dvd_differenceGCD_iff (n p : ℕ) (m : ℤ) :
    p ∣ differenceGCD n m ↔ (m : ZMod p) ^ n = ((m : ZMod p) + 1) ^ n ∧
      ((m : ZMod p) + 1) ^ n = ((m : ZMod p) + 2) ^ n := by
  have hd (a b : ℤ) : p ∣ Int.gcd a b ↔ (p : ℤ) ∣ a ∧ (p : ℤ) ∣ b := by
    rw [← Int.natCast_dvd_natCast]
    exact ⟨fun h => ⟨h.trans Int.gcd_dvd_left, h.trans Int.gcd_dvd_right⟩,
      fun h => Int.dvd_coe_gcd h.1 h.2⟩
  rw [differenceGCD, hd, ← ZMod.intCast_zmod_eq_zero_iff_dvd,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨(sub_eq_zero.mp h₁).symm, by linear_combination -h₁ - h₂⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨sub_eq_zero.mpr h₁.symm, by linear_combination h₁ - h₂⟩

private theorem active_of_dvd {n p : ℕ} {m : ℤ} (hp : p.Prime) (h : p ∣ differenceGCD n m) :
    ActivePrime n p := ⟨hp, m, (dvd_differenceGCD_iff n p m).mp h⟩

/-- An arbitrary shift, including zero, is a period exactly when it is a
multiple of every active prime. -/
theorem periodic_iff_active_dvd (n : ℕ) (hn : 2 ≤ n) (T : ℕ) :
    Periodic (indicator n) (T : ℤ) ↔ ∀ p, ActivePrime n p → p ∣ T := by
  constructor
  · intro hper p ⟨hp, x, hx⟩
    letI : Fact p.Prime := ⟨hp⟩
    by_contra h
    have hT : (T : ZMod p) ≠ 0 := fun hz => h ((ZMod.natCast_zmod_eq_zero_iff_dvd T p).mp hz)
    obtain ⟨b, hb⟩ := ZMod.intCast_surjective (x / (T : ZMod p))
    have he : ((b * (T : ℤ) : ℤ) : ZMod p) = x := by
      rw [Int.cast_mul, Int.cast_natCast, hb, div_mul_cancel₀ _ hT]
    have hd : p ∣ differenceGCD n (b * T) :=
      (dvd_differenceGCD_iff n p _).mpr (by simpa only [he] using hx)
    have hzero : indicator n 0 = 1 := by
      simp [indicator, differenceGCD, zero_pow (by omega : n ≠ 0)]
    have hsame : indicator n (b * T) = 1 := by
      simpa only [zero_add, hzero] using hper.int_mul b 0
    by_cases hg : differenceGCD n (b * T) = 1
    · exact hp.not_dvd_one (hg ▸ hd)
    · simp [indicator, hg] at hsame
  · intro h m
    have shift (p : ℕ) (hpT : p ∣ T) :
        p ∣ differenceGCD n (m + T) ↔ p ∣ differenceGCD n m := by
      simp only [dvd_differenceGCD_iff, Int.cast_add, Int.cast_natCast,
        (ZMod.natCast_zmod_eq_zero_iff_dvd T p).mpr hpT, add_zero]
    have eqOne : differenceGCD n (m + T) = 1 ↔ differenceGCD n m = 1 := by
      rw [Nat.eq_one_iff_not_exists_prime_dvd, Nat.eq_one_iff_not_exists_prime_dvd]
      constructor
      · intro h₁ p hp hd
        exact h₁ p hp ((shift p (h p (active_of_dvd hp hd))).mpr hd)
      · intro h₁ p hp hd
        exact h₁ p hp ((shift p (h p (active_of_dvd hp hd))).mp hd)
    simp only [indicator, eqOne]

/-- No smaller period is gained by ignoring the nonpositive indices. -/
theorem periodic_iff_from_one (n : ℕ) (hn : 2 ≤ n) (T : ℕ) :
    Periodic (indicator n) (T : ℤ) ↔
      ∀ m : ℤ, 0 < m → indicator n (m + T) = indicator n m := by
  refine ⟨fun h m _ => h m, ?_⟩
  intro h m
  obtain ⟨U, hU, hper⟩ := indicator_periodic n hn
  have hp : Periodic (indicator n) (U : ℤ) := hper
  let b : ℤ := |m| + 1
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hu : (1 : ℤ) ≤ U := by exact_mod_cast hU
  have hpos : 0 < m + b * U := by
    have hmul := mul_le_mul_of_nonneg_left hu hb
    dsimp [b] at hmul ⊢
    linarith [neg_le_abs m]
  calc
    indicator n (m + T) = indicator n ((m + T) + b * U) := ((hp.int_mul b) _).symm
    _ = indicator n ((m + b * U) + T) := by rw [add_right_comm]
    _ = indicator n (m + b * U) := h _ hpos
    _ = indicator n m := hp.int_mul b m

/-- The OEIS sequence, as a least *positive* period. `periodic_iff_from_one`
identifies this definition with the sequence starting at index 1. -/
noncomputable def leastPeriod (n : ℕ) (hn : 2 ≤ n) : ℕ := by
  classical
  exact Nat.find (indicator_periodic n hn)

theorem leastPeriod_spec (n : ℕ) (hn : 2 ≤ n) :
    0 < leastPeriod n hn ∧ Periodic (indicator n) (leastPeriod n hn : ℤ) := by
  classical
  exact Nat.find_spec (indicator_periodic n hn)

theorem leastPeriod_min (n : ℕ) (hn : 2 ≤ n) {T : ℕ} (hT : 0 < T)
    (hper : Periodic (indicator n) (T : ℤ)) : leastPeriod n hn ≤ T := by
  classical
  exact Nat.find_min' (indicator_periodic n hn) ⟨hT, hper⟩

/-- A certificate consisting of exactly the active primes determines the answer. -/
theorem leastPeriod_eq_prod (n : ℕ) (hn : 2 ≤ n) (S : Finset ℕ)
    (hS : ∀ p, p ∈ S ↔ ActivePrime n p) : leastPeriod n hn = ∏ p ∈ S, p := by
  have hL := leastPeriod_spec n hn
  have hsub : S ⊆ (leastPeriod n hn).primeFactors := by
    intro p hp
    have ha := (hS p).mp hp
    exact Nat.mem_primeFactors.mpr ⟨ha.1, (periodic_iff_active_dvd n hn _).mp hL.2 p ha, hL.1.ne'⟩
  apply Nat.le_antisymm
  · apply leastPeriod_min n hn (Finset.prod_pos fun p hp => ((hS p).mp hp).1.pos)
    exact (periodic_iff_active_dvd n hn _).mpr fun p hp =>
      Finset.dvd_prod_of_mem (fun q : ℕ => q) ((hS p).mpr hp)
  · apply Nat.le_of_dvd hL.1
    exact (Finset.prod_dvd_prod_of_subset S _ (fun p => p) hsub).trans (Nat.prod_primeFactors_dvd _)

/-- A prime divides the least period iff the local obstruction exists. In
particular none of the witnessed primes disappear on passing to the minimum. -/
theorem mem_primeFactors_iff_active (n : ℕ) (hn : 2 ≤ n) (p : ℕ) :
    p ∈ (leastPeriod n hn).primeFactors ↔ ActivePrime n p := by
  classical
  let S := (leastPeriod n hn).primeFactors.filter (ActivePrime n)
  have hs (q : ℕ) : q ∈ S ↔ ActivePrime n q := by
    refine ⟨fun h => (Finset.mem_filter.mp h).2, fun h => Finset.mem_filter.mpr ⟨?_, h⟩⟩
    have hL := leastPeriod_spec n hn
    exact Nat.mem_primeFactors.mpr ⟨h.1, (periodic_iff_active_dvd n hn _).mp hL.2 q h, hL.1.ne'⟩
  refine ⟨fun hp => ?_, fun hp => (Finset.mem_filter.mp ((hs p).mpr hp)).1⟩
  obtain ⟨hprime, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
  rw [leastPeriod_eq_prod n hn S hs] at hdvd
  obtain ⟨q, hq, hpq⟩ := (hprime.prime.dvd_finset_prod_iff (fun q : ℕ => q)).mp hdvd
  have hact := (hs q).mp hq
  exact (Nat.prime_dvd_prime_iff_eq hprime hact.1).mp hpq ▸ hact

theorem leastPeriod_eq_radical (n : ℕ) (hn : 2 ≤ n) :
    leastPeriod n hn = ∏ p ∈ (leastPeriod n hn).primeFactors, p :=
  leastPeriod_eq_prod n hn _ (mem_primeFactors_iff_active n hn)

/-- At prime exponents every prime factor is 1 modulo the exponent. -/
theorem prime_exponent_congruence {n p : ℕ} (hn : n.Prime)
    (hp : p ∈ (leastPeriod n hn.two_le).primeFactors) : n ∣ p - 1 :=
  dvd_sub_one_of_activePrime hn ((mem_primeFactors_iff_active n hn.two_le p).mp hp)

/-- All primes from a divisor exponent persist, and the *whole* earlier
period divides the new one. -/
theorem leastPeriod_dvd_of_dvd {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ≤ n) (hdn : d ∣ n) :
    leastPeriod d hd ∣ leastPeriod n hn := by
  have hsub : (leastPeriod d hd).primeFactors ⊆ (leastPeriod n hn).primeFactors := by
    intro p hp
    exact (mem_primeFactors_iff_active n hn p).mpr
      (activePrime_of_dvd hdn ((mem_primeFactors_iff_active d hd p).mp hp))
  calc
    leastPeriod d hd = _ := leastPeriod_eq_radical d hd
    _ ∣ _ := Finset.prod_dvd_prod_of_subset _ _ (fun p => p) hsub
    _ ∣ leastPeriod n hn := Nat.prod_primeFactors_dvd _

/-- Every prime `p ≥ 5` occurs in the period at exponent `p - 1`. -/
theorem prime_occurs_at_sub_one {p : ℕ} (hp : p.Prime) (h₅ : 5 ≤ p) :
    p ∈ (leastPeriod (p - 1) (by omega)).primeFactors :=
  (mem_primeFactors_iff_active _ _ _).mpr (activePrime_sub_one hp h₅)

end PowerPeriods
