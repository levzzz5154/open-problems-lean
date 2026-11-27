import DivisorAdj.Prefix
import DivisorAdj.Tail
import DivisorAdj.Slots
import DivisorAdj.Value
import Mathlib.NumberTheory.Primorial

/-! # First occurrence of eight in OEIS A251758

[Robert G. Wilson v, 2014](https://oeis.org/A251758): is the product of the
primes from 11 through 37 the least index at which the quotient equals eight?
[Adamczewski, Appendix A](https://arxiv.org/html/2608.11941v1) lists verified
first occurrences through 17 *except eight*. Here the proof for eight never
enumerates indices below the candidate. In fact, for arbitrarily large `n`,
returning eight requires at least eight distinct prime factors.
-/

namespace DivisorAdj

open Finset

/-- Unbounded in `n`: seven prime factors at least 11 can never lower the
quotient below nine, whatever their multiplicities. -/
theorem nine_le_of_seven {n : ℕ} (hn : 2 ≤ n) (hmin : ∀ p ∈ n.primeFactors, 11 ≤ p)
    (hcard : n.primeFactors.card ≤ 7) : 9 ≤ a n := by
  have hn' : 0 < n := by omega
  obtain ⟨s⟩ := (rank_threshold hn' hmin).2 hcard
  have h1 := prefix_bound hn' s
  have h2 := compositeWeight_le hn' s
  have hrecip : 9 * recipSum (divs n) < 1 := by linarith
  have hr := mul_lt_mul_of_pos_left hrecip (by positivity : 0 < (n : ℚ)^2)
  have ht : (9 : ℚ) * prodSum (divs n) < (n : ℚ)^2 := by
    rw [ratio_identity hn']; linarith only [hr]
  exact (Nat.le_div_iff_mul_le (prodSum_pos hn)).mpr (by exact_mod_cast ht.le)

theorem prime_factor_obstruction {n : ℕ} (hn : 2 ≤ n) (h : a n = 8) :
    (∀ p ∈ n.primeFactors, 11 ≤ p) ∧ 8 ≤ n.primeFactors.card := by
  have h8 : 8 ≤ n.minFac := h ▸ a_le_minFactor hn
  have hmin : ∀ p ∈ n.primeFactors, 11 ≤ p := by
    intro p hp
    obtain ⟨hp', hd, _⟩ := Nat.mem_primeFactors.mp hp
    have hlo := h8.trans (Nat.minFac_le_of_dvd hp'.two_le hd)
    by_contra! h11
    interval_cases p <;> norm_num at *
  refine ⟨hmin, ?_⟩
  by_contra! hc
  have := nine_le_of_seven hn hmin (by omega); omega

/-- Exact answer to Wilson's question, as a least element, not just a witness. -/
theorem first_eight : IsLeast {n : ℕ | 2 ≤ n ∧ a n = 8} 35336848261 := by
  refine ⟨⟨by decide, candidate_value⟩, ?_⟩
  intro n ⟨hn,h⟩
  obtain ⟨hm,hc⟩ := prime_factor_obstruction hn h
  exact (rank_threshold (by omega : 0 < n) hm).1 hc

theorem wilson_first_eight : IsLeast {n : ℕ | 2 ≤ n ∧ a n = 8} (primorial 37 / primorial 7) := by
  have h : primorial 37 / primorial 7 = 35336848261 := by decide +kernel
  rw [h]; exact first_eight

end DivisorAdj
