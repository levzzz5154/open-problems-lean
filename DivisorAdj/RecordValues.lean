import DivisorAdj.Records

/-! Exact first indices much larger than a divisor enumeration can handle.
All certificates use only additions, products, comparisons and primality tests
on the small prime table. The largest table here has thirty entries. -/

namespace DivisorAdj

private def primes29 : Fin 13 → ℕ := ![29,31,37,41,43,47,53,59,61,67,71,73,79]
private def primes37 : Fin 10 → ℕ := ![37,41,43,47,53,59,61,67,71,73]
private def primes53 : Fin 8 → ℕ := ![53,59,61,67,71,73,79,83]
private def primes97 : Fin 10 → ℕ := ![97,101,103,107,109,113,127,131,137,139]
private def primes127 : Fin 30 → ℕ :=
  ![127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281]

private theorem checked_record {k N m : ℕ} [NeZero m] (P : Fin (m+1) → ℕ)
    (h : TableChecks k P) (hv : (∏ i, P i) = N) : IsLeast {n : ℕ | 2 ≤ n ∧ a n = k} N :=
  hv ▸ first_of_table h

set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

theorem first_24 : IsLeast {n : ℕ | 2 ≤ n ∧ a n = 24} 14422893781144475428099 :=
  checked_record primes29 (by decide +kernel) (by decide +kernel)

theorem first_32 : IsLeast {n : ℕ | 2 ≤ n ∧ a n = 32} 203079283326684719 :=
  checked_record primes37 (by decide +kernel) (by decide +kernel)

theorem first_48 : IsLeast {n : ℕ | 2 ≤ n ∧ a n = 48} 434329083441619 :=
  checked_record primes53 (by decide +kernel) (by decide +kernel)

theorem first_90 : IsLeast {n : ℕ | 2 ≤ n ∧ a n = 90} 421336842070675358939 :=
  checked_record primes97 (by decide +kernel) (by decide +kernel)

theorem first_114 : IsLeast {n : ℕ | 2 ≤ n ∧ a n = 114}
    779748936453915736849589129606381217938585702367540346069703562697141 :=
  checked_record primes127 (by decide +kernel) (by decide +kernel)

theorem first_118 : IsLeast {n : ℕ | 2 ≤ n ∧ a n = 118} 6294274991138150192814357017873 :=
  checked_record (fun i : Fin 14 => primes127 (i.castLE (by decide))) (by decide +kernel) (by decide +kernel)

end DivisorAdj
