import DivisorAdj.FirstEight
import DivisorAdj.Rough
import DivisorAdj.Monotone

namespace DivisorAdj

open Finset

private theorem not_dvd_210 {p : ℕ} (hp : p.Prime) (h : 11 ≤ p) : ¬p ∣ 210 := by
  intro hd
  change p ∣ 2 * (3 * (5 * 7)) at hd
  simp only [hp.dvd_mul] at hd
  rcases hd with hd | hd | hd | hd <;> have := Nat.le_of_dvd (by decide) hd <;> omega

/-- Exact classification on all positive multiples of the first solution. -/
theorem eight_on_multiples {n : ℕ} (hn : 0 < n) (hd : 35336848261 ∣ n) :
    a n = 8 ↔ n.Coprime 210 := by
  have hN := Nat.le_of_dvd hn hd
  have h2 : 2 ≤ n := by omega
  constructor
  · intro h
    apply Nat.coprime_of_dvd
    intro p hp hpn
    exact not_dvd_210 hp ((prime_factor_obstruction h2 h).1 p (Nat.mem_primeFactors.mpr ⟨hp,hpn,hn.ne'⟩))
  · intro hc
    exact le_antisymm ((a_antitone_dvd (by decide) h2 hd).trans_eq candidate_value) (rough_lower h2 hc)

/-- Every consecutive prime product starting at eleven and ending at or beyond
37 gives eight, not just the first few proposed examples. -/
theorem consecutive_primes (t : ℕ) (ht : 37 ≤ t) :
    a (∏ p ∈ (Icc 11 t).filter Nat.Prime, p) = 8 := by
  let P (u : ℕ) := (Icc 11 u).filter Nat.Prime
  have h37 : (∏ p ∈ P 37, p) = 35336848261 := by decide +kernel
  have hs : P 37 ⊆ P t := by
    intro p hp
    obtain ⟨hm,hp⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp hm).1, (mem_Icc.mp hm).2.trans ht⟩, hp⟩
  have hn : 0 < ∏ p ∈ P t, p := prod_pos fun _ hp => (mem_filter.mp hp).2.pos
  apply (eight_on_multiples hn (h37 ▸ prod_dvd_prod_of_subset (P 37) (P t) id hs)).mpr
  apply Nat.Coprime.prod_left
  intro p hp
  obtain ⟨hm,hp⟩ := mem_filter.mp hp
  exact hp.coprime_iff_not_dvd.mpr (not_dvd_210 hp (mem_Icc.mp hm).1)

/-- A whole arithmetic progression of indices, with no primality conditions. -/
theorem progression (k : ℕ) : a (35336848261 * (1+210*k)) = 8 := by
  apply (eight_on_multiples (by positivity) (dvd_mul_right ..)).mpr
  rw [Nat.coprime_mul_iff_left, Nat.coprime_add_mul_left_left]
  exact ⟨by decide, Nat.coprime_one_left _⟩

end DivisorAdj
