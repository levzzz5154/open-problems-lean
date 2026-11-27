import DivisorAdj.Dyadic
import DivisorAdj.Wilson

/-! # Unconditional expanding neighborhoods in Wilson's conjecture

Proximity to **any** prime suffices, not just to the next prime. Every prime
`p` supplies a block of about `√(2p)/8` consecutive targets ending at `p`.
The complete positive range below the elementary estimate is certified by
`wilson_through_400000`. No Dusart hypothesis appears in these results.
-/

namespace DivisorAdj

open Finset

theorem wilson_near_prime {k p : ℕ} (hk : 0 < k) (hp : p.Prime) (hkp : k ≤ p)
    (hgap : 8*(p-k) ≤ Nat.sqrt (2*p)) : WilsonValue k := by
  by_cases h : 8192 ≤ p
  · let m := ((Ioc p (2*p)).filter Nat.Prime).card
    let d := p-(k+1)
    have hc : Nat.sqrt (2*p) ≤ m := dyadic_prime_count h
    have hm : 0 < m := (Nat.le_sqrt.mpr (by have := hp.pos; omega) : 1 ≤ Nat.sqrt (2*p)).trans hc
    have h2 : p ≤ 2*k := by have := Nat.sqrt_le_self (2*p); omega
    have hd : 8*d ≤ m := (show 8*d ≤ 8*(p-k) by dsimp [d]; omega).trans (hgap.trans hc)
    apply wilson_of_density hp hkp
    change 4*p*d < m*(k+1)
    calc 4*p*d ≤ (8*d)*k := by nlinarith only [Nat.mul_le_mul_right d h2]
         _ ≤ m*k := Nat.mul_le_mul_right _ hd
         _ < m*(k+1) := Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self _) hm
  · exact wilson_through_400000 hk (by omega)

/-- Arbitrarily long blocks occur beyond any prescribed cutoff. -/
theorem wilson_blocks (width cutoff : ℕ) :
    ∃ a : ℕ, cutoff ≤ a ∧ ∀ k, a ≤ k → k ≤ a+width → WilsonValue k := by
  obtain ⟨p,hlo,hp⟩ := Nat.exists_infinite_primes (max (cutoff+width+1) ((8*width)^2))
  have h0 := (le_max_left (cutoff+width+1) ((8*width)^2)).trans hlo
  have hw := (le_max_right (cutoff+width+1) ((8*width)^2)).trans hlo
  refine ⟨p-width,by omega,?_⟩
  intro k hk hk'
  apply wilson_near_prime (by omega) hp (by omega)
  exact (show 8*(p-k) ≤ 8*width by omega).trans (Nat.le_sqrt'.mpr (by omega))

end DivisorAdj
