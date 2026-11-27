import DivisorAdj.AnalyticDensity
import DivisorAdj.PrimeGrid
import DivisorAdj.ShortGrid
import Mathlib.NumberTheory.Primorial

/-! # Wilson's general consecutive-primorial assertion for A251758

For every positive output there is a product of consecutive primes beginning
at the least prime at least that output. The finite theorem is unconditional.
The unrestricted Lean implication takes just the published estimate (6.6) of
Dusart as a hypothesis; it does not assume any conjecture about prime gaps.
-/

namespace DivisorAdj

open Finset

/-- No analytic hypotheses for the finite range, including the small prime-gap exceptions. -/
theorem wilson_through_400000 {k : ℕ} (hk : 0 < k) (hK : k ≤ 400000) : WilsonValue k := by
  by_cases h : 512 ≤ k
  · obtain ⟨p,hp,hkp,_,hd⟩ := medium_prime_density h hK
    exact wilson_of_density hp hkp hd
  · exact wilson_small hk (by omega)

/-- Equation (6.6) of Dusart implies the unrestricted Wilson assertion. -/
theorem wilson_of_dusart (H : Dusart66) {k : ℕ} (hk : 0 < k) : WilsonValue k := by
  by_cases small : k ≤ 400000
  · exact wilson_through_400000 hk small
  · have ex : ∃ q : ℕ, q.Prime ∧ k ≤ q := by
      obtain ⟨q,hkq,hq⟩ := Nat.exists_infinite_primes k; exact ⟨q,hq,hkq⟩
    let p := Nat.find ex
    obtain ⟨hp,hkp⟩ := Nat.find_spec ex
    have first (r : ℕ) (hr : r.Prime) (hkr : k ≤ r) : p ≤ r := Nat.find_min' ex ⟨hr,hkr⟩
    exact wilson_of_density hp hkp (analytic_prime_density H (by omega) hkp first)

private theorem interval_primorial {k t : ℕ} (hk : 0 < k) (hkt : k ≤ t) :
    primorial t / primorial (k-1) = ∏ p ∈ (Icc k t).filter Nat.Prime, p := by
  let A := (range ((k-1)+1)).filter Nat.Prime
  let B := (Icc k t).filter Nat.Prime
  have eq : (range (t+1)).filter Nat.Prime = A ∪ B := by
    ext p
    simp only [A,B,mem_filter,mem_union,mem_range,mem_Icc]
    constructor
    · rintro ⟨h,hp⟩; by_cases hlo : p < k
      · exact Or.inl ⟨by omega,hp⟩
      · exact Or.inr ⟨⟨by omega,by omega⟩,hp⟩
    · rintro (⟨hl,hp⟩|⟨⟨_,hl⟩,hp⟩) <;> exact ⟨by omega,hp⟩
  have dis : Disjoint A B := by
    apply disjoint_left.mpr; intro p hp hq
    have hlo := mem_range.mp (mem_filter.mp hp).1
    have hhi := (mem_Icc.mp (mem_filter.mp hq).1).1
    omega
  change (∏ p ∈ (range (t+1)).filter Nat.Prime, p) / primorial (k-1) = _
  rw [eq,prod_union dis]
  exact Nat.mul_div_cancel_left _ (primorial_pos (k-1))

theorem wilson_primorial_through_400000 {k : ℕ} (hk : 0 < k) (hK : k ≤ 400000) :
    ∃ t, k ≤ t ∧ a (primorial t / primorial (k-1)) = k := by
  obtain ⟨t,hkt,h⟩ := wilson_through_400000 hk hK
  exact ⟨t,hkt,by rwa [interval_primorial hk hkt]⟩

/-- The exact quotient formulation in Wilson's original question. -/
theorem wilson_primorial_of_dusart (H : Dusart66) {k : ℕ} (hk : 0 < k) :
    ∃ t, k ≤ t ∧ a (primorial t / primorial (k-1)) = k := by
  obtain ⟨t,hkt,h⟩ := wilson_of_dusart H hk
  exact ⟨t,hkt,by rwa [interval_primorial hk hkt]⟩

end DivisorAdj
