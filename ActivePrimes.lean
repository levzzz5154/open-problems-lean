import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum

namespace PowerPeriods

/-- A local obstruction in OEIS A353890: the powers agree at three consecutive
residues modulo `p`. No period is involved in this definition. -/
def ActivePrime (n p : ℕ) : Prop :=
  p.Prime ∧ ∃ x : ZMod p, x ^ n = (x + 1) ^ n ∧ (x + 1) ^ n = (x + 2) ^ n

/-- A triple witnessing activity still works at every multiple of its exponent. -/
theorem activePrime_of_dvd {d n p : ℕ} (hdn : d ∣ n) (h : ActivePrime d p) :
    ActivePrime n p := by
  obtain ⟨k, rfl⟩ := hdn
  obtain ⟨hp, x, h₁, h₂⟩ := h
  exact ⟨hp, x, by simp only [pow_mul, h₁], by simp only [pow_mul, h₂]⟩

/-- The order of the ratio divides both the original exponent and `p - 1`.
Thus raising to their gcd preserves equality for this pair of nonzero residues. -/
private theorem pow_eq_at_gcd {n p : ℕ} [Fact p.Prime] {a b : ZMod p}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ^ n = b ^ n) :
    a ^ (n.gcd (p - 1)) = b ^ (n.gcd (p - 1)) := by
  have h₁ : orderOf (a / b) ∣ n := orderOf_dvd_of_pow_eq_one (by
    rw [div_pow, hab, div_self (pow_ne_zero _ hb)])
  have h₂ := ZMod.orderOf_dvd_card_sub_one (div_ne_zero ha hb)
  have hg := orderOf_dvd_iff_pow_eq_one.mp (Nat.dvd_gcd h₁ h₂)
  rw [div_pow] at hg
  exact (div_eq_one_iff_eq (pow_ne_zero _ hb)).mp hg

/-- The *same* witness works after reducing the exponent to `gcd(n,p-1)`.
Conversely this gcd divides `n`, so raising the powers again recovers activity. -/
theorem activePrime_iff_gcd {n p : ℕ} (hn : 2 ≤ n) :
    ActivePrime n p ↔ ActivePrime (n.gcd (p - 1)) p := by
  refine ⟨?_, activePrime_of_dvd (Nat.gcd_dvd_left _ _)⟩
  rintro ⟨hp, x, h₁, h₂⟩
  letI : Fact p.Prime := ⟨hp⟩
  have hn₀ : n ≠ 0 := by omega
  have hx : x ≠ 0 := by
    rintro rfl
    simp [zero_pow hn₀] at h₁
  have next_ne {a b : ZMod p} (ha : a ≠ 0) (e : a ^ n = b ^ n) : b ≠ 0 := by
    rintro rfl
    exact pow_ne_zero _ ha (e.trans (zero_pow hn₀))
  have hy := next_ne hx h₁
  exact ⟨hp, x, pow_eq_at_gcd hx hy h₁, pow_eq_at_gcd hy (next_ne hy h₂) h₂⟩

/-- Successive residues are distinct in a prime field. -/
theorem not_activePrime_one (p : ℕ) : ¬ ActivePrime 1 p := by
  rintro ⟨hp, x, h, _⟩
  letI : Fact p.Prime := ⟨hp⟩
  simp at h

/-- For a prime exponent every active prime is congruent to one modulo that exponent. -/
theorem dvd_sub_one_of_activePrime {n p : ℕ} (hn : n.Prime) (h : ActivePrime n p) :
    n ∣ p - 1 := by
  have hg := (activePrime_iff_gcd hn.two_le).mp h
  rcases hn.eq_one_or_self_of_dvd _ (Nat.gcd_dvd_left n (p - 1)) with h₁ | h₂
  · rw [h₁] at hg
    exact (not_activePrime_one p hg).elim
  · exact h₂ ▸ Nat.gcd_dvd_right n (p - 1)

/-- Fermat's little theorem applied to the residues 1, 2, 3. -/
theorem activePrime_sub_one {p : ℕ} (hp : p.Prime) (h₅ : 5 ≤ p) : ActivePrime (p - 1) p := by
  letI : Fact p.Prime := ⟨hp⟩
  have small_ne (k : ℕ) (hk : 0 < k) (hlt : k < p) : (k : ZMod p) ≠ 0 := by
    intro h
    exact (Nat.not_le_of_lt hlt) (Nat.le_of_dvd hk ((ZMod.natCast_zmod_eq_zero_iff_dvd k p).mp h))
  have h₂ := ZMod.pow_card_sub_one_eq_one (small_ne 2 (by decide) (by omega))
  have h₃ := ZMod.pow_card_sub_one_eq_one (small_ne 3 (by decide) (by omega))
  have e₂ : (1 : ZMod p) + 1 = (2 : ℕ) := by norm_num
  have e₃ : (1 : ZMod p) + 2 = (3 : ℕ) := by norm_num
  exact ⟨hp, 1, by rw [one_pow, e₂, h₂], by rw [e₂, e₃, h₂, h₃]⟩

end PowerPeriods
