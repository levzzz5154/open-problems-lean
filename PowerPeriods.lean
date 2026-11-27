import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Int.GCD
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Periodicity in [OEIS A353890](https://oeis.org/A353890)

The polynomial-gcd argument is the known periodicity theorem of
[Bodin–Dèbes–Najib, Proposition 3.2](https://arxiv.org/abs/2002.02292).
Here the two power differences satisfy its hypothesis because three consecutive
points on a horizontal line cannot have the same complex modulus.
-/

namespace PowerPeriods

open Polynomial
open scoped Polynomial nonZeroDivisors

/-- Clearing the two denominators of a rational polynomial Bézout identity gives
an integral polynomial identity with a nonzero constant on the right. -/
private theorem integer_bezout (f g : ℤ[X])
    (h : IsCoprime (f.map (algebraMap ℤ ℚ)) (g.map (algebraMap ℤ ℚ))) :
    ∃ k : ℤ, k ≠ 0 ∧ ∃ u v : ℤ[X], u * f + v * g = C k := by
  obtain ⟨a, b, hab⟩ := h
  obtain ⟨⟨c, hc0⟩, hc⟩ := IsLocalization.integerNormalization_map_to_map ℤ⁰ a
  obtain ⟨⟨d, hd0⟩, hd⟩ := IsLocalization.integerNormalization_map_to_map ℤ⁰ b
  rw [Algebra.smul_def, Polynomial.algebraMap_apply, Subtype.coe_mk] at hc hd
  rw [mem_nonZeroDivisors_iff_ne_zero] at hc0 hd0
  refine ⟨c * d, mul_ne_zero hc0 hd0,
    C d * IsLocalization.integerNormalization ℤ⁰ a,
    C c * IsLocalization.integerNormalization ℤ⁰ b, ?_⟩
  apply Polynomial.map_injective (algebraMap ℤ ℚ) (IsFractionRing.injective ℤ ℚ)
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hc, hd, map_mul]
  calc
    _ = (C ((algebraMap ℤ ℚ) c) * C ((algebraMap ℤ ℚ) d)) *
        (a * f.map (algebraMap ℤ ℚ) + b * g.map (algebraMap ℤ ℚ)) := by ring
    _ = _ := by rw [hab, mul_one]

/-- The full gcd of two integer polynomial values (not just its coprimality
indicator) is periodic if the polynomials are coprime over the rationals. -/
theorem polynomial_gcd_periodic (f g : ℤ[X])
    (h : IsCoprime (f.map (algebraMap ℤ ℚ)) (g.map (algebraMap ℤ ℚ))) :
    ∃ T : ℕ, 0 < T ∧ ∀ m : ℤ,
      Int.gcd (f.eval (m + T)) (g.eval (m + T)) = Int.gcd (f.eval m) (g.eval m) := by
  obtain ⟨k, hk, u, v, huv⟩ := integer_bezout f g h
  have bound (m : ℤ) : (Int.gcd (f.eval m) (g.eval m) : ℤ) ∣ |k| := by
    apply (dvd_abs _ _).2
    have he := congrArg (Polynomial.eval m) huv
    simp only [eval_add, eval_mul, eval_C] at he
    rw [← he]
    exact dvd_add (dvd_mul_of_dvd_right Int.gcd_dvd_left _)
      (dvd_mul_of_dvd_right Int.gcd_dvd_right _)
  refine ⟨k.natAbs, Int.natAbs_pos.mpr hk, ?_⟩
  intro m
  rw [Int.natCast_natAbs]
  have transfer (s : ℤ) (hs : s ∣ |k|) (p : ℤ[X]) :
      s ∣ p.eval (m + |k|) ↔ s ∣ p.eval m := by
    apply dvd_iff_dvd_of_dvd_sub
    apply hs.trans
    simpa using Polynomial.sub_dvd_eval_sub (m + |k|) m p
  apply Nat.dvd_antisymm
  · exact Int.natCast_dvd_natCast.mp <| Int.dvd_coe_gcd
      ((transfer _ (bound (m + |k|)) f).mp Int.gcd_dvd_left)
      ((transfer _ (bound (m + |k|)) g).mp Int.gcd_dvd_right)
  · exact Int.natCast_dvd_natCast.mp <| Int.dvd_coe_gcd
      ((transfer _ (bound m) f).mpr Int.gcd_dvd_left)
      ((transfer _ (bound m) g).mpr Int.gcd_dvd_right)

private noncomputable def firstPoly (n : ℕ) : ℤ[X] := (X + 1) ^ n - X ^ n

private noncomputable def secondPoly (n : ℕ) : ℤ[X] :=
  (X + 2) ^ n - 2 * (X + 1) ^ n + X ^ n

/-- The three points on this line cannot all have the same squared modulus. -/
private theorem no_three_equal_powers {n : ℕ} (hn : n ≠ 0) (z : ℂ)
    (h₁ : (z + 1) ^ n = z ^ n) (h₂ : (z + 2) ^ n = (z + 1) ^ n) : False := by
  have norms {x y : ℂ} (h : x ^ n = y ^ n) : Complex.normSq x = Complex.normSq y := by
    apply (pow_left_inj₀ (Complex.normSq_nonneg x) (Complex.normSq_nonneg y) hn).mp
    simpa only [map_pow] using congrArg Complex.normSq h
  have e₁ := norms h₁
  have e₂ := norms h₂
  norm_num [Complex.normSq_apply, Complex.add_re, Complex.add_im] at e₁ e₂
  nlinarith

/-- Use integer subtraction so that the displayed second difference is the
OEIS expression, even when its first subtraction alone would be negative. -/
def differenceGCD (n : ℕ) (m : ℤ) : ℕ :=
  Int.gcd ((m + 1) ^ n - m ^ n) ((m + 2) ^ n - 2 * (m + 1) ^ n + m ^ n)

/-- The binary sequence in OEIS A353890, extended to every integer index. -/
def indicator (n : ℕ) (m : ℤ) : ℕ := if differenceGCD n m = 1 then 1 else 0

/-- In fact the sequence of gcds is periodic, not just the 0/1 sequence. -/
theorem differenceGCD_periodic (n : ℕ) (hn : 2 ≤ n) :
    ∃ T : ℕ, 0 < T ∧ ∀ m : ℤ, differenceGCD n (m + T) = differenceGCD n m := by
  have hc : IsCoprime ((firstPoly n).map (algebraMap ℤ ℚ))
      ((secondPoly n).map (algebraMap ℤ ℚ)) := by
    apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℚ ℂ _ _).mpr
    intro z
    by_cases h : aeval z ((firstPoly n).map (algebraMap ℤ ℚ)) = 0
    · right
      intro h'
      have hz : (z + 1) ^ n - z ^ n = 0 := by simpa [firstPoly] using h
      have two : aeval z (2 : ℚ[X]) = (2 : ℂ) := by
        simpa only [map_one, one_add_one_eq_two] using
          (map_add (aeval z : ℚ[X] →ₐ[ℚ] ℂ) (1 : ℚ[X]) 1)
      have hz' : (z + 2) ^ n - 2 * (z + 1) ^ n + z ^ n = 0 := by
        simpa [secondPoly, two] using h'
      apply no_three_equal_powers (by omega : n ≠ 0) z (sub_eq_zero.mp hz)
      linear_combination hz + hz'
    · exact Or.inl h
  simpa [differenceGCD, firstPoly, secondPoly] using
    polynomial_gcd_periodic (firstPoly n) (secondPoly n) hc

/-- A positive period for every exponent in the domain of A353890; the equality
holds in particular at each positive index, starting at 1, with no transient. -/
theorem indicator_periodic (n : ℕ) (hn : 2 ≤ n) :
    ∃ T : ℕ, 0 < T ∧ ∀ m : ℤ, indicator n (m + T) = indicator n m := by
  obtain ⟨T, hT, h⟩ := differenceGCD_periodic n hn
  exact ⟨T, hT, fun m => by simp only [indicator, h m]⟩

end PowerPeriods
