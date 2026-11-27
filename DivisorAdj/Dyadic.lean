import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic

/-! # A uniform square-root lower bound for dyadic prime counts

Keep the fourth prime range in the Erdős central-binomial-coefficient proof
of Bertrand's postulate, rather than assuming that range is empty. Applying
mathlib's `Bertrand.real_main_inequality` at `x/16` pays for two copies of
`(2x)^√(2x)`, instead of only one. No explicit prime number theorem is used.
-/

namespace DivisorAdj

open Finset

private theorem binom_dyadic {n : ℕ} (hn : 2 < n) :
    n.centralBinom ≤ (2*n)^Nat.sqrt (2*n) * 4^(2*n/3) *
      (2*n)^((Ioc n (2*n)).filter Nat.Prime).card := by
  let A := (range (2*n/3+1)).filter Nat.Prime
  let B := (Ioc n (2*n)).filter Nat.Prime
  let f (p : ℕ) := p^n.centralBinom.factorization p
  have sub : A ∪ B ⊆ range (2*n+1) := by
    intro p hp; apply mem_range.mpr
    rcases mem_union.mp hp with ha|hb
    · have := mem_range.mp (mem_filter.mp ha).1; omega
    · have := (mem_Ioc.mp (mem_filter.mp hb).1).2; omega
  have hdis : Disjoint A B := by
    apply disjoint_left.mpr; intro p ha hb
    have := mem_range.mp (mem_filter.mp ha).1
    have := (mem_Ioc.mp (mem_filter.mp hb).1).1
    omega
  have eq : (∏ p ∈ A ∪ B, f p) = n.centralBinom := by
    refine (prod_subset sub ?_).trans n.prod_pow_factorization_centralBinom
    intro p hp hab
    by_cases hprime : p.Prime
    · have ha : 2*n/3 < p := by
        by_contra! h
        exact hab (mem_union_left _ (mem_filter.mpr ⟨mem_range.mpr (by omega),hprime⟩))
      have hb : p ≤ n := by
        by_contra! h
        exact hab (mem_union_right _ (mem_filter.mpr ⟨mem_Ioc.mpr ⟨h,by have := mem_range.mp hp; omega⟩,hprime⟩))
      simp only [f,Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul hn hb (by omega),pow_zero]
    · simp only [f,Nat.factorization_eq_zero_of_non_prime _ hprime,pow_zero]
  have hpos : 1 ≤ 2*n := by omega
  have fsmall (p : ℕ) : f p ≤ 2*n := Nat.pow_factorization_choose_le (by omega)
  have prodA : (∏ p ∈ A, f p) ≤ (2*n)^Nat.sqrt (2*n)*4^(2*n/3) := by
    rw [← prod_filter_mul_prod_filter_not A (· ≤ Nat.sqrt (2*n))]
    apply mul_le_mul'
    · refine (prod_le_prod' fun p _ => fsmall p).trans ?_
      rw [prod_const]; apply pow_right_mono₀ hpos
      have sub' : A.filter (· ≤ Nat.sqrt (2*n)) ⊆ Icc 1 (Nat.sqrt (2*n)) := by
        intro p hp; obtain ⟨ha,h⟩ := mem_filter.mp hp
        exact mem_Icc.mpr ⟨(mem_filter.mp ha).2.one_lt.le,h⟩
      simpa using card_le_card sub'
    · refine le_trans ?_ (primorial_le_4_pow (2*n/3))
      change _ ≤ ∏ p ∈ A, p
      refine (prod_le_prod' fun p hp => (?_ : f p ≤ p)).trans ?_
      · obtain ⟨ha,hnle⟩ := mem_filter.mp hp
        exact (pow_right_mono₀ (mem_filter.mp ha).2.one_lt.le
          (Nat.factorization_choose_le_one (Nat.sqrt_lt'.mp (not_le.mp hnle)))).trans (pow_one p).le
      · exact prod_le_prod_of_subset_of_one_le' (filter_subset _ _) fun p hp _ => (mem_filter.mp hp).2.one_lt.le
  have prodB : (∏ p ∈ B, f p) ≤ (2*n)^B.card := by
    simpa only [prod_const] using prod_le_prod' (s := B) (fun p _ => fsmall p)
  rw [← eq,prod_union hdis]
  exact Nat.mul_le_mul prodA prodB

private theorem dyadic_real {x : ℝ} (hx : 8192 ≤ x) :
    (2*x)^(2*Real.sqrt (2*x)) * (4:ℝ)^(2*x/3) ≤ 4^x := by
  let y := x/16
  have hy : 512 ≤ y := by dsimp [y]; linarith
  have yp : 0 < y := by linarith
  have xp : 0 < x := by linarith
  have hxy : x = 16*y := by dsimp [y]; ring
  have l := Real.log_le_log (by positivity) (Bertrand.real_main_inequality hy)
  rw [Real.log_mul (by positivity) (by positivity),Real.log_mul yp.ne' (by positivity),
    Real.log_rpow (by positivity),Real.log_rpow (by norm_num),Real.log_rpow (by norm_num)] at l
  have lg : Real.log (2*x) ≤ 2*Real.log (2*y) := by
    have square : 2*x ≤ (2*y)^2 := by
      rw [hxy]; nlinarith only [mul_nonneg yp.le (by linarith : 0 ≤ y-8)]
    simpa only [Real.log_pow,Nat.cast_ofNat] using Real.log_le_log (by positivity) square
  have root : Real.sqrt (2*x) = 4*Real.sqrt (2*y) := by
    rw [show 2*x = (4:ℝ)^2*(2*y) by rw [hxy]; ring, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  rw [Real.log_mul (by positivity) (by positivity),Real.log_rpow (by positivity),
    Real.log_rpow (by norm_num),Real.log_rpow (by norm_num),root]
  have h' := mul_le_mul_of_nonneg_left lg (Real.sqrt_nonneg (2*y))
  rw [hxy] at h' ⊢
  nlinarith only [l,h',Real.log_nonneg (by linarith : 1 ≤ y)]

/-- At least `⌊√(2n)⌋` primes lie in `(n,2n]` once `n ≥ 8192`. -/
theorem dyadic_prime_count {n : ℕ} (hn : 8192 ≤ n) :
    Nat.sqrt (2*n) ≤ ((Ioc n (2*n)).filter Nat.Prime).card := by
  let m := ((Ioc n (2*n)).filter Nat.Prime).card
  let s := Nat.sqrt (2*n)
  have npos : 1 ≤ 2*n := by omega
  have bound : (2*n)^(2*s)*4^(2*n/3) ≤ 4^n := by
    rw [← @Nat.cast_le ℝ]
    simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,← Real.rpow_natCast]
    refine le_trans ?_ (dyadic_real (x := n) (by exact_mod_cast hn))
    apply mul_le_mul _ _ (by positivity) (by positivity)
    · apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast npos)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa [s] using (Real.nat_sqrt_le_real_sqrt (a := 2*n))
    · apply Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (4:ℝ))
      exact Nat.cast_div_le.trans (by push_cast; rfl)
  by_contra! h
  have hm : m+1 ≤ s := h
  have hb := binom_dyadic (n := n) (by omega)
  have up : n*n.centralBinom ≤ (2*n)^(2*s) * 4^(2*n/3) := calc
    _ ≤ (2*n)*((2*n)^s * 4^(2*n/3) * (2*n)^m) := Nat.mul_le_mul (by omega) hb
    _ = (2*n)^(s+m+1) * 4^(2*n/3) := by rw [pow_succ,pow_add]; ring
    _ ≤ _ := Nat.mul_le_mul_right _ (pow_right_mono₀ npos (by omega))
  exact not_le_of_gt (Nat.four_pow_lt_mul_centralBinom n (by omega)) (up.trans bound)

end DivisorAdj
