import DivisorAdj.Basic

namespace DivisorAdj

open Finset

private theorem firstPrime_min (i : Fin 7) : 11 ≤ firstPrime i := by
  fin_cases i <;> decide

private theorem divisor_lower {k n m p₀ : ℕ} {L : Fin k → ℕ}
    (hL : ∀ i, p₀ ≤ L i) (hn : 0 < n) (s : Slots L n)
    (hm : m ∣ n) (h : m ≠ 1) : p₀ ≤ m := by
  let p : n.primeFactors := ⟨m.minFac, Nat.mem_primeFactors.mpr
    ⟨Nat.minFac_prime h, (Nat.minFac_dvd m).trans hm, hn.ne'⟩⟩
  exact (hL (s.slot p)).trans ((s.lower p).trans
    (Nat.minFac_le (Nat.pos_of_dvd_of_pos hm hn)))

private theorem divisor_sum_bound {k n p₀ : ℕ} {L : Fin k → ℕ}
    (hn : 0 < n) (s : Slots L n) (hp₀ : 2 ≤ p₀) (hL : ∀ i, p₀ ≤ L i) :
    ∑ m ∈ n.divisors, 1 / (m : ℚ)^2 ≤ 1 + 1 / ((p₀ : ℚ) - 1) := by
  have hsub : n.divisors ⊆ insert 1 (Ico p₀ (n+p₀)) := by
    intro m hm
    by_cases h : m = 1
    · simp [h]
    · have hmn := Nat.dvd_of_mem_divisors hm
      exact mem_insert_of_mem (mem_Ico.mpr ⟨divisor_lower hL hn s hmn h,
        by have := Nat.le_of_dvd hn hmn; omega⟩)
  calc
    _ ≤ ∑ m ∈ insert 1 (Ico p₀ (n+p₀)), 1 / (m : ℚ)^2 :=
      sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    _ ≤ _ := by
      rw [sum_insert (by simp [show ¬ p₀ ≤ 1 by omega])]
      norm_num only [Nat.cast_one, one_pow, div_one]
      have ht := inverse_square_tail (p₀-1) n (by omega)
      rw [show p₀-1+1 = p₀ by omega, Nat.cast_sub (by omega : 1 ≤ p₀), Nat.cast_one] at ht
      have hpos : 0 < (p₀ : ℚ) - 1 := sub_pos.mpr (by exact_mod_cast (show 1 < p₀ by omega))
      linarith [show (0 : ℚ) ≤ 1 / ((n : ℚ)+((p₀ : ℚ)-1)) by positivity]

/-- Split off the least prime twice, retaining their order, including repeated primes. -/
private theorem factor_pair {d n : ℕ} (hn : 0 < n) (hdn : d ∣ n) (hd : 1 < d)
    (hc : ¬d.Prime) : ∃ (p q : n.primeFactors) (m : ℕ),
      p ≤ q ∧ m ∈ n.divisors ∧ d = p.val*q.val*m := by
  let p := d.minFac
  let r := d / p
  let q := r.minFac
  let m := r / q
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpd : p ∣ d := Nat.minFac_dvd _
  have hrd : r ∣ d := Nat.div_dvd_of_dvd hpd
  have hr : r ≠ 1 := by
    have := Nat.minFac_le_div (by omega : 0 < d) hc
    have := hp.two_le
    change d / d.minFac ≠ 1
    change 2 ≤ d.minFac at ‹2 ≤ p›
    omega
  have hq : q.Prime := Nat.minFac_prime hr
  have hqr : q ∣ r := Nat.minFac_dvd _
  have hqd := hqr.trans hrd
  refine ⟨⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpd.trans hdn, hn.ne'⟩⟩,
    ⟨q, Nat.mem_primeFactors.mpr ⟨hq, hqd.trans hdn, hn.ne'⟩⟩, m,
    Nat.minFac_le_of_dvd hq.two_le hqd,
    Nat.mem_divisors.mpr ⟨(Nat.div_dvd_of_dvd hqr).trans (hrd.trans hdn), hn.ne'⟩, ?_⟩
  change d = p*q*(r/q)
  rw [mul_assoc, Nat.mul_div_cancel' hqr, Nat.mul_div_cancel' hpd]

def orderedPairs (k : ℕ) := (univ : Finset (Fin k × Fin k)).filter fun ij => ij.1 ≤ ij.2

def pairWeight {k : ℕ} (L : Fin k → ℕ) (ij : Fin k × Fin k) : ℚ :=
  1 / ((L ij.1 : ℚ) * L ij.2)^2

/-- Sum over unordered pairs with repetition, counting the diagonal once. -/
def pairWeightSum {k : ℕ} (L : Fin k → ℕ) : ℚ :=
  ∑ ij ∈ orderedPairs k, pairWeight L ij

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem numerical_bound :
    pairWeightSum firstPrime * (11/10) ≤ 402/1000000 := by
  rw [pairWeightSum, orderedPairs, sum_filter, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, pairWeight, firstPrime,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num [Fin.le_def]

/-- Every composite divisor gives a distinct pair of ordered slots and a residual divisor. -/
theorem compositeWeight_le_of_slots {k n p₀ : ℕ} {L : Fin k → ℕ}
    (hn : 0 < n) (s : Slots L n) (hp₀ : 2 ≤ p₀) (hL : ∀ i, p₀ ≤ L i) :
    compositeWeight n ≤ pairWeightSum L * (1 + 1 / ((p₀ : ℚ) - 1)) := by
  classical
  let C := n.divisors.filter (fun d => 1 < d ∧ ¬ d.Prime)
  have hfac (d : C) := factor_pair hn (Nat.dvd_of_mem_divisors (mem_filter.mp d.property).1)
    (mem_filter.mp d.property).2.1 (mem_filter.mp d.property).2.2
  choose p q m hpq hm heq using hfac
  let key (d : C) := ((s.slot (p d), s.slot (q d)), m d)
  let W (x : (Fin k × Fin k) × ℕ) := pairWeight L x.1 * (1 / (x.2 : ℚ)^2)
  have hinj : Function.Injective key := by
    intro d e h
    have hp := s.mono.injective (congrArg (fun t : (Fin k × Fin k) × ℕ => t.1.1) h)
    have hq := s.mono.injective (congrArg (fun t : (Fin k × Fin k) × ℕ => t.1.2) h)
    have hr : m d = m e := congrArg Prod.snd h
    change p d = p e at hp
    change q d = q e at hq
    exact Subtype.ext ((heq d).trans (by rw [hp, hq, hr, ← heq e]))
  have hsub : C.attach.image key ⊆ orderedPairs k ×ˢ n.divisors := by
    intro x hx
    obtain ⟨d, _, rfl⟩ := mem_image.mp hx
    exact mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _, s.mono.monotone (hpq d)⟩, hm d⟩
  calc
    compositeWeight n = ∑ d ∈ C.attach, 1 / (d.val : ℚ)^2 := (sum_attach C _).symm
    _ ≤ ∑ d ∈ C.attach, W (key d) := by
      apply sum_le_sum
      intro d _
      have hl := Nat.mul_le_mul (Nat.mul_le_mul (s.lower (p d)) (s.lower (q d))) (le_refl (m d))
      rw [← heq d] at hl
      have h1 := hL (s.slot (p d))
      have h2 := hL (s.slot (q d))
      have h3 := Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors (hm d)) hn
      have hpos : 0 < L (s.slot (p d)) * L (s.slot (q d)) * m d :=
        Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) h3
      unfold W key pairWeight
      dsimp only
      rw [div_mul_div_comm, one_mul, ← mul_pow, ← Nat.cast_mul, ← Nat.cast_mul]
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.pow_le_pow_left hl 2)
    _ = ∑ x ∈ C.attach.image key, W x := (sum_image hinj.injOn).symm
    _ ≤ ∑ x ∈ orderedPairs k ×ˢ n.divisors, W x :=
      sum_le_sum_of_subset_of_nonneg hsub (by intros; dsimp [W, pairWeight]; positivity)
    _ = pairWeightSum L * ∑ m ∈ n.divisors, 1 / (m : ℚ)^2 := by
      rw [pairWeightSum, sum_product, sum_mul]
      simp only [W, mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (divisor_sum_bound hn s hp₀ hL)
      (sum_nonneg (by intros; unfold pairWeight; positivity))

theorem compositeWeight_le {n : ℕ} (hn : 0 < n) (s : Slots firstPrime n) :
    compositeWeight n ≤ (402 : ℚ)/1000000 := by
  have h := compositeWeight_le_of_slots hn s (by decide : 2 ≤ 11) firstPrime_min
  norm_num at h
  exact h.trans numerical_bound

end DivisorAdj
