import DivisorAdj.Records

/-! # Local certificates for Wilson's consecutive-prime representation -/

namespace DivisorAdj

open Finset

/-- Stop at `t`, using every prime from `k` through `t` inclusive. -/
def WilsonValue (k : ℕ) : Prop :=
  ∃ t, k ≤ t ∧ a (∏ p ∈ (Icc k t).filter Nat.Prime, p) = k

private abbrev primesIn (k t : ℕ) := (Icc k t).filter Nat.Prime

private theorem mem_primesIn {k t q : ℕ} : q ∈ primesIn k t ↔ k ≤ q ∧ q ≤ t ∧ q.Prime := by
  simp [primesIn, and_assoc]

private theorem run_pos (k t : ℕ) : 0 < ∏ p ∈ primesIn k t, p :=
  prod_pos fun _ h => (mem_primesIn.mp h).2.2.pos

private theorem run_two {k t : ℕ} (hne : (primesIn k t).Nonempty) :
    2 ≤ ∏ p ∈ primesIn k t, p := by
  obtain ⟨q,hq⟩ := hne
  exact (mem_primesIn.mp hq).2.2.two_le.trans
    (Nat.le_of_dvd (run_pos k t) (dvd_prod_of_mem id hq))

/-- The first nonempty interval gives its single prime; after that, each
extension either changes nothing or appends a fresh largest prime. -/
theorem wilson_of_endpoint {k t : ℕ} (hne : ((Icc k t).filter Nat.Prime).Nonempty)
    (hend : a (∏ p ∈ (Icc k t).filter Nat.Prime, p) ≤ k) : WilsonValue k := by
  change (primesIn k t).Nonempty at hne
  change a (∏ p ∈ primesIn k t, p) ≤ k at hend
  induction t with
  | zero =>
    obtain ⟨q,hq⟩ := hne
    obtain ⟨_,h,hp⟩ := mem_primesIn.mp hq
    have := hp.two_le; omega
  | succ t ih =>
    by_cases hq : t+1 ∈ primesIn k (t+1)
    · obtain ⟨hkq,_,hprime⟩ := mem_primesIn.mp hq
      have eq : primesIn k (t+1) = insert (t+1) (primesIn k t) := by
        ext r; simp only [mem_insert,mem_primesIn]; constructor
        · rintro ⟨h1,h2,h3⟩; by_cases e : r=t+1
          · exact Or.inl e
          · exact Or.inr ⟨h1,by omega,h3⟩
        · rintro (rfl|⟨h1,h2,h3⟩)
          · exact ⟨hkq,le_rfl,hprime⟩
          · exact ⟨h1,by omega,h3⟩
      have hn : t+1 ∉ primesIn k t := fun h => (Nat.not_succ_le_self t) (mem_primesIn.mp h).2.1
      rw [eq,prod_insert hn,mul_comm] at hend
      refine Or.elim (em (primesIn k t).Nonempty) (fun h => ?_) (fun h => ?_)
      · by_cases old : a (∏ p ∈ primesIn k t, p) ≤ k
        · exact ih h old
        have step := (new_prime_step (run_two h) hprime (fun r hr => by
          obtain ⟨hrp,hd,_⟩ := Nat.mem_primeFactors.mp hr
          obtain ⟨s,hs,hrs⟩ := (hrp.prime.dvd_finset_prod_iff id).mp hd
          have hs' := mem_primesIn.mp hs
          have : s = r := (hs'.2.2.dvd_iff_eq hrp.ne_one).mp hrs
          omega)).2
        refine ⟨t+1,hkq,?_⟩
        change a (∏ p ∈ primesIn k (t+1), p) = k
        rw [eq,prod_insert hn,mul_comm]; omega
      · have hem := not_nonempty_iff_eq_empty.mp h
        simp only [hem, prod_empty,one_mul,prime_value hprime] at hend
        refine ⟨t+1,hkq,?_⟩
        change a (∏ p ∈ primesIn k (t+1), p) = k
        rw [eq,prod_insert hn,hem,prod_empty,mul_one,prime_value hprime]
        exact le_antisymm hend hkq
    · have eq : primesIn k (t+1) = primesIn k t := by
        ext r; simp only [mem_primesIn]; constructor
        · rintro ⟨h1,h2,h3⟩
          have ne : r ≠ t+1 := by
            rintro rfl; exact hq (mem_primesIn.mpr ⟨h1,h2,h3⟩)
          exact ⟨h1,by omega,h3⟩
        · rintro ⟨h1,h2,h3⟩; exact ⟨h1,by omega,h3⟩
      exact ih (eq ▸ hne) (eq ▸ hend)

/-- Any strictly increasing list of primes inside the proposed interval can
certify coverage. Skipped primes are included in the actual Wilson product. -/
theorem wilson_of_prefix {k t : ℕ} (xs : List ℕ) (hs : xs.Sorted (· < ·))
    (hm : ∀ q ∈ xs, q.Prime ∧ k ≤ q ∧ q ≤ t)
    (hlarge : 1 < ((k : ℚ)+1) * recipSum (1 :: xs)) : WilsonValue k := by
  have hne : (primesIn k t).Nonempty := by
    cases xs with
    | nil => norm_num [recipSum] at hlarge
    | cons q qs =>
      obtain ⟨hp,hk,ht⟩ := hm q List.mem_cons_self
      exact ⟨q,mem_primesIn.mpr ⟨hk,ht,hp⟩⟩
  let n := ∏ p ∈ primesIn k t, p
  have hsort : (1 :: xs).Sorted (· < ·) :=
    List.pairwise_cons.mpr ⟨fun q h => (hm q h).1.one_lt,hs⟩
  have bound := recipSum_le_divs (n := n) hsort (by
    intro r hr
    apply (mem_sort (· ≤ ·)).mpr
    apply Nat.mem_divisors.mpr ⟨_,(run_pos k t).ne'⟩
    rcases List.mem_cons.mp hr with rfl|hr
    · exact one_dvd _
    · obtain ⟨hp,hk,ht⟩ := hm r hr
      exact dvd_prod_of_mem id (mem_primesIn.mpr ⟨hk,ht,hp⟩))
  apply wilson_of_endpoint hne
  change a n ≤ k
  apply le_of_not_gt
  intro h
  have hh : (k : ℚ)+1 ≤ a n := by exact_mod_cast h
  have hpos : 0 ≤ recipSum (divs n) := by
    rw [divisor_steps]; apply sum_nonneg; intros; unfold weight; positivity
  exact lt_irrefl (1 : ℚ) ((hlarge.trans_le (mul_le_mul_of_nonneg_left bound (by positivity))).trans_le
    ((mul_le_mul_of_nonneg_right hh hpos).trans (floor_recipSum (run_two hne)).1))

private theorem tail_lower (B : ℕ) (xs : List ℕ) (x : ℕ) (hx : 0 < x ∧ x ≤ B)
    (hm : ∀ q ∈ xs, 0 < q ∧ q ≤ B) :
    (xs.length : ℚ) / (B : ℚ)^2 ≤ recipSum (x :: xs) := by
  induction xs generalizing x with
  | nil => simp [recipSum]
  | cons y ys ih =>
    have hy := hm y List.mem_cons_self
    have he : 1 / (B : ℚ)^2 ≤ 1 / ((x : ℚ)*y) := by
      apply one_div_le_one_div_of_le (by exact_mod_cast Nat.mul_pos hx.1 hy.1)
      rw [sq]; exact_mod_cast Nat.mul_le_mul hx.2 hy.2
    have ht := ih y hy (fun q h => hm q (.tail _ h))
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one,add_div,recipSum]
    linarith

/-- A count of primes in `(p,2p]` suffices: after the first edge `1/p`,
each of the remaining edges contributes at least `1/(4p²)`. -/
theorem wilson_of_density {k p : ℕ} (hp : p.Prime) (hkp : k ≤ p)
    (hd : 4*p*(p-(k+1)) < ((Ioc p (2*p)).filter Nat.Prime).card*(k+1)) : WilsonValue k := by
  let s := (Ioc p (2*p)).filter Nat.Prime
  let xs := s.sort (· ≤ ·)
  have hm (q : ℕ) (hq : q ∈ xs) : p < q ∧ q ≤ 2*p ∧ q.Prime := by
    simpa [xs,s,and_assoc] using hq
  apply wilson_of_prefix (t := 2*p) (p :: xs)
    (List.pairwise_cons.mpr ⟨fun q h => (hm q h).1,sort_sorted_lt s⟩)
  · intro q h; rcases List.mem_cons.mp h with rfl|h
    · exact ⟨hp,hkp,by omega⟩
    · obtain ⟨h1,h2,h3⟩ := hm q h; exact ⟨h3,by omega,h2⟩
  · have ht := tail_lower (2*p) xs p ⟨hp.pos,by omega⟩ (fun q h =>
      ⟨hp.pos.trans (hm q h).1,(hm q h).2.1⟩)
    have hl : xs.length = s.card := by simp [xs]
    rw [hl] at ht
    push_cast at ht
    have hpp : 0 < (p : ℚ) := by exact_mod_cast hp.pos
    have hsub : (p : ℚ)-((k : ℚ)+1) ≤ (p-(k+1) : ℕ) := by
      by_cases h : k+1 ≤ p
      · simp [Nat.cast_sub h]
      · have : (p : ℚ) ≤ (k : ℚ)+1 := by exact_mod_cast (show p ≤ k+1 by omega)
        have : p-(k+1) = 0 := by omega
        simp [this]; linarith
    have hd' : 4*(p : ℚ)*(p-(k+1) : ℕ) < (s.card : ℚ)*((k : ℚ)+1) := by exact_mod_cast hd
    have hx := (mul_le_mul_of_nonneg_left hsub (by positivity : 0 ≤ 4*(p : ℚ))).trans_lt hd'
    have hw : 1 < ((k : ℚ)+1)*(1/(p : ℚ)+(s.card : ℚ)/(2*(p : ℚ))^2) := by
      have e : ((k : ℚ)+1)*(1/(p : ℚ)+(s.card : ℚ)/(2*(p : ℚ))^2) =
          (((k : ℚ)+1)*(4*p+s.card))/(2*(p : ℚ))^2 := by field_simp; ring
      rw [e,lt_div_iff₀ (by positivity)]; nlinarith only [hx]
    simp only [recipSum, Nat.cast_one, one_mul]
    exact hw.trans_le (mul_le_mul_of_nonneg_left (add_le_add_left ht _) (by positivity))

end DivisorAdj
