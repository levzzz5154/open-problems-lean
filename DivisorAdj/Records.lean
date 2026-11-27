import DivisorAdj.NewPrime
import DivisorAdj.Slots
import DivisorAdj.Prefix
import DivisorAdj.Tail
import Mathlib.Data.Finset.NatDivisors

/-! # A finite structural certificate for first occurrences in OEIS A251758

The certificate only uses the primes in the table and their ordered pairs. In
particular, neither the check nor its proof enumerates the divisors of the
proposed first index, much less the earlier indices.
-/

namespace DivisorAdj

open Finset

theorem prime_value {p : ℕ} (hp : p.Prime) : a p = p := by
  have hp1 := hp.one_lt
  have hs : divs p = [1,p] := by
    apply (sort_sorted_lt p.divisors).eq_of_mem_iff (show [1,p].Sorted (· < ·) by simp [List.Sorted,hp1])
    intro d; simp [hp.divisors]
  simp [a,hs,prodSum,pow_two,hp.pos]

theorem first_prime {p : ℕ} (hp : p.Prime) : IsLeast {n : ℕ | 2 ≤ n ∧ a n = p} p := by
  refine ⟨⟨hp.two_le,prime_value hp⟩,?_⟩
  intro n ⟨hn,e⟩
  exact e ▸ (a_le_minFactor hn).trans (Nat.minFac_le (by omega))

theorem prime_square_value {p : ℕ} (hp : p.Prime) : a (p^2) = p-1 := by
  have hp1 := hp.one_lt
  have hp2 : p < p^2 := by simpa [sq] using (lt_mul_of_one_lt_right hp.pos hp1)
  have hs : divs (p^2) = [1,p,p^2] := by
    apply (sort_sorted_lt _).eq_of_mem_iff (show [1,p,p^2].Sorted (· < ·) by
      simp [List.Sorted,hp1,hp2,hp1.trans hp2])
    intro d; simp [hp.divisors_sq,or_comm,or_left_comm,or_assoc]
  rw [a,hs]; simp only [prodSum,one_mul,add_zero]
  have hpos : 0 < p+p*p^2 := by have := hp.pos; positivity
  apply le_antisymm
  · have hh : (p^2)^2 / (p+p*p^2) < p := (Nat.div_lt_iff_lt_mul hpos).mpr (by nlinarith)
    omega
  · apply (Nat.le_div_iff_mul_le hpos).mpr
    obtain ⟨b,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne_zero
    simp only [Nat.succ_sub_one,Nat.succ_eq_add_one]
    ring_nf; omega

/-- If `p-1` is not prime, the first index giving `p-1` is `p²`, not the
first product of two different primes. This includes `p=2`. -/
theorem first_prime_pred {p : ℕ} (hp : p.Prime) (hc : ¬(p-1).Prime) :
    IsLeast {n : ℕ | 2 ≤ n ∧ a n = p-1} (p^2) := by
  have hp2 := hp.two_le
  refine ⟨⟨by nlinarith,prime_square_value hp⟩,?_⟩
  intro n ⟨hn,e⟩
  have hnp : ¬n.Prime := by intro h; exact hc ((prime_value h ▸ e) ▸ h)
  have hmin := a_le_minFactor hn
  have hpmin := Nat.minFac_prime (by omega : n ≠ 1)
  have he : n.minFac ≠ p-1 := fun h => hc (h ▸ hpmin)
  exact (Nat.pow_le_pow_left (show p ≤ n.minFac by omega) 2).trans (Nat.minFac_sq_le_self (by omega) hnp)

/-- Upper bound for the normalized sum when there are only `m` distinct
prime factors. `P` has one more entry, the prime needed to attain the record. -/
def tableCap {m : ℕ} (P : Fin (m+1) → ℕ) : ℚ :=
  let L := fun i : Fin m => P i.castSucc
  let p := P 0
  headCost (p^2) 1 ((List.finRange m).map L) + (m : ℚ) / ((p^2 : ℕ) : ℚ)^2 +
    pairWeightSum L * (1+1/((p : ℚ)-1))

/-- All conditions are finite and rational, including both prime-gap checks.
The last strict inequality uses only the consecutive *primes* of the witness. -/
def TableChecks {m : ℕ} (k : ℕ) (P : Fin (m+1) → ℕ) : Prop :=
  (∀ i, (P i).Prime) ∧ (∀ i : Fin m, P i.castSucc < P i.succ) ∧
  (∀ p ∈ Ico k (P 0), ¬ p.Prime) ∧
  (∀ i : Fin m, ∀ p ∈ Ioo (P i.castSucc) (P i.succ), ¬ p.Prime) ∧
  (∀ i : Fin m, P i.castSucc < (P 0)^2) ∧
  ((k : ℚ)+1) * tableCap P < 1 ∧
  1 < ((k : ℚ)+1) * recipSum (1 :: (List.finRange (m+1)).map P)

instance {m : ℕ} (k : ℕ) (P : Fin (m+1) → ℕ) : Decidable (TableChecks k P) := by
  unfold TableChecks; infer_instance

theorem first_of_table {m k : ℕ} [NeZero m] {P : Fin (m+1) → ℕ} (c : TableChecks k P) :
    IsLeast {n : ℕ | 2 ≤ n ∧ a n = k} (∏ i, P i) := by
  obtain ⟨prime,inc,initial,gaps,cut,tiny,large⟩ := c
  have mono : StrictMono P := Fin.strictMono_iff_lt_succ.mpr inc
  let L (i : Fin m) := P i.castSucc
  let N := ∏ i, P i
  let n₀ := ∏ i, L i
  let q := P (Fin.last m)
  have lower (i : Fin m) : P 0 ≤ L i := mono.monotone (Fin.zero_le _)
  have lmono : StrictMono L := fun _ _ h => mono (Fin.castSucc_lt_castSucc_iff.mpr h)
  have next (i : Fin m) (p : ℕ) (hp : p.Prime) (h : P i.castSucc < p) : P i.succ ≤ p := by
    by_contra! hh; exact gaps i p (mem_Ioo.mpr ⟨h,hh⟩) hp
  have below {n : ℕ} (hn : 2 ≤ n) (hsmall : n < N) (hmin : ∀ p ∈ n.primeFactors, P 0 ≤ p) : k < a n := by
    obtain ⟨big,pack⟩ := rank_threshold_of_table P next (by omega : 0 < n) hmin
    have hcard : n.primeFactors.card ≤ m := by
      by_contra! h; exact (not_le_of_gt hsmall) (big h)
    obtain ⟨s⟩ := pack hcard
    have hp := prefix_bound_table (by omega : 0 < n) s (prime 0).two_le lower cut lmono
    have ht := compositeWeight_le_of_slots (by omega : 0 < n) s (prime 0).two_le lower
    have bound : recipSum (divs n) ≤ tableCap P := hp.trans (add_le_add_left ht _)
    have hs : 0 ≤ recipSum (divs n) := by rw [divisor_steps]; apply sum_nonneg; intros; unfold weight; positivity
    by_contra! he
    have leK : (a n : ℚ)+1 ≤ (k : ℚ)+1 := by exact_mod_cast Nat.succ_le_succ he
    exact lt_irrefl (1 : ℚ) (((floor_recipSum hn).2.trans_le
      (mul_le_mul leK bound hs (by positivity))).trans tiny)
  have npos : 0 < N := Finset.prod_pos fun i _ => (prime i).pos
  have n₀pos : 0 < n₀ := Finset.prod_pos fun i _ => (prime i.castSucc).pos
  have hn : 2 ≤ N := (prime 0).two_le.trans (Nat.le_of_dvd npos (dvd_prod_of_mem P (mem_univ 0)))
  have hn₀ : 2 ≤ n₀ := (prime (0 : Fin m).castSucc).two_le.trans (Nat.le_of_dvd n₀pos (dvd_prod_of_mem L (mem_univ 0)))
  have eq : N = n₀*q := Fin.prod_univ_castSucc P
  have hlt : n₀ < N := eq ▸ lt_mul_of_one_lt_right n₀pos (prime _).one_lt
  have fromTable {p : ℕ} (h : p ∈ n₀.primeFactors) : ∃ i : Fin m, L i = p := by
    obtain ⟨hp,hd,_⟩ := Nat.mem_primeFactors.mp h
    obtain ⟨i,_,hi⟩ := (hp.prime.dvd_finset_prod_iff L).mp hd
    exact ⟨i,((prime i.castSucc).dvd_iff_eq hp.ne_one).mp hi⟩
  have before := below hn₀ hlt (fun p hp => by obtain ⟨i,rfl⟩ := fromTable hp; exact lower i)
  have step := (new_prime_step hn₀ (prime (Fin.last m)) (fun p hp => by
    obtain ⟨i,rfl⟩ := fromTable hp; exact mono i.castSucc_lt_last)).2
  change a n₀ ≤ a (n₀*q)+1 at step
  rw [← eq] at step
  have hsort : (1 :: (List.finRange (m+1)).map P).Sorted (· < ·) := by
    refine List.pairwise_cons.mpr ⟨?_,List.pairwise_map.mpr ((List.pairwise_lt_finRange _).imp fun h => mono h)⟩
    intro p hp; obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp; exact (prime i).one_lt
  have hs := recipSum_le_divs (n := N) hsort (by
    intro p hp
    apply (mem_sort (· ≤ ·)).mpr
    apply Nat.mem_divisors.mpr ⟨_,npos.ne'⟩
    rcases List.mem_cons.mp hp with rfl|h
    · exact one_dvd _
    · obtain ⟨i,_,rfl⟩ := List.mem_map.mp h; exact dvd_prod_of_mem P (mem_univ i))
  have hright : a N ≤ k := by
    by_contra! h
    have hS : 0 ≤ recipSum (divs N) := by rw [divisor_steps]; apply sum_nonneg; intros; unfold weight; positivity
    have hk : (k : ℚ)+1 ≤ (a N : ℚ) := by exact_mod_cast h
    have := large.trans_le (mul_le_mul_of_nonneg_left hs (by positivity))
    exact lt_irrefl (1 : ℚ) ((this.trans_le (mul_le_mul_of_nonneg_right hk hS)).trans_le (floor_recipSum hn).1)
  refine ⟨⟨hn,by change a N = k; omega⟩,?_⟩
  intro n ⟨hn',he⟩
  by_contra! h
  have ymin := a_le_minFactor hn'
  have hf (p : ℕ) (hp : p ∈ n.primeFactors) : P 0 ≤ p := by
    obtain ⟨hp,hd,_⟩ := Nat.mem_primeFactors.mp hp
    have hkp := ymin.trans (Nat.minFac_le_of_dvd hp.two_le hd)
    by_contra! hh; exact initial p (mem_Ico.mpr ⟨by omega,hh⟩) hp
  have := below hn' h hf
  omega

end DivisorAdj
