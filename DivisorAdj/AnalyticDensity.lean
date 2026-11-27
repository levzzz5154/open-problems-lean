import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Tactic

/-! # The analytic input for Wilson's primorial representation

`Dusart66` is precisely the common integer range of the two inequalities in
Pierre Dusart, *Estimates of some functions over primes without R.H.*, Theorem
6.9, equation (6.6), p. 9: https://arxiv.org/pdf/1002.0442#page=9 .
It is an explicit hypothesis, not a Lean axiom or a claimed formalization of
Dusart's proof. No separate short-interval or prime-gap theorem is needed.
-/

namespace DivisorAdj

open Finset Real

def Dusart66 : Prop := ∀ x : ℕ, 60184 ≤ x →
  (x : ℝ)/(log (x : ℝ)-1) ≤ (x.primeCounting : ℝ) ∧
  (x.primeCounting : ℝ) ≤ (x : ℝ)/(log (x : ℝ)-11/10)

private theorem prime_count_add {a b : ℕ} (h : a ≤ b) :
    a.primeCounting + ((Ioc a b).filter Nat.Prime).card = b.primeCounting := by
  let A := (range (a+1)).filter Nat.Prime
  let B := (Ioc a b).filter Nat.Prime
  have he : (range (b+1)).filter Nat.Prime = A ∪ B := by
    ext x
    simp only [A,B,mem_filter,mem_union,mem_range,mem_Ioc]
    constructor
    · rintro ⟨hx,hp⟩; by_cases ha : x ≤ a
      · exact Or.inl ⟨by omega,hp⟩
      · exact Or.inr ⟨⟨by omega,by omega⟩,hp⟩
    · rintro (⟨hx,hp⟩|⟨⟨_,hx⟩,hp⟩) <;> exact ⟨by omega,hp⟩
  have hd : Disjoint A B := by
    apply disjoint_left.mpr; intro x hx hy
    have h1 := mem_range.mp (mem_filter.mp hx).1
    have h2 := (mem_Ioc.mp (mem_filter.mp hy).1).1
    omega
  simp only [Nat.primeCounting,Nat.primeCounting',Nat.count_eq_card_filter_range]
  rw [he,card_union_of_disjoint hd]

/-- Large-case prime inequality, derived from prime counts alone. -/
theorem analytic_prime_density (H : Dusart66) {k p : ℕ} (hk : 60184 ≤ k) (hkp : k ≤ p)
    (hfirst : ∀ r : ℕ, r.Prime → k ≤ r → p ≤ r) :
    4*p*(p-(k+1)) < ((Ioc p (2*p)).filter Nat.Prime).card*(k+1) := by
  let d := p-(k+1)
  let u := k+d
  let M := ((Ioc p (2*p)).filter Nat.Prime).card
  have hu : k ≤ u := Nat.le_add_right ..
  have eu : (u : ℝ) = (k : ℝ)+d := by simp [u]
  have kp : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have pp : 0 < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
  have up : 0 < (u : ℝ) := by exact_mod_cast (show 0 < u by omega)
  have lk : 8 ≤ log (k : ℝ) := by
    have htwo : (2 : ℝ)^12 ≤ k := by norm_num; exact_mod_cast (show 4096 ≤ k by omega)
    have h := log_le_log (by norm_num : 0 < (2 : ℝ)^12) htwo
    rw [log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith [log_two_gt_d9]
  have lp := lk.trans (log_le_log kp (by exact_mod_cast hkp : (k : ℝ) ≤ p))
  have lu := lk.trans (log_le_log kp (by exact_mod_cast hu : (k : ℝ) ≤ u))
  have hem : (Ioc k u).filter Nat.Prime = ∅ := by
    apply eq_empty_of_forall_not_mem
    intro r hr
    obtain ⟨hi,hpr⟩ := mem_filter.mp hr
    obtain ⟨hkr,hru⟩ := mem_Ioc.mp hi
    have h := hfirst r hpr hkr.le
    dsimp [u,d] at hru
    omega
  have eqcount : u.primeCounting = k.primeCounting := by
    have h := prime_count_add hu
    simpa [hem] using h.symm
  have loggap : (k : ℝ)*(log (u : ℝ)-log (k : ℝ)) ≤ d := by
    have h := log_le_sub_one_of_pos (div_pos up kp)
    rw [log_div up.ne' kp.ne'] at h
    calc
      _ ≤ (k : ℝ)*((u : ℝ)/k-1) := mul_le_mul_of_nonneg_left h kp.le
      _ = _ := by rw [eu]; field_simp
  have cmp : (u : ℝ)/(log (u : ℝ)-1) ≤ (k : ℝ)/(log (k : ℝ)-11/10) := by
    calc
      _ ≤ (u.primeCounting : ℝ) := (H u (hk.trans hu)).1
      _ = (k.primeCounting : ℝ) := by rw [eqcount]
      _ ≤ _ := (H k hk).2
  have cross := (div_le_div_iff₀ (by linarith : 0 < log (u : ℝ)-1)
    (by linarith : 0 < log (k : ℝ)-11/10)).mp cmp
  have small : (d : ℝ)*(10*log (k : ℝ)-21) ≤ k := by
    rw [eu] at cross loggap
    nlinarith only [cross,loggap]
  have two_d : 2*d ≤ k := by
    have ht : (2 : ℝ)*d ≤ k := by
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) d) (by linarith : 0 ≤ 10*log (k : ℝ)-21-2)]
    exact_mod_cast ht
  have hpk : p ≤ 2*k := by dsimp [d] at two_d; omega
  have logp : log (p : ℝ) ≤ log (k : ℝ)+1 := calc
    _ ≤ log (2*(k : ℝ)) := log_le_log pp (by exact_mod_cast hpk)
    _ ≤ _ := by rw [log_mul (by norm_num) kp.ne']; linarith [log_two_lt_d9]
  have hlog2 : log (2*(p : ℝ)) = log 2+log (p : ℝ) := log_mul (by norm_num) pp.ne'
  have boundP := (le_div_iff₀ (by linarith : 0 < log (p : ℝ)-11/10)).mp (H p (hk.trans hkp)).2
  have Pupper : 4*(p.primeCounting : ℝ)*log (p : ℝ) ≤ 5*p := by
    nlinarith only [boundP, mul_le_mul_of_nonneg_left (by linarith : 4*log (p : ℝ) ≤ 5*(log (p : ℝ)-11/10))
      (Nat.cast_nonneg (α := ℝ) p.primeCounting)]
  have htlo := (H (2*p) (by omega)).1
  push_cast at htlo
  have Plo := (div_le_iff₀ (by linarith [log_two_gt_d9] : 0 < log (2*(p : ℝ))-1)).mp htlo
  have Plo' : 2*(p : ℝ) ≤ ((2*p).primeCounting : ℝ)*log (p : ℝ) := Plo.trans <|
    mul_le_mul_of_nonneg_left (by linarith [log_two_lt_d9]) (by positivity)
  have add : (p.primeCounting : ℝ) + M = (2*p).primeCounting := by
    exact_mod_cast prime_count_add (a := p) (b := 2*p) (by omega)
  rw [← add] at Plo'
  have count : 3*(p : ℝ) ≤ 4*M*log (p : ℝ) := by nlinarith only [Plo',Pupper]
  have Mpos : 0 < (M : ℝ) := by
    by_contra! e
    have : (M : ℝ) = 0 := le_antisymm e (Nat.cast_nonneg _)
    rw [this] at count; linarith
  have compare : 16*log (p : ℝ) ≤ (5/2)*(10*log (k : ℝ)-21) := by linarith
  have tiny : 16*(d : ℝ)*log (p : ℝ) < 3*k := by
    nlinarith only [mul_le_mul_of_nonneg_left compare (Nat.cast_nonneg (α := ℝ) d),small,kp]
  have final : 4*(p : ℝ)*d < M*((k : ℝ)+1) := by
    nlinarith only [mul_le_mul_of_nonneg_right count (Nat.cast_nonneg (α := ℝ) d),
      mul_lt_mul_of_pos_left tiny Mpos,Mpos]
  exact_mod_cast final

end DivisorAdj
