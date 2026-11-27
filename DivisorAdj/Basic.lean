import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.List.Sort
import Mathlib.Tactic

/-! # Consecutive divisor products (OEIS A251758)

[Wilson's 2014 question](https://oeis.org/A251758) asks for the first index of 8.
All sums here are finite; the estimates use rational numbers only.
-/

namespace DivisorAdj

open Finset

def divs (n : ℕ) : List ℕ := n.divisors.sort (· ≤ ·)

def prodSum : List ℕ → ℕ
  | x :: y :: xs => x*y + prodSum (y :: xs)
  | _ => 0

def recipSum : List ℕ → ℚ
  | x :: y :: xs => 1 / ((x : ℚ)*y) + recipSum (y :: xs)
  | _ => 0

def a (n : ℕ) : ℕ := n^2 / prodSum (divs n)

theorem prodSum_pos {n : ℕ} (hn : 2 ≤ n) : 0 < prodSum (divs n) := by
  have hn0 : n ≠ 0 := by omega
  have hc : 1 < n.divisors.card := one_lt_card.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd _, hn0⟩,
    n, Nat.mem_divisors.mpr ⟨dvd_rfl, hn0⟩, by omega⟩
  have hl : 1 < (divs n).length := by simpa [divs] using hc
  cases h : divs n with
  | nil => simp [h] at hl
  | cons x xs =>
    cases xs with
    | nil => simp [h] at hl
    | cons y ys =>
      have hp (d : ℕ) (hd : d ∈ divs n) := Nat.pos_of_mem_divisors ((mem_sort (· ≤ ·)).mp hd)
      exact Nat.add_pos_left (Nat.mul_pos (hp x (by simp [h])) (hp y (by simp [h]))) _

/-- An increasing list charges each adjacent reciprocal product to the inverse
square of the earlier entry. -/
theorem recipSum_square_bound : ∀ l : List ℕ, l.Sorted (· < ·) → (∀ d ∈ l, 0 < d) →
    recipSum l ≤ ∑ d ∈ l.toFinset, 1 / (d:ℚ)^2
  | [], _, _ => by simp [recipSum]
  | [x], _, _ => by simp [recipSum]
  | x :: y :: t, hs, hp => by
    have hxy : x < y := List.rel_of_pairwise_cons hs List.mem_cons_self
    have hx := hp x List.mem_cons_self
    have hr := recipSum_square_bound (y::t) (List.sorted_cons.mp hs).2 (fun d hd => hp d (.tail _ hd))
    have hnot : x ∉ (y::t).toFinset := fun h => (lt_irrefl x) (List.rel_of_pairwise_cons hs (List.mem_toFinset.mp h))
    rw [List.toFinset_cons, sum_insert hnot, recipSum]
    apply add_le_add _ hr
    apply one_div_le_one_div_of_le (by positivity)
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hxy.le) (by positivity)

/-- Telescope `1/m² ≤ 1/(m−1) − 1/m` on any positive integer tail. -/
theorem inverse_square_tail (b k : ℕ) (hb : 0 < b) :
    ∑ m ∈ Ico (b+1) (k+(b+1)), 1 / (m:ℚ)^2 ≤ 1/(b:ℚ) - 1/((k:ℚ)+b) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show k.succ+(b+1) = (k+(b+1))+1 by omega, sum_Ico_succ_top (by omega : b+1 ≤ k+(b+1))]
    push_cast
    have hb' : (0:ℚ) < b := by exact_mod_cast hb
    have hp : (0:ℚ) < (k:ℚ)+b := by positivity
    have hq : (0:ℚ) < (k:ℚ)+(b+1) := by positivity
    have hs : 1 / ((k:ℚ)+(b+1))^2 ≤ 1/((k:ℚ)+b) - 1/((k:ℚ)+(b+1)) := by
      calc
        _ ≤ 1 / (((k:ℚ)+b)*((k:ℚ)+(b+1))) :=
          one_div_le_one_div_of_le (mul_pos hp hq) (by nlinarith)
        _ = _ := by field_simp [hp.ne', hq.ne']
    rw [show (k:ℚ)+1+b = k+(b+1) by ring]
    linarith

def firstPrime : Fin 7 → ℕ := ![11, 13, 17, 19, 23, 29, 31]

/-- Distinct prime factors in increasing slots. A table entry bounds the
corresponding prime from below; the table need not divide `n`. -/
structure Slots {k : ℕ} (table : Fin k → ℕ) (n : ℕ) where
  slot : (p : n.primeFactors) → Fin k
  mono : StrictMono slot
  lower : ∀ p, table (slot p) ≤ p.val

def compositeWeight (n : ℕ) : ℚ :=
  ∑ d ∈ n.divisors.filter (fun d => 1 < d ∧ ¬ d.Prime), 1 / (d : ℚ)^2

end DivisorAdj
