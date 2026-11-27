import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith

/-! A sparse prime grid bounds the distance to the next prime on a whole band.
A second, increasing list of primes gives a lower bound on the size of every
relevant prime interval on that band. Neither list has to contain all primes. -/

namespace DivisorAdj.Grid

/-- The least prime above `k` (inclusively) satisfies the required count inequality. -/
def DenseAt (k : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ k ≤ p ∧ (∀ r : ℕ, r.Prime → k ≤ r → p ≤ r) ∧
    4*p*(p-(k+1)) < ((Finset.Ioc p (2*p)).filter Nat.Prime).card*(k+1)

def Band (a b : ℕ) : Prop := ∀ k, a ≤ k → k ≤ b → DenseAt k

theorem join {a b c : ℕ} (h : Band a b) (h' : Band (b+1) c) : Band a c := by
  intro k h₁ h₂
  by_cases hk : k ≤ b
  · exact h k h₁ hk
  · exact h' k (by omega) h₂

/-- A single GCD rules out all possible small prime divisors at once. -/
private theorem prime_of_gcd {n bound fac : ℕ} (hf : fac = bound.factorial)
    (h : 1 < n ∧ n ≤ bound^2 ∧ n.gcd fac = 1) : n.Prime := by
  obtain ⟨hn, hsq, hcop⟩ := h
  have hsmall := (Nat.coprime_factorial_iff (m := n) (n := bound) (by omega)).mp
    (show n.Coprime bound.factorial from hf ▸ hcop)
  by_contra hnot
  have hmin := Nat.minFac_sq_le_self (by omega : 0 < n) hnot
  have hbig := Nat.pow_le_pow_left (show bound+1 ≤ n.minFac from hsmall) 2
  nlinarith

-- Quote the numerals once; the identities justifying them are checked below.
local elab "factorial%" n:num : term => return Lean.mkNatLit n.getNat.factorial

private def fac128 : ℕ := factorial% 128
private def fac1024 : ℕ := factorial% 1024

set_option maxRecDepth 4096 in
private theorem fac1024_eq : fac1024 = Nat.factorial 1024 := by decide +kernel
private theorem fac128_eq : fac128 = Nat.factorial 128 := by decide +kernel

private def good (n : ℕ) : Bool :=
  if n ≤ 128^2 then decide (1 < n ∧ n.gcd fac128 = 1)
  else decide (1 < n ∧ n ≤ 1024^2 ∧ n.gcd fac1024 = 1)

private theorem good_sound {n : ℕ} (h : good n = true) : n.Prime := by
  unfold good at h
  split at h
  · rename_i hl
    obtain ⟨hp, hc⟩ := of_decide_eq_true h
    exact prime_of_gcd fac128_eq ⟨hp, hl, hc⟩
  · exact prime_of_gcd fac1024_eq (of_decide_eq_true h)

/-- A grid point `q` covers the as yet uncovered integers `a,...,q`. -/
def grid : ℕ → ℕ → ℕ → List ℕ → Bool
  | a, b, _, [] => decide (b < a)
  | a, b, g, q::qs => decide (a ≤ q ∧ q ≤ a+g) && good q && grid (q+1) b g qs

private theorem grid_sound {a b g k : ℕ} {xs : List ℕ} (h : grid a b g xs = true)
    (hak : a ≤ k) (hkb : k ≤ b) : ∃ q, Nat.Prime q ∧ k ≤ q ∧ q ≤ k+g := by
  induction xs generalizing a with
  | nil => simp [grid] at h; omega
  | cons q qs ih =>
    simp only [grid, Bool.and_eq_true, decide_eq_true_eq] at h
    by_cases hq : k ≤ q
    · exact ⟨q, good_sound h.1.2, hq, by have := h.1.1.2; omega⟩
    · exact ih h.2 (by omega)

/-- Check an increasing list of primes inside the common interval `(l,u]`. -/
def sample : ℕ → ℕ → List ℕ → Bool
  | _, _, [] => true
  | l, u, q::qs => decide (l < q ∧ q ≤ u) && good q && sample q u qs

private theorem sample_sound {l u : ℕ} {xs : List ℕ} (h : sample l u xs = true) :
    xs.Nodup ∧ ∀ q ∈ xs, l < q ∧ q ≤ u ∧ Nat.Prime q := by
  induction xs generalizing l with
  | nil => simp
  | cons q qs ih =>
    simp only [sample, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hd, hm⟩ := ih h.2
    refine ⟨List.nodup_cons.mpr ⟨fun hh => (lt_irrefl q) (hm q hh).1, hd⟩, ?_⟩
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact ⟨h.1.1.1, h.1.1.2, good_sound h.1.2⟩
    · exact ⟨h.1.1.1.trans (hm t ht).1, (hm t ht).2⟩

/-- The only numerical hypotheses on a band are checked on its two sparse lists. -/
theorem certified {a b g : ℕ} (xs ys : List ℕ) (hx : grid a b g xs = true)
    (hy : sample (b+g) (2*a) ys = true)
    (hcost : 4*(b+g)*(g-1) < ys.length*(a+1)) : Band a b := by
  intro k hak hkb
  obtain ⟨q, hq, hkq, hqg⟩ := grid_sound hx hak hkb
  let ex : ∃ p, Nat.Prime p ∧ k ≤ p := ⟨q, hq, hkq⟩
  let p := Nat.find ex
  obtain ⟨hp, hkp⟩ := Nat.find_spec ex
  have least (r : ℕ) (hr : r.Prime) (hkr : k ≤ r) : p ≤ r := Nat.find_min' ex ⟨hr, hkr⟩
  have hpq := least q hq hkq
  obtain ⟨hn, hs⟩ := sample_sound hy
  have sub : ys.toFinset ⊆ (Finset.Ioc p (2*p)).filter Nat.Prime := by
    intro r hr
    obtain ⟨hl, hu, hrp⟩ := hs r (List.mem_toFinset.mp hr)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, by change k ≤ p at hkp; omega⟩, hrp⟩
  have count := Finset.card_le_card sub
  rw [List.toFinset_card_of_nodup hn] at count
  refine ⟨p, hp, hkp, least, ?_⟩
  calc
    4*p*(p-(k+1)) ≤ 4*(b+g)*(g-1) := Nat.mul_le_mul (by omega) (by omega)
    _ < ys.length*(a+1) := hcost
    _ ≤ _ := Nat.mul_le_mul count (by omega)

end DivisorAdj.Grid
