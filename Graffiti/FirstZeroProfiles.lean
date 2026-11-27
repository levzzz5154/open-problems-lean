import Graffiti369
import Mathlib.Tactic.IntervalCases

/-! # A finite degree-sequence certificate for WoW II 368 and 369

A positive nonincreasing tree degree list on `n` vertices is a partition of
`n−2` after subtracting one from every entry and dropping the zeros. There
are only 11,731 such profiles in orders 3 through 28. Enumerate partitions,
not labeled trees. The only arithmetic facts used to reject a putative total
dominating set of size `b` are its minimum size, the parity-sensitive nonleaf
budget, and the sum of the `b` largest degrees. All computations are reduced
by the kernel; the enumeration-completeness argument is independent of them.
-/

namespace Graffiti.FirstZero

/-- Failure of a necessary condition for a total dominating set of size ≤ `b`. -/
def ExcludedBudget (n : ℕ) (ds : List ℕ) (b : ℕ) : Prop :=
  b < 2 ∨ b + 2 * (b / 2) < (ds.filter (fun d => 1 < d)).length + 2 ∨ (ds.take b).sum < n

private instance (n : ℕ) (ds : List ℕ) (b : ℕ) : Decidable (ExcludedBudget n ds b) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

private def touchesOne : List ℕ → Bool
  | [] => false
  | d :: xs => (xs.take d).contains 1

private theorem zero_of_touches {ds : List ℕ} (h : touchesOne ds = true) : 0 ∈ step ds := by
  cases ds with
  | nil => simp [touchesOne] at h
  | cons d xs =>
    have hm : 1 ∈ xs.take d := by simpa [touchesOne] using h
    rw [step, List.mem_insertionSort]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨1, hm, rfl⟩)

/-- A cap is harmless: exhaustion rejects the certificate rather than asserting a bound. -/
private def hit? : ℕ → List ℕ → Option ℕ
  | 0, _ => none
  | fuel + 1, ds => if touchesOne ds then some 1 else (hit? fuel (step ds)).map Nat.succ

private theorem hit_sound {fuel k : ℕ} {ds : List ℕ} (h : hit? fuel ds = some k) :
    0 < k ∧ 0 ∈ step^[k] ds := by
  induction fuel generalizing ds k with
  | zero => simp [hit?] at h
  | succ f ih =>
    by_cases ht : touchesOne ds = true
    · have eq : 1 = k := by simpa [hit?, ht] using h
      subst k
      exact ⟨by decide, by simpa using zero_of_touches ht⟩
    · cases e : hit? f (step ds) with
      | none => simp [hit?, ht, e] at h
      | some j =>
        have eq : j.succ = k := by simpa [hit?, ht, e] using h
        subst k
        exact ⟨Nat.zero_lt_succ _, by rw [Function.iterate_succ_apply]; exact (ih e).2⟩

private theorem count_pair_le (ds : List ℕ) {a b : ℕ} (hab : a ≠ b) :
    ds.count a + ds.count b ≤ ds.length := by
  induction ds with
  | nil => simp
  | cons x xs ih =>
    by_cases ha : x = a <;> by_cases hb : x = b <;>
      simp_all [List.count_cons] <;> omega

/-- When the leaves are a strict majority, computing the other counts is unnecessary. -/
private def modeCap (ds : List ℕ) : ℕ :=
  if ds.length < 2 * ds.count 1 then 1 else (modes ds).card

private theorem modes_le_cap (ds : List ℕ) : (modes ds).card ≤ modeCap ds := by
  unfold modeCap
  split
  · rename_i h
    have h1 : 1 ∈ ds := List.count_pos_iff.mp (by omega)
    have sub : modes ds ⊆ {1} := by
      intro d hd
      rw [Finset.mem_singleton]
      by_contra ne
      have hi := (Finset.mem_filter.mp hd).2 1 (List.mem_toFinset.mpr h1)
      have lo := count_pair_le ds ne
      omega
    simpa using Finset.card_le_card sub
  · exact le_rfl

private def budget (n : ℕ) (ds : List ℕ) (k : ℕ) : ℕ :=
  max k (modeCap ds + (n % 2) * k - 1)

private def check (n : ℕ) (ds : List ℕ) : Bool :=
  match hit? 15 ds with
  | none => false
  | some k => decide (ExcludedBudget n ds (budget n ds k))

private theorem check_sound {n : ℕ} {ds : List ℕ} (hc : check n ds = true) :
    ∃ b, firstZeroStep ds ≤ b ∧ (modes ds).card + (n % 2) * firstZeroStep ds ≤ b + 1 ∧
      ExcludedBudget n ds b := by
  cases e : hit? 15 ds with
  | none => simp [check, e] at hc
  | some k =>
    have hk : firstZeroStep ds ≤ k := Nat.sInf_le (s := {j : ℕ | 0 < j ∧ 0 ∈ step^[j] ds}) (hit_sound e)
    refine ⟨budget n ds k, hk.trans (le_max_left ..), ?_, by simpa [check, e] using hc⟩
    have hmul := Nat.mul_le_mul_left (n % 2) hk
    have hmode := modes_le_cap ds
    have hmax : modeCap ds + (n % 2) * k - 1 ≤ budget n ds k := le_max_right ..
    omega

/-- Choose each next positive excess in `1..min rem cap`; after the excess
runs out, the entire unfilled suffix consists of ones. `acc` is reversed. -/
private def visit (f : List ℕ → Bool) : ℕ → ℕ → ℕ → List ℕ → Bool
  | 0, rem, _, acc => if rem = 0 then f acc.reverse else true
  | slots + 1, rem, cap, acc =>
    if rem = 0 then f (acc.reverse ++ List.replicate (slots + 1) 1) else
      (List.range (min rem cap)).all fun j => visit f slots (rem - (j+1)) (j+1) ((j+2) :: acc)

private theorem length_le_sum (xs : List ℕ) (hp : ∀ x ∈ xs, 0 < x) : xs.length ≤ xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hp x List.mem_cons_self
    have hi := ih (fun a ha => hp a (List.mem_cons_of_mem _ ha))
    simp only [List.sum_cons, List.length_cons]; omega

private theorem ones_of_sum {xs : List ℕ} (hp : ∀ x ∈ xs, 0 < x) (hs : xs.sum = xs.length) :
    xs = List.replicate xs.length 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := hp x List.mem_cons_self
    have ht (a) (ha : a ∈ xs) := hp a (List.mem_cons_of_mem _ ha)
    have hi := length_le_sum xs ht
    simp only [List.sum_cons, List.length_cons] at hs
    rw [show x = 1 by omega]
    exact congrArg (1 :: ·) (ih ht (by omega))

private theorem visit_sound {f : List ℕ → Bool} (slots rem cap : ℕ) (acc xs : List ℕ)
    (hv : visit f slots rem cap acc = true) (hl : xs.length = slots) (hs : xs.sum = slots + rem)
    (hr : xs.Pairwise (· ≥ ·)) (hp : ∀ x ∈ xs, 0 < x) (hc : ∀ x ∈ xs, x ≤ cap + 1) :
    f (acc.reverse ++ xs) = true := by
  induction slots generalizing rem cap acc xs with
  | zero =>
    obtain rfl : xs = [] := List.length_eq_zero_iff.mp hl
    have eq : rem = 0 := by simpa using hs.symm
    simpa [visit, eq] using hv
  | succ s ih =>
    by_cases he : rem = 0
    · have eq : xs = List.replicate (s + 1) 1 := hl ▸ ones_of_sum hp (by omega)
      simpa only [eq, visit, he, if_pos rfl] using hv
    · cases xs with
      | nil => simp at hl
      | cons x xs =>
        have hlen : xs.length = s := by simpa using hl
        have hp' (a) (ha : a ∈ xs) := hp a (List.mem_cons_of_mem _ ha)
        have lo := length_le_sum xs hp'
        have upper := (List.pairwise_cons.mp hr).1
        have base := hp x List.mem_cons_self
        have capx := hc x List.mem_cons_self
        simp only [List.sum_cons] at hs
        have big : 2 ≤ x := by
          by_contra! h
          have eq : xs = List.replicate xs.length 1 := List.eq_replicate_of_mem (fun a ha => by
            have := upper a ha; have := hp' a ha; omega)
          have eqs := congrArg List.sum eq
          simp only [List.sum_replicate_nat, Nat.mul_one] at eqs
          omega
        have ix : x - 2 ∈ List.range (min rem cap) := List.mem_range.mpr (lt_min (by omega) (by omega))
        have hv' := List.all_eq_true.mp (show (List.range (min rem cap)).all (fun j =>
          visit f s (rem - (j+1)) (j+1) ((j+2)::acc)) = true by simpa [visit, he] using hv) (x-2) ix
        rw [show x-2+2 = x by omega] at hv'
        have res := ih _ _ _ xs hv' hlen (by omega) (List.pairwise_cons.mp hr).2 hp' (fun a ha => by
          have := upper a ha; omega)
        simpa [List.reverse_cons, List.append_assoc] using res

private theorem le_sum_of_mem {d : ℕ} {xs : List ℕ} (hd : d ∈ xs) : d ≤ xs.sum := by
  induction xs with
  | nil => simp at hd
  | cons a xs ih =>
    rcases List.mem_cons.mp hd with rfl | h <;> simp only [List.sum_cons]
    · omega
    · have := ih h; omega

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem profiles_verified (n : ℕ) (lo : 3 ≤ n) (hi : n ≤ 28) :
    visit (check n) n (n-2) (2*n) [] = true := by
  interval_cases n <;> decide +kernel

/-- Simultaneously rule out both violations on every tree degree profile below order 29. -/
theorem small_degree_profile {n : ℕ} (lo : 3 ≤ n) (hi : n ≤ 28) (ds : List ℕ)
    (hl : ds.length = n) (hs : ds.sum + 2 = 2*n) (hr : ds.Pairwise (· ≥ ·))
    (hp : ∀ x ∈ ds, 0 < x) :
    ∃ b, firstZeroStep ds ≤ b ∧ (modes ds).card + (n % 2) * firstZeroStep ds ≤ b + 1 ∧
      ExcludedBudget n ds b := by
  apply check_sound
  exact visit_sound n (n-2) (2*n) [] ds (profiles_verified n lo hi) hl (by omega) hr hp
    (fun x hx => by have := le_sum_of_mem hx; omega)

end Graffiti.FirstZero
