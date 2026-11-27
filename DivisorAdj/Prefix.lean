import DivisorAdj.Monotone
import Mathlib.Data.List.Sublists

namespace DivisorAdj

open Finset

/-- Cost of the prime prefix, including a possible jump to a divisor at least `C`. -/
def headCost (C x : ℕ) : List ℕ → ℚ
  | [] => 1 / ((x : ℚ)*C)
  | y :: ys => 1 / ((x : ℚ)*y) + headCost C y ys

private def wt (d : ℕ) : ℚ := 1 / (d : ℚ)^2

private theorem mono_recip {u v x y : ℕ} (hu : 0 < u) (hv : 0 < v) (hx : u ≤ x) (hy : v ≤ y) :
    1 / ((x : ℚ)*y) ≤ 1 / ((u : ℚ)*v) :=
  one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.mul_le_mul hx hy)

private theorem split_charge {C : ℕ} (hC : 0 < C) (small big : List ℕ) (hs : big.Pairwise (· < ·))
    (hb : ∀ d ∈ big, C ≤ d) (hp : ∀ d ∈ small, 0 < d) (x : ℕ) (hx : 0 < x) :
    recipSum (x :: (small ++ big)) ≤ headCost C x small + (big.map wt).sum := by
  induction small generalizing x with
  | nil =>
    cases big with
    | nil => simp [recipSum, headCost]; positivity
    | cons y ys =>
      have hj := mono_recip hx hC (le_refl x) (hb y (by simp))
      have ht := recipSum_square_bound (y::ys) hs (fun d hd => lt_of_lt_of_le hC (hb d hd))
      change recipSum (y::ys) ≤ (y::ys).toFinset.sum wt at ht
      rw [List.sum_toFinset wt (List.Sorted.nodup hs)] at ht
      simpa only [List.nil_append, recipSum, headCost] using add_le_add hj ht
  | cons y ys ih =>
    have hi := ih (fun d hd => hp d (List.mem_cons_of_mem _ hd)) y (hp y (by simp))
    simpa only [List.cons_append, recipSum, headCost, add_assoc] using
      add_le_add_left hi (1 / ((x : ℚ)*y))

private theorem lower_head_cost {C : ℕ} (hC : 0 < C) (f : ℕ → ℕ) {l : List ℕ}
    (hf : ∀ d ∈ l, 0 < f d ∧ f d ≤ d) {u x : ℕ} (hu : 0 < u) (hux : u ≤ x) :
    headCost C x l ≤ headCost C u (l.map f) := by
  induction l generalizing u x with
  | nil => exact mono_recip hu hC hux (le_refl C)
  | cons d ds ih =>
    obtain ⟨hd, hfd⟩ := hf d (by simp)
    exact add_le_add (mono_recip hu hd hux hfd)
      (ih (fun y hy => hf y (List.mem_cons_of_mem _ hy)) hd hfd)

-- All 128 increasing slot selections. An unused slot can supply at most one
-- prime at or above 121, costing at most 1/121² in the square-weight tail.
private theorem head_certificate : ∀ t ∈ (List.finRange 7).sublists',
    headCost 121 1 (t.map firstPrime) + ((7-t.length : ℕ) : ℚ) / 121^2 ≤ 1107/10000 := by decide +kernel

private theorem small_prime {m n d p₀ : ℕ} {L : Fin m → ℕ} (hn : n ≠ 0)
    (s : Slots L n) (hfirst : ∀ i, p₀ ≤ L i) (hd : d ∣ n)
    (h1 : 1 < d) (hcut : d < p₀^2) : d.Prime := by
  by_contra hnp
  have hq := Nat.minFac_prime (by omega : d ≠ 1)
  have hmem := Nat.mem_primeFactors.mpr ⟨hq, (Nat.minFac_dvd d).trans hd, hn⟩
  have hlo := (hfirst _).trans (s.lower ⟨d.minFac, hmem⟩)
  have := Nat.minFac_sq_le_self (by omega : 0 < d) hnp
  nlinarith

/-- Split at the square of a lower prime bound and charge each unused prime slot
at most one square weight. The caller bounds the cost of the retained slots. -/
theorem prefix_bound_certificate {m n p₀ : ℕ} [NeZero m] {L : Fin m → ℕ}
    {K : ℚ} (hn : 0 < n) (s : Slots L n) (hp₀ : 2 ≤ p₀) (hlo : ∀ i, p₀ ≤ L i)
    (cert : ∀ t : List (Fin m), t.Sublist (List.finRange m) →
      headCost (p₀^2) 1 (t.map L) + ((m-t.length : ℕ) : ℚ) / ((p₀^2 : ℕ) : ℚ)^2 ≤ K) :
    recipSum (divs n) ≤ K + compositeWeight n := by
  let C := p₀^2
  have hC' : 1 < C := by dsimp [C]; nlinarith
  have hC : 0 < C := by omega
  let A := n.primeFactors.filter (· < C)
  let B := n.divisors.filter (C ≤ ·)
  let l := A.sort (· ≤ ·)
  let b := B.sort (· ≤ ·)
  have hl {d} : d ∈ l ↔ d ∈ n.primeFactors ∧ d < C := by simp [l, A]
  have hb {d} : d ∈ b ↔ d ∈ n.divisors ∧ C ≤ d := by simp [b, B]
  have hp {d} (h : d ∈ l) := (Nat.mem_primeFactors.mp (hl.mp h).1).1
  have hs : (l ++ b).Pairwise (· < ·) := List.pairwise_append.mpr
    ⟨A.sort_sorted_lt, B.sort_sorted_lt, fun _ hi _ hj => (hl.mp hi).2.trans_le (hb.mp hj).2⟩
  have hdiv : divs n = 1 :: (l ++ b) := by
    have hhead : ∀ d ∈ l ++ b, 1 < d := by
      intro d hd
      rcases List.mem_append.mp hd with hi | hi
      · exact (hp hi).one_lt
      · exact lt_of_lt_of_le hC' (hb.mp hi).2
    apply List.Sorted.eq_of_mem_iff n.divisors.sort_sorted_lt (List.pairwise_cons.mpr ⟨hhead, hs⟩)
    · intro d
      simp only [divs, Finset.mem_sort, List.mem_cons, List.mem_append, hl, hb]
      constructor
      · intro h
        have hpos := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp h).1 hn
        by_cases h1 : d = 1
        · exact Or.inl h1
        by_cases hbig : C ≤ d
        · exact Or.inr (Or.inr ⟨h,hbig⟩)
        have hdvd := (Nat.mem_divisors.mp h).1
        exact Or.inr (Or.inl ⟨Nat.mem_primeFactors.mpr
          ⟨small_prime hn.ne' s hlo hdvd (by omega) (by omega), hdvd, hn.ne'⟩, by omega⟩)
      · rintro (rfl | ⟨h,_⟩ | ⟨h,_⟩)
        · exact Nat.mem_divisors.mpr ⟨one_dvd _, hn.ne'⟩
        · exact Nat.mem_divisors.mpr (Nat.mem_primeFactors.mp h).2
        · exact h
  let idx (d : ℕ) : Fin m := if h : d ∈ n.primeFactors then s.slot ⟨d,h⟩ else 0
  have hidx {d} (hd : d ∈ l) : idx d = s.slot ⟨d,(hl.mp hd).1⟩ := dif_pos _
  have hsorted : (l.map idx).Pairwise (· < ·) := List.pairwise_map.mpr <|
    A.sort_sorted_lt.imp_of_mem fun ha hb' h => by
      rw [hidx ha, hidx hb']; exact s.mono (show (⟨_,(hl.mp ha).1⟩ : n.primeFactors) < ⟨_,(hl.mp hb').1⟩ from h)
  have hsub := List.sublist_of_subperm_of_sorted (hsorted.nodup.subperm (fun d _ => List.mem_finRange d))
    (hsorted.imp (fun h => le_of_lt h)) (List.pairwise_le_finRange m)
  have hc := cert _ hsub
  rw [List.length_map, show l.length = A.card from Finset.length_sort ..] at hc
  let f (d : ℕ) := L (idx d)
  have hf : ∀ d ∈ l, 0 < f d ∧ f d ≤ d := by
    intro d hd
    exact ⟨lt_of_lt_of_le (by omega : 0 < p₀) (hlo _), by simpa only [f, hidx hd] using s.lower ⟨d,(hl.mp hd).1⟩⟩
  have hc' : headCost C 1 l + ((m-A.card : ℕ) : ℚ) / (C:ℚ)^2 ≤ K := by
    refine (add_le_add_right (lower_head_cost hC f hf (by decide : 0 < 1) (le_refl 1)) _).trans ?_
    simpa only [List.map_map, f, Function.comp_def] using hc
  have cardP : n.primeFactors.card ≤ m := by
    simpa using Fintype.card_le_of_injective s.slot s.mono.injective
  have hpbig : B.filter Nat.Prime = n.primeFactors.filter (fun p => ¬ p < C) := by
    ext p; simp [B, Nat.mem_primeFactors, Nat.mem_divisors, not_lt, and_assoc, and_left_comm, and_comm]
  have hcard : (B.filter Nat.Prime).card ≤ m - A.card := by
    rw [hpbig]; have ht := filter_card_add_filter_neg_card_eq_card (s := n.primeFactors) (· < C)
    change A.card + _ = _ at ht; omega
  have hbp : ∑ d ∈ B.filter Nat.Prime, wt d ≤ ((m-A.card : ℕ) : ℚ) / (C:ℚ)^2 := by
    calc
      _ ≤ ∑ _d ∈ B.filter Nat.Prime, (1 : ℚ) / (C:ℚ)^2 := by
        apply sum_le_sum; intro d hd
        have h := (mem_filter.mp (mem_filter.mp hd).1).2
        exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.pow_le_pow_left h 2)
      _ = ((B.filter Nat.Prime).card : ℚ) / (C:ℚ)^2 := by simp; ring
      _ ≤ _ := by gcongr
  have hbc : ∑ d ∈ B.filter (fun d => ¬d.Prime), wt d ≤ compositeWeight n := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro d hd
      obtain ⟨hB, hnp⟩ := mem_filter.mp hd
      obtain ⟨hdiv', hbig⟩ := mem_filter.mp hB
      exact mem_filter.mpr ⟨hdiv', by omega, hnp⟩
    · intro d _ _; dsimp [wt]; positivity
  have htail : (b.map wt).sum ≤ ((m-A.card : ℕ) : ℚ) / (C:ℚ)^2 + compositeWeight n := by
    rw [← List.sum_toFinset wt (B.sort_nodup _ : b.Nodup), show b.toFinset = B from B.sort_toFinset _,
      ← sum_filter_add_sum_filter_not B Nat.Prime wt]
    exact add_le_add hbp hbc
  rw [hdiv]
  have h := split_charge hC l b B.sort_sorted_lt (fun _ hd => (hb.mp hd).2) (fun _ hd => (hp hd).pos) 1 (by decide)
  linarith

private theorem headCost_eq (C x : ℕ) (l : List ℕ) :
    headCost C x l = recipSum (x :: (l ++ [C])) := by
  induction l generalizing x with
  | nil => simp [headCost, recipSum]
  | cons y ys ih => simp only [headCost, List.cons_append, recipSum, ih]

/-- Polynomial-size bound: retaining the entire ordered lower-bound table only
increases the head cost, so no enumeration of sublists is needed. -/
theorem prefix_bound_table {m n p₀ : ℕ} [NeZero m] {L : Fin m → ℕ}
    (hn : 0 < n) (s : Slots L n) (hp₀ : 2 ≤ p₀) (hlo : ∀ i, p₀ ≤ L i)
    (hhi : ∀ i, L i < p₀^2) (hmono : StrictMono L) :
    recipSum (divs n) ≤ headCost (p₀^2) 1 ((List.finRange m).map L) +
      (m : ℚ) / ((p₀^2 : ℕ) : ℚ)^2 + compositeWeight n := by
  apply prefix_bound_certificate hn s hp₀ hlo
  intro t ht
  apply add_le_add
  · rw [headCost_eq, headCost_eq]
    apply recipSum_le_sublist (((ht.map L).append_right _).cons₂ 1)
    · apply List.pairwise_cons.mpr
      constructor
      · intro y hy
        rcases List.mem_append.mp hy with h | h
        · obtain ⟨i, _, rfl⟩ := List.mem_map.mp h
          exact lt_of_lt_of_le (by omega : 1 < p₀) (hlo i)
        · simp only [List.mem_singleton] at h; subst y; nlinarith
      · apply List.pairwise_append.mpr
        refine ⟨List.pairwise_map.mpr ((List.pairwise_lt_finRange m).imp (fun h => hmono h)), by simp, ?_⟩
        intro y hy z hz
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hy
        simpa only [List.mem_singleton.mp hz] using hhi i
    · intro y hy
      simp only [List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | ⟨i, _, rfl⟩ | rfl
      · decide
      · exact lt_of_lt_of_le (by omega : 0 < p₀) (hlo i)
      · exact pow_pos (by omega) _
  · gcongr; exact Nat.sub_le _ _

/-- Seven slots at least eleven, with the sharper enumerated certificate. -/
theorem prefix_bound {n : ℕ} (hn : 0 < n) (s : Slots firstPrime n) :
    recipSum (divs n) ≤ 1107/10000 + compositeWeight n := by
  exact prefix_bound_certificate (p₀ := 11) hn s (by decide) (by decide)
    (fun t ht => head_certificate t (List.mem_sublists'.mpr ht))

end DivisorAdj
