import SelfBanning.Core
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Pigeonhole

namespace SelfBanning

/-- Once `B` previous entries are known, any ban on the smaller candidate
has a witness in the known history and hence also in the matching history. -/
private theorem not_lt_of_matching_history {k B x y n : ℕ} {a : ℕ → ℕ}
    (h : IsRow k a) (hb : ∀ t, a t ≤ B) (hn : B ≤ n)
    (hist : ∀ i < n, a (x + i) = a (y + i)) : ¬ a (x + n) < a (y + n) := by
  intro hlt
  obtain ⟨s, hs, hban, hval⟩ := h.skipped (y + n) (a (x + n)) (h.lower _) hlt
  have hbound := hb (x + n)
  have hstart : y ≤ s := by omega
  have hi : s - y < n := by omega
  have hmatch := hist (s - y) hi
  rw [show y + (s - y) = s by omega, hval] at hmatch
  exact h.allowed (x + n) (x + (s - y)) (by omega) (by omega) hmatch

/-- A bounded greedy row eventually repeats: there are finitely many windows
of length `B`, and equal windows force equal future entries. -/
theorem periodic_of_bounded {k B : ℕ} {a : ℕ → ℕ} (h : IsRow k a)
    (hb : ∀ t, a t ≤ B) : EventuallyPeriodic a := by
  let window (t : ℕ) (i : Fin B) : Fin (B + 1) :=
    ⟨a (t + i.val), Nat.lt_succ_of_le (hb _)⟩
  obtain ⟨u, v, huv, heq⟩ := Finite.exists_ne_map_eq_of_infinite window
  obtain ⟨x, y, hxy, hw⟩ : ∃ x y : ℕ, x < y ∧ window x = window y := by
    rcases lt_or_gt_of_ne huv with hlt | hgt
    · exact ⟨u, v, hlt, heq⟩
    · exact ⟨v, u, hgt, heq.symm⟩
  have tail_eq (n : ℕ) : a (x + n) = a (y + n) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n < B
      · exact congrArg Fin.val (congrFun hw ⟨n, hn⟩)
      · have hBn : B ≤ n := by omega
        have h₁ := not_lt_of_matching_history h hb hBn ih
        have h₂ := not_lt_of_matching_history (x := y) (y := x) h hb hBn
          (fun i hi => (ih i hi).symm)
        omega
  refine ⟨x, y - x, by omega, ?_⟩
  intro t ht
  have ht₁ : x + (t - x) = t := by omega
  have ht₂ : y + (t - x) = t + (y - x) := by omega
  simpa only [ht₁, ht₂] using (tail_eq (t - x)).symm

end SelfBanning
