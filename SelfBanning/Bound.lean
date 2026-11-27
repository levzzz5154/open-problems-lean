import SelfBanning.Core
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Choose

namespace SelfBanning

/-- A window of length `n * d` must reserve at least `n` slots for multiples
of `d`, regardless of where the window begins. -/
private theorem window_capacity {d n u w : ℕ} (hd : 0 < d) (s : Fin w → ℕ)
    (hinj : Function.Injective s) (hwin : ∀ i, u ≤ s i ∧ s i < u + n * d)
    (hnot : ∀ i, ¬ d ∣ s i) : w + n ≤ n * d := by
  let q := (u + d - 1) / d
  let p := d * q
  have hfirst : u ≤ p ∧ p < u + d := by
    have he := Nat.mod_add_div (u + d - 1) d
    have hr := Nat.mod_lt (u + d - 1) hd
    change u ≤ d * ((u + d - 1) / d) ∧ d * ((u + d - 1) / d) < u + d
    omega
  let m (i : Fin n) := p + i.val * d
  have hm (i : Fin n) : d ∣ m i :=
    ⟨q + i.val, by change d * q + i.val * d = d * (q + i.val)
                   rw [Nat.mul_add, Nat.mul_comm d i.val]⟩
  let pos : Fin w ⊕ Fin n → ℕ := Sum.elim s m
  have bounds (x) : u ≤ pos x ∧ pos x < u + n * d := by
    cases x with
    | inl i => exact hwin i
    | inr i =>
      change u ≤ p + i.val * d ∧ p + i.val * d < u + n * d
      have hi := Nat.mul_le_mul_right d (Nat.succ_le_of_lt i.isLt)
      rw [Nat.succ_mul] at hi
      omega
  have disjoint (i j) (he : s i = m j) : False := hnot i (he.symm ▸ hm j)
  have uniquePos : Function.Injective pos := by
    rintro (i | i) (j | j) he
    · exact congrArg Sum.inl (hinj he)
    · exact (disjoint i j he).elim
    · exact (disjoint j i he.symm).elim
    · change p + i.val * d = p + j.val * d at he
      exact congrArg Sum.inr (Fin.ext (Nat.mul_right_cancel hd (Nat.add_left_cancel he)))
  let slot (x : Fin w ⊕ Fin n) : Fin (n * d) :=
    ⟨pos x - u, by have := bounds x; omega⟩
  have injSlot : Function.Injective slot := by
    intro x y he
    apply uniquePos
    have he' : pos x - u = pos y - u := congrArg Fin.val he
    have hx := bounds x
    have hy := bounds y
    omega
  simpa using Fintype.card_le_of_injective slot injSlot

/-- No entry in the greedy row exceeds `(k+1)^2`. -/
theorem row_bounded {k : ℕ} {a : ℕ → ℕ} (h : IsRow k a)
    (hmin : ∀ t, a t = k ↔ k+1 ∣ t) (t : ℕ) : a t ≤ (k+1)^2 := by
  classical
  rw [pow_two]
  let B := (k + 1) * (k + 1)
  change a t ≤ B
  by_contra hlarge
  have hkB : k + 1 ≤ B := by
    have hh := Nat.mul_le_mul_left (k + 1) (show 1 ≤ k + 1 by omega)
    simpa [B] using hh
  have witnesses (i : Fin (B - k)) :
      ∃ s < t, t ≤ s + (k + 1 + i.val) ∧ a s = k + 1 + i.val := by
    have hi := i.isLt
    apply h.skipped <;> omega
  choose s hlt hwin hval using witnesses
  have hinj : Function.Injective s := by
    intro i j he
    have hij := congrArg a he
    rw [hval i, hval j] at hij
    exact Fin.ext (Nat.add_left_cancel hij)
  have hw (i) : t - B ≤ s i ∧ s i < t - B + B := by
    have hi := i.isLt
    have hw' := hwin i
    have hl := hlt i
    omega
  have hnot (i) : ¬ k + 1 ∣ s i := by
    intro hd
    have hsmall := (hmin (s i)).2 hd
    have hbig := hval i
    omega
  have hc : B - k + (k + 1) ≤ B :=
    window_capacity (d := k + 1) (n := k + 1) (u := t - B) (by omega) s hinj hw hnot
  omega

end SelfBanning
