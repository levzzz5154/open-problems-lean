import Mathlib.Data.Nat.Basic

/-! # The greedy self-banning rows of OEIS A398589

Time starts at zero. An occurrence of `v` at time `s` makes `v` unavailable
at times `s+1, ..., s+v`; it becomes available again at `s+v+1`.
-/

namespace SelfBanning

/-- A row always takes the least unbanned integer at least `k`. -/
structure IsRow (k : ℕ) (a : ℕ → ℕ) : Prop where
  lower (t : ℕ) : k ≤ a t
  allowed (t s : ℕ) (hs : s < t) (hb : t ≤ s + a t) : a s ≠ a t
  skipped (t v : ℕ) (hk : k ≤ v) (hv : v < a t) :
    ∃ s < t, t ≤ s + v ∧ a s = v

def EventuallyPeriodic (a : ℕ → ℕ) : Prop :=
  ∃ start T : ℕ, 0 < T ∧ ∀ t ≥ start, a (t + T) = a t

end SelfBanning
