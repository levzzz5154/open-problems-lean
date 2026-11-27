import EvenCover.Core
import Mathlib.Data.Fintype.Basic

namespace EvenCover

-- This bounded check includes the two exceptional anchors, at lengths 7 and 8.
private theorem small_pairs : ∀ N t : Fin 8, t.val ≤ N.val →
    ∃ x y : Fin 8, pattern N.val x.val ∧ pattern N.val y.val ∧
      x.val + y.val = 2 * t.val := by decide

/-- Each even sum up to `2*N` is realized by two offsets in the pattern. -/
theorem pattern_covers (N : ℕ) : CoversOffsets N (pattern N) := by
  intro t ht
  by_cases hsmall : N < 8
  · obtain ⟨x, y, hx, hy, hsum⟩ := small_pairs ⟨N, hsmall⟩ ⟨t, by omega⟩ ht
    exact ⟨x.val, y.val, hx.1, hy.1, hx, hy, hsum⟩
  let m := N / 4
  have hm : 4 * m ≤ N ∧ N < 4 * m + 4 := by dsimp [m]; omega
  have hzero : pattern N 0 := ⟨Nat.zero_le _, Or.inl rfl⟩
  have hend : pattern N N := ⟨le_rfl, Or.inr (Or.inr (Or.inr rfl))⟩
  have hM : pattern N (4 * m) := by
    refine ⟨hm.1, Or.inr (Or.inr (Or.inl ?_))⟩
    simp [anchor, m, show ¬ (N = 6 ∨ N = 7) by omega]
  have regular (k : ℕ) (hk : 4 * k + 2 ≤ N) : pattern N (4 * k + 2) :=
    ⟨hk, Or.inr (Or.inl (by simp [Nat.add_mod]))⟩
  have pair {x y : ℕ} (hx : pattern N x) (hy : pattern N y) (hs : x + y = 2 * t) :
      ∃ x y : ℕ, x ≤ N ∧ y ≤ N ∧ pattern N x ∧ pattern N y ∧ x + y = 2 * t :=
    ⟨x, y, hx.1, hy.1, hx, hy, hs⟩
  by_cases he : t = N
  · exact pair hend hend (by omega)
  by_cases hc : t ≤ 4 * m
  · by_cases hz : t = 0
    · exact pair hzero hzero (by omega)
    by_cases hlast : t = 4 * m
    · exact pair hM hM (by omega)
    -- Interior multiples of four are midpoints of consecutive regular offsets.
    by_cases hfour : t = 4 * (t / 4)
    · exact pair (regular (t / 4 - 1) (by omega)) (regular (t / 4) (by omega)) (by omega)
    by_cases htwo : t = 4 * (t / 4) + 2
    · exact pair (regular (t / 4) (by omega)) (regular (t / 4) (by omega)) (by omega)
    -- For an odd midpoint, pair a regular offset with the nearer core endpoint.
    obtain ⟨q, hq⟩ : ∃ q : ℕ, t = 2 * q + 1 := by
      by_cases hone : t = 4 * (t / 4) + 1
      · exact ⟨2 * (t / 4), by omega⟩
      · exact ⟨2 * (t / 4) + 1, by omega⟩
    by_cases hlo : 2 * t ≤ 4 * m
    · exact pair hzero (regular q (by omega)) (by omega)
    · exact pair hM (regular (q - m) (by omega)) (by omega)
  · -- Above the core there are at most two non-endpoint midpoints.
    by_cases hone : t = 4 * m + 1
    · exact pair hM (regular m (by omega)) (by omega)
    · exact pair (regular m (by omega)) (regular m (by omega)) (by omega)

end EvenCover
