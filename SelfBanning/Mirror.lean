import SelfBanning.Core

namespace SelfBanning

/-- The ascending run `k, ..., 2*k` forces the same labels in reverse
before it, separated from it by `k` entries all greater than `2*k`. -/
theorem mirror_of_ramp {k N : ℕ} {a : ℕ → ℕ} (h : IsRow k a) (hk : 0 < k)
    (hN : 2*(k+1) ≤ N) (ramp : ∀ i ≤ k, a (N+i) = k+i) :
    ∀ i ≤ k, a (N-(k+1+i)) = k+i := by
  have gap (s : ℕ) (hs : N - k ≤ s) (hsN : s < N) : 2*k < a s := by
    by_contra hsmall
    let i := a s - k
    have hlo := h.lower s
    have hi : i ≤ k := by dsimp [i]; omega
    have hv : a s = k + i := by dsimp [i]; omega
    have hr := ramp i hi
    exact h.allowed (N+i) s (by omega) (by rw [hr]; omega) (hv.trans hr.symm)
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    have hlast := gap (N-1) (by omega) (by omega)
    obtain ⟨s, hs, hdist, hv⟩ := h.skipped (N-1) (k+i) (by omega) (by omega)
    have hs' : s < N - k := by
      by_contra hn
      have := gap s (by omega) (by omega)
      omega
    have left : N - (k+1+i) ≤ s := by omega
    by_cases he : s = N - (k+1+i)
    · exact he ▸ hv
    · let j := N - (k+1) - s
      have hj : j < i := by dsimp [j]; omega
      have hjpos : N - (k+1+j) = s := by dsimp [j]; omega
      have prev := ih j hj (by omega)
      rw [hjpos] at prev
      omega

end SelfBanning
