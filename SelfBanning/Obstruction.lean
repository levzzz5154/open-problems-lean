import SelfBanning.Row

/-! # The mirrored initial run is impossible past the boundary

At a descent from a larger label to `v`, exactly one past occurrence of `v`
can account for its unavailability one step earlier and its availability now.
Applying this to the mirrored run forces a second copy with doubled offsets.
-/

namespace SelfBanning

/-- No sufficiently late anchor admits the mirrored run forced by a repeated
initial ascending block, for any starting label `k ≥ 3`. -/
theorem no_mirror {k N : ℕ} {a : ℕ → ℕ} (h : IsRow k a) (hk : 3 ≤ k)
    (hN : 5*(k+2) ≤ N) (hmirror : ∀ i ≤ k, a (N-(k+1+i))=k+i) : False := by
  let d := k+1
  let b := fun j : ℕ => a (N-j)
  have hd : d = k+1 := rfl
  change ∀ i ≤ k, b (d+i) = k+i at hmirror
  have lower (x : ℕ) : k ≤ b x := h.lower _
  -- Arguments are offsets into the past: the larger offset is the earlier time.
  have ban (x y v : ℕ) (hy : b y = v) (hyx : y < x) (hx : x ≤ N)
      (hgap : x ≤ y+v) : b x ≠ v := by
    intro he
    have hy' : a (N-y) = v := hy
    exact h.allowed (N-y) (N-x) (by omega) (by omega)
      ((show a (N-x) = v from he).trans hy'.symm)
  have release (x v : ℕ) (hx : x+v+1 ≤ N) (he : b x = v) (hh : v < b (x+1)) :
      b (x+v+1) = v := by
    have hv : k ≤ v := he ▸ lower x
    obtain ⟨s,hs,hb,hsval⟩ := h.skipped (N-(x+1)) v hv hh
    have he' : a (N-x) = v := he
    have hfar : s+v < N-x := by
      by_contra! hclose
      exact h.allowed (N-x) s (by omega) (by omega) (hsval.trans he'.symm)
    have hsEq : s = N-(x+v+1) := by omega
    change a (N-(x+v+1)) = v
    rwa [← hsEq]
  have twice (i : ℕ) (hi : i < k) : b (2*(d+i)) = k+i := by
    have hbefore := hmirror (i+1) (by omega)
    have hh : k+i < b (d+i+1) := by
      rw [show d+i+1 = d+(i+1) by omega, hbefore]
      omega
    rw [show 2*(d+i) = d+i+(k+i)+1 by omega]
    exact release (d+i) (k+i) (by omega) (hmirror i (by omega)) hh
  have m₂ : b (2*d) = k := by simpa using twice 0 (by omega)
  have s₂ : b (2*(d+1)) = k+1 := twice 1 (by omega)
  -- The minimum and its successor each give a third forced occurrence.
  have m₃ : b (3*d) = k := by
    have hn := ban (2*d+1) (2*d) k m₂ (by omega) (by omega) (by omega)
    have hl := lower (2*d+1)
    rw [show 3*d = 2*d+k+1 by omega]
    exact release (2*d) k (by omega) m₂ (by omega)
  have s₃ : b (3*(d+1)) = k+1 := by
    let x := 2*(d+1)+1
    have hx : x = 2*(d+1)+1 := rfl
    have hn := ban x (2*d) k m₂ (by omega) (by omega) (by omega)
    have hs := ban x (2*(d+1)) (k+1) s₂ (by omega) (by omega) (by omega)
    have hl := lower x
    have hh : k+1 < b x := by omega
    rw [show 3*(d+1) = 2*(d+1)+(k+1)+1 by omega]
    exact release (2*(d+1)) (k+1) (by omega) s₂ hh
  by_cases heven : d % 2 = 0
  · have hcollision := twice (d/2) (by omega)
    rw [show 2*(d+d/2) = 3*d by omega, m₃] at hcollision
    omega
  by_cases hk4 : k = 4
  · -- The first collision here is at offset 24, for labels 5 and 7.
    have m15 : b 15 = 4 := by simpa [d,hk4] using m₃
    have s12 : b 12 = 5 := by simpa [d,hk4] using s₂
    have s18 : b 18 = 5 := by simpa [d,hk4] using s₃
    have t14 : b 14 = 6 := by simpa [d,hk4] using twice 2 (by omega)
    have t16 : b 16 = 7 := by simpa [d,hk4] using twice 3 (by omega)
    have s24 : b 24 = 5 := by
      have hl := lower 19
      have hn := ban 19 15 4 m15 (by decide) (by omega) (by decide)
      have hs := ban 19 18 5 s18 (by decide) (by omega) (by decide)
      exact release 18 5 (by omega) s18 (by change 5 < b 19; omega)
    have t24 : b 24 = 7 := by
      have hl := lower 17
      have hn := ban 17 15 4 m15 (by decide) (by omega) (by decide)
      have hs := ban 17 12 5 s12 (by decide) (by omega) (by decide)
      have ht := ban 17 14 6 t14 (by decide) (by omega) (by decide)
      have hu := ban 17 16 7 t16 (by decide) (by omega) (by decide)
      exact release 16 7 (by omega) t16 (by change 7 < b 17; omega)
    omega
  · have hcollision := twice ((d+3)/2) (by omega)
    rw [show 2*(d+(d+3)/2) = 3*(d+1) by omega, s₃] at hcollision
    omega

end SelfBanning
