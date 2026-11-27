import SelfBanning.Row
import Mathlib.Tactic.Ring

/-! # The two smallest labels force a square divisor of every period

The SeqFan discussion linked by OEIS A398589 noted a power-of-four divisor
in all 101 computed periods. In fact the full square `(k+1)^2` divides any
eventual period. Numbering the blocks of length `k+1` from zero, label `k+1`
occurs in successive block positions `1, 2, ..., k`, then misses one block.
-/

namespace SelfBanning

private theorem gap {k s u : ℕ} {a : ℕ → ℕ} (h : IsRow k a) (hs : a s = k+1)
    (h₁ : s < u) (h₂ : u ≤ s+(k+1)) : a u ≠ k+1 := by
  intro hu
  exact (h.allowed u s h₁ (by omega)) (hs.trans hu.symm)

private theorem second_if_free {k t : ℕ} {a : ℕ → ℕ} (h : IsRow k a)
    (hn : ¬ k+1 ∣ t) (hf : ∀ u < t, t ≤ u+(k+1) → a u ≠ k+1) : a t = k+1 := by
  have hl := h.lower t
  have hne : a t ≠ k := fun e => hn ((minimum_iff h t).1 e)
  by_contra hn'
  obtain ⟨u,hu,hb,he⟩ := h.skipped t (k+1) (by omega) (by omega)
  exact hf u hu hb he

/-- A release is delayed by one step precisely when the minimum intervenes. -/
private theorem next_second {k s t : ℕ} {a : ℕ → ℕ} (h : IsRow k a) (hs : a s = k+1)
    (hn : ¬ k+1 ∣ t) (hl : s+(k+1)+1 ≤ t) (hu : t ≤ s+(k+1)+2)
    (hskip : s+(k+1)+1 < t → k+1 ∣ s+(k+1)+1) : a t = k+1 := by
  apply second_if_free h hn
  intro v hv hb
  by_cases hsmall : v ≤ s+(k+1)
  · exact gap h hs (by omega) hsmall
  have he : v = s+(k+1)+1 := by omega
  have hm : a v = k := (minimum_iff h v).2 (he ▸ hskip (by omega))
  omega

private def mark (k c i : ℕ) : ℕ := c*(k+1)^2 + i*(k+2) + 1

private theorem mark_not_min {k c i : ℕ} (hi : i < k) : ¬ k+1 ∣ mark k c i := by
  have he : mark k c i = (k+1)*(c*(k+1)+i)+(i+1) := by unfold mark; ring
  rw [Nat.dvd_iff_mod_eq_zero, he, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  omega

private theorem marks_from_first {k c : ℕ} {a : ℕ → ℕ} (h : IsRow k a)
    (hf : a (mark k c 0) = k+1) (i : ℕ) (hi : i < k) : a (mark k c i) = k+1 := by
  induction i with
  | zero => exact hf
  | succ i ih =>
    have hd : mark k c (i+1) = mark k c i + (k+1)+1 := by unfold mark; ring
    exact next_second h (ih (by omega)) (mark_not_min hi) (by omega) (by omega) (by omega)

private theorem first_in_cycle {k : ℕ} {a : ℕ → ℕ} (h : IsRow k a) (hk : 0 < k) (c : ℕ) :
    a (mark k c 0) = k+1 := by
  induction c with
  | zero =>
    apply second_if_free h (mark_not_min hk)
    simp only [mark, zero_mul, zero_add]
    intro u hu _
    have e : u=0 := by omega
    have hm : a 0 = k := (minimum_iff h 0).2 (dvd_zero _)
    rw [e, hm]
    omega
  | succ c ih =>
    have hp := marks_from_first h ih (k-1) (by omega)
    have hd : mark k (c+1) 0 = mark k c (k-1)+(k+1)+2 := by
      obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
      simp only [Nat.succ_sub_one, mark, Nat.succ_eq_add_one]
      ring
    apply next_second h hp (mark_not_min hk) (by omega) (by omega)
    intro _
    have e : mark k c (k-1)+(k+1)+1 = (c+1)*(k+1)^2 := by
      simp only [mark, zero_mul, add_zero] at hd ⊢
      omega
    exact ⟨(c+1)*(k+1), by rw [e]; ring⟩

/-- The second slot in block `q` carries the second-smallest label exactly
when `q` is a multiple of the block length. -/
theorem block_second_iff {k : ℕ} {a : ℕ → ℕ} (h : IsRow k a) (hk : 0 < k) (q : ℕ) :
    a (q*(k+1)+1) = k+1 ↔ k+1 ∣ q := by
  let c := q/(k+1)
  let j := q%(k+1)
  have hq : j+(k+1)*c=q := Nat.mod_add_div q (k+1)
  have hj : j < k+1 := Nat.mod_lt _ (by omega)
  have hv := first_in_cycle h hk c
  by_cases hz : j = 0
  · have he : q*(k+1)+1=mark k c 0 := by
      rw [← hq, hz]; unfold mark; ring
    exact ⟨fun _ => Nat.dvd_of_mod_eq_zero hz, fun _ => he ▸ hv⟩
  · have hnot : ¬ k+1 ∣ q := fun hd => hz (Nat.mod_eq_zero_of_dvd hd)
    obtain ⟨i,hi⟩ := Nat.exists_eq_succ_of_ne_zero hz
    have hi' : i < k := by omega
    have hprevious := marks_from_first h hv i hi'
    have he : q*(k+1)+1 = c*(k+1)^2 + i*(k+2) + (k+1)+1 - i := by
      rw [← hq, hi]
      apply Nat.eq_sub_of_add_eq
      simp only [Nat.succ_eq_add_one]
      ring
    have hl : mark k c i < q*(k+1)+1 := by unfold mark; omega
    have hu : q*(k+1)+1 ≤ mark k c i+(k+1) := by unfold mark; omega
    exact ⟨fun hh => (gap h hprevious hl hu hh).elim, fun hd => (hnot hd).elim⟩

/-- A necessary divisor of *every* eventual period, not just the least one. -/
theorem square_dvd_period {k start T : ℕ} {a : ℕ → ℕ} (h : IsRow k a)
    (hp : ∀ t ≥ start, a (t+T) = a t) : (k+1)^2 ∣ T := by
  by_cases hz : k = 0
  · simp [hz]
  have hk : 0 < k := by omega
  let q := (k+1)*start
  let t := q*(k+1)
  have hs : start ≤ t := by
    calc start = 1*start := (Nat.one_mul _).symm
         _ ≤ (k+1)*start := Nat.mul_le_mul_right start (by omega)
         _ = q*1 := (Nat.mul_one q).symm
         _ ≤ q*(k+1) := Nat.mul_le_mul_left q (by omega)
  have ht : k+1 ∣ t := ⟨q,Nat.mul_comm _ _⟩
  have hm : a (t+T) = k := (hp t hs).trans ((minimum_iff h t).2 ht)
  have hT : k+1 ∣ T := (Nat.dvd_add_iff_right ht).mpr ((minimum_iff h _).1 hm)
  obtain ⟨u,hu⟩ := hT
  have hq : k+1 ∣ q := ⟨start,rfl⟩
  have hw := (hp (t+1) (by omega)).trans ((block_second_iff h hk q).2 hq)
  have he : (q+u)*(k+1)+1=t+1+T := by rw [hu]; dsimp [t]; ring
  have hu' : k+1 ∣ u := (Nat.dvd_add_iff_right hq).mpr ((block_second_iff h hk (q+u)).1 (he.symm ▸ hw))
  obtain ⟨v,hv⟩ := hu'
  exact ⟨v,by rw [hu,hv]; ring⟩

end SelfBanning
