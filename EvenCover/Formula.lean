import EvenCover.Sequence
import Mathlib.Tactic.NormNum

/-! # Exact correction to `(19/30) * 2^n`

The OSF manuscript https://doi.org/10.17605/osf.io/tq45x reports numerical
evidence for the four-step recurrence and explicitly asks for a proof. The
optimal bit mask gives a bounded, exactly periodic error from `n = 9` on.
-/

namespace EvenCover

private def recurring (i : ℕ) : Bool := decide (i = 0 ∨ i % 4 = 2)
private def prefixValue (q : ℕ) := pack recurring (4*q)
private def tailBits (r i : ℕ) : Bool := decide (i = 0 ∨ i = 2 ∨ i = r)

/-- Each full four-bit block after the leading `1010` is `0010`. -/
private theorem prefix_step (q : ℕ) (hq : 0 < q) : prefixValue (q+1) = 16*prefixValue q + 2 := by
  have hblock : pack (fun i => recurring (4*q+i)) 4 = pack (fun i => decide (i=2)) 4 := by
    apply pack_congr
    intro i hi
    unfold recurring
    apply decide_eq_decide.mpr
    omega
  unfold prefixValue
  rw [show 4*(q+1)=4*q+4 by omega, pack_append, hblock,
    show pack (fun i => decide (i=2)) 4 = 2 by decide]
  omega

private theorem prefix_scaled (q : ℕ) : 30*prefixValue (q+1)+4 = 19*2^(4*(q+1)) := by
  induction q with
  | zero => decide
  | succ q ih =>
    rw [prefix_step (q+1) (by omega), show 4*(q+1+1) = 4*(q+1)+4 by omega, Nat.pow_add]
    omega

private theorem block_shape (q r : ℕ) (hq : 2 ≤ q) (hr : r < 4) :
    number (4*q+r) = prefixValue q * 2^(r+1) + pack (tailBits r) (r+1) := by
  have ha : anchor (4*q+r) = 4*q := by unfold anchor; split <;> omega
  have h₁ : pack (fun i => decide (pattern (4*q+r) i)) (4*q) = prefixValue q := by
    apply pack_congr
    intro i hi
    unfold recurring
    apply decide_eq_decide.mpr
    unfold pattern
    rw [ha]
    omega
  have h₂ : pack (fun i => decide (pattern (4*q+r) (4*q+i))) (r+1) = pack (tailBits r) (r+1) := by
    apply pack_congr
    intro i hi
    unfold tailBits
    apply decide_eq_decide.mpr
    unfold pattern
    rw [ha]
    omega
  unfold number
  rw [show 4*q+r+1=4*q+(r+1) by omega, pack_append, h₁, h₂]

/-- Numerator of the error, indexed by the sequence index (not the bit offset). -/
def correction (n : ℕ) : ℕ :=
  if n % 4 = 0 then 266 else if n % 4 = 1 then 22 else if n % 4 = 2 then 74 else 118

private theorem tail_arithmetic (r P K : ℕ) (hr : r < 4) (h : 30*P+4 = 19*K) :
    30*(P*2^(r+1)+pack (tailBits r) (r+1)) = 19*(K*2^(r+1)) + correction (r+1) := by
  have casesR : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases casesR with rfl | rfl | rfl | rfl
  all_goals (norm_num [tailBits, correction, pack, Nat.bit_true, Nat.bit_false]; omega)

/-- Exact formula, in integer arithmetic, valid from the ninth term. -/
theorem scaled_exact (n : ℕ) (hn : 9 ≤ n) : 30*sequence n = 19*2^n + correction n := by
  let q := (n-1)/4
  let r := (n-1)%4
  have hq : 2 ≤ q := by dsimp [q]; omega
  have hr : r < 4 := Nat.mod_lt _ (by decide)
  have he : n = 4*q+r+1 := by dsimp [q,r]; omega
  have hp : 30*prefixValue q+4 = 19*2^(4*q) := by
    simpa only [show q-1+1=q by omega] using prefix_scaled (q-1)
  have hc : correction n = correction (r+1) := by
    unfold correction
    rw [show n%4=(r+1)%4 by omega]
  calc 30*sequence n = 30*number (4*q+r) := congrArg (30 * ·) ((congrArg sequence he).trans (sequence_succ _))
       _ = 19*(2^(4*q)*2^(r+1)) + correction (r+1) := by
         rw [block_shape q r hq hr]; exact tail_arithmetic r _ _ hr hp
       _ = 19*2^n + correction n := by rw [← Nat.pow_add, ← hc, show 4*q+(r+1)=n by omega]

/-- All four corrections reported in the OSF manuscript hold universally
from the tenth index onward, including the negative corrections. -/
theorem four_corrections (n : ℕ) (hn : 9 ≤ n) :
    (sequence (n+1) : ℤ) - 2*(sequence n : ℤ) =
      (if n%4=0 then -17 else if n%4=2 then -1 else 1) := by
  have a := scaled_exact n hn
  have b := scaled_exact (n+1) (by omega)
  rw [Nat.pow_succ] at b
  have hh : n%4=0 ∨ n%4=1 ∨ n%4=2 ∨ n%4=3 := by omega
  rcases hh with h | h | h | h
  all_goals first | have hh' : (n+1)%4=0 := by omega | have hh' : (n+1)%4=1 := by omega | have hh' : (n+1)%4=2 := by omega | have hh' : (n+1)%4=3 := by omega
  all_goals (simp [correction, h, hh'] at a b ⊢; omega)

end EvenCover
