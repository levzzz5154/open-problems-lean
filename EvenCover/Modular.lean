import EvenCover.Asymptotic
import Mathlib.Data.Nat.Size
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-! # Prime membership cannot be guaranteed by a reduced residue class

The prime question in https://doi.org/10.17605/osf.io/tq45x concerns coverage
through the full binary width, not coverage of a fixed finite prefix. Dirichlet's
theorem produces arbitrarily large counterexamples in *each* reduced class.
-/

namespace EvenCover

/-- The pair sums cover all even targets up to twice the binary width. -/
def FullCover (m : ℕ) : Prop := Covers m.size m

theorem not_full_of_missing_bits {m t : ℕ} (ht : t < m.size)
    (hg : ∀ i, t ≤ i → i ≤ 2*t → m.testBit i = false) : ¬ FullCover m := by
  intro hc
  obtain ⟨i,j,hi,hj,hs⟩ := hc t ht
  by_cases hl : t ≤ i
  · rw [hg i hl (by omega)] at hi
    contradiction
  · rw [hg j (by omega) (by omega)] at hj
    contradiction

/-- A fixed positive fraction of each sufficiently high dyadic block is empty. -/
theorem no_cover_at_start_of_block {m n : ℕ} (hn : 8 ≤ n) (hl : 2^n ≤ m)
    (hu : 15*m ≤ 19*2^n) : ¬ FullCover m := by
  have hpow := Nat.two_pow_pos n
  have hh : m < 2^(n+1) := by rw [Nat.pow_succ]; omega
  have he : m.size = n+1 := by have := Nat.size_le.mpr hh; have := Nat.lt_size.mpr hl; omega
  intro hm
  have hc : Covers (n+1) m := he ▸ hm
  have hmin := (width_interval (by omega : 0<n+1) hh hc).1
  have hs := scaled_exact (n+1) (by omega)
  have hpos : 0 < correction (n+1) := by unfold correction; split <;> (try split) <;> (try split) <;> decide
  rw [Nat.pow_succ] at hs
  omega

/-- In any reduced residue class, primes that fail the full covering condition
occur beyond any cutoff. This is not an assertion about their density. -/
theorem arbitrarily_large_noncovering_prime {m b : ℕ} (hm : 0 < m) (hb : b.Coprime m) (N : ℕ) :
    ∃ p > N, p.Prime ∧ p ≡ b [MOD m] ∧ ¬ FullCover p := by
  letI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨r,hrt,hr,hres⟩ := Nat.forall_exists_prime_gt_and_eq_mod ((ZMod.isUnit_iff_coprime b m).2 hb) 2
  let t := r.size
  let B := 2^(2*t+1)
  have hB : 0 < B := Nat.two_pow_pos _
  letI : NeZero (m*B) := ⟨(Nat.mul_pos hm hB).ne'⟩
  have hrm : r.Coprime m := (ZMod.isUnit_iff_coprime _ _).1 (hres ▸ (ZMod.isUnit_iff_coprime b m).2 hb)
  have hr₂ : r.Coprime 2 := Nat.coprime_two_right.mpr (hr.odd_of_ne_two (by omega))
  have hcop : r.Coprime (m*B) := hrm.mul_right (hr₂.pow_right _)
  obtain ⟨p,hpn,hp,hpmod⟩ := Nat.forall_exists_prime_gt_and_eq_mod
    ((ZMod.isUnit_iff_coprime _ _).2 hcop) (max N (2^t))
  have hz := (ZMod.natCast_eq_natCast_iff p r (m*B)).1 hpmod
  have hpr : p ≡ b [MOD m] := (hz.of_dvd (dvd_mul_right m B)).trans ((ZMod.natCast_eq_natCast_iff _ _ _).1 hres)
  have hrpow : r < 2^t := Nat.lt_size_self r
  have hrB : r < B := lt_of_lt_of_le hrpow (Nat.pow_le_pow_right (by decide) (by omega : t ≤ 2*t+1))
  have hlow : p%B = r := Eq.trans (hz.of_dvd (dvd_mul_left B m)) (Nat.mod_eq_of_lt hrB)
  refine ⟨p,lt_of_le_of_lt (le_max_left _ _) hpn,hp,hpr,not_full_of_missing_bits (t := t)
    (Nat.lt_size.mpr (le_trans (le_max_right _ _) hpn.le)) ?_⟩
  intro i hi hi'
  have he := congrArg (fun z : ℕ => z.testBit i) hlow
  have hrzero := Nat.testBit_lt_two_pow (lt_of_lt_of_le hrpow (Nat.pow_le_pow_right (by decide) hi))
  simpa [B,show i < 2*t+1 by omega, hrzero] using he

end EvenCover
