import PeriodPrimes
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring

/-! # The least period at exponent 20 in OEIS A353890

The Bézout certificate bounds all possible prime divisors without searching up
to the period or assuming a bound on the primes. Only two extra candidate
primes, 2 and 29, require a local exclusion.
-/

namespace PowerPeriods

/-- The thirteen active primes at exponent twenty. -/
def activePrimes20 : Finset ℕ :=
  {5, 11, 31, 41, 61, 101, 401, 541, 761, 1061, 1181, 1361, 1601}

private theorem active20_of_mem {p : ℕ} (h : p ∈ activePrimes20) : ActivePrime 20 p := by
  simp only [activePrimes20, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, 1, by decide, by decide⟩
  · exact ⟨by norm_num, 1, by decide, by decide⟩
  · exact ⟨by norm_num, 9, by decide, by decide⟩
  · exact ⟨by norm_num, 8, by decide, by decide⟩
  · exact ⟨by norm_num, 5, by decide, by decide⟩
  · exact ⟨by norm_num, 47, by decide, by decide⟩
  · exact ⟨by norm_num, 190, by decide, by decide⟩
  · exact ⟨by norm_num, 11, by decide, by decide⟩
  · exact ⟨by norm_num, 18, by decide, by decide⟩
  · exact ⟨by norm_num, 281, by decide, by decide⟩
  · exact ⟨by norm_num, 589, by decide, by decide⟩
  · exact ⟨by norm_num, 511, by decide, by decide⟩
  · exact ⟨by norm_num, 780, by decide, by decide⟩

private abbrev constant20 : ℕ := 12385717229909763881405723731679000

/-- In the centered coordinate `t = x + 1`, reflection exchanges the two
outer residues. Hence one multiplier supplies both halves of the certificate. -/
private def multiplier20 {R : Type*} [CommRing R] (t : R) : R :=
    15926214264543657188601148760350980 * t ^ 18
  - 151299035513164743291710913223334310 * t ^ 17
  + 907363774834632049804897843003655180 * t ^ 16
  - 3854036242264315059457635741999693445 * t ^ 15
  + 12321503212653878762579624701887822416 * t ^ 14
  - 30761080079715802552432426208418696070 * t ^ 13
  + 61398428170599854442861725701600706324 * t ^ 12
  - 99485955864721560187517812674014256610 * t ^ 11
  + 132108252162715705916353015170282392376 * t ^ 10
  - 144482226584900594985211619340586962609 * t ^ 9
  + 130272269018112484810725779661665442184 * t ^ 8
  - 96556807900300386564325174192424419661 * t ^ 7
  + 58404316987969706108972739931426551696 * t ^ 6
  - 28461857553414930802963119943996193519 * t ^ 5
  + 10945116668535746932092329716248585280 * t ^ 4
  - 3211906293033897267550928655714791266 * t ^ 3
  + 679377954907121555143104298233809380 * t ^ 2
  - 92801054587427456193832402637165719 * t
  + 6192858614954881940702861865839500

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem bezout20 {R : Type*} [CommRing R] (t : R) :
    multiplier20 (-t) * ((t - 1) ^ 20 - t ^ 20) +
      multiplier20 t * ((t + 1) ^ 20 - t ^ 20) = (constant20 : R) := by
  unfold multiplier20 constant20
  ring

private theorem dvd_constant20 {p : ℕ} (h : ActivePrime 20 p) : p ∣ constant20 := by
  obtain ⟨_, x, h₁, h₂⟩ := h
  have e := bezout20 (x + 1)
  have hs : x + 1 + 1 = x + 2 := by ring
  simp only [add_sub_cancel_right, hs, ← h₂, h₁, sub_self, mul_zero, add_zero] at e
  exact (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp e.symm

private theorem product20 : ∏ p ∈ activePrimes20, p = 194133498901406957388804447205 := by
  decide

/-- No prime outside the displayed set can witness a triple at exponent 20. -/
theorem mem_activePrimes20_iff (p : ℕ) : p ∈ activePrimes20 ↔ ActivePrime 20 p := by
  refine ⟨active20_of_mem, fun h => ?_⟩
  have hp := h.1
  -- The factorization has multiplicities at most three. This divisibility
  -- check certifies that no additional prime can divide the Bézout constant.
  have hd : constant20 ∣ (2 * 29 * ∏ q ∈ activePrimes20, q) ^ 3 := by
    rw [product20]
    decide
  have hd' := hp.dvd_of_dvd_pow ((dvd_constant20 h).trans hd)
  rcases hp.dvd_mul.mp hd' with he | hs
  · rcases hp.dvd_mul.mp he with h₂ | h₂₉
    · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2)).mp h₂
      have hn : ¬ ActivePrime 20 2 := by unfold ActivePrime; decide
      exact (hn h).elim
    · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 29)).mp h₂₉
      have hn : ¬ ActivePrime 20 29 := by unfold ActivePrime; decide
      exact (hn h).elim
  · obtain ⟨q, hq, hdq⟩ := ((Nat.prime_iff.mp hp).dvd_finset_prod_iff id).mp hs
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (active20_of_mem hq).1).mp hdq
    exact hq

/-- The value at index 20 of A353890 (whose offset is 2). -/
theorem leastPeriod_twenty : leastPeriod 20 (by decide) = 194133498901406957388804447205 :=
  (leastPeriod_eq_prod 20 (by decide) activePrimes20 mem_activePrimes20_iff).trans product20

end PowerPeriods
