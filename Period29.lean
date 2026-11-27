import PeriodPrimes
import PrimeFactor
import Mathlib.Tactic.Ring

/-! # The true greatest prime divisor at the counterexample exponent

For OEIS A353890 at exponent 29 the entire least period is computed here.
The candidate list is exhaustive by an integer polynomial Bézout identity.
Each membership certificate is an explicit residue of three equal powers.
-/

namespace PowerPeriods

def activePrimes29 : Finset ℕ :=
  {59, 233, 349, 929, 4003, 8353, 16067, 19489, 21577, 23201, 215587, 3033169, 23641903, 61584227, 89854181, 107367629, 108050869}

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
private theorem active29_of_mem {p : ℕ} (h : p ∈ activePrimes29) : ActivePrime 29 p := by
  simp only [activePrimes29, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, 3, by decide, by decide⟩
  · exact ⟨by norm_num, 13, by decide, by decide⟩
  · exact ⟨by norm_num, 3, by decide, by decide⟩
  · exact ⟨by norm_num, 316, by decide, by decide⟩
  · exact ⟨by norm_num, 1187, by decide, by decide⟩
  · exact ⟨by norm_num, 64, by decide, by decide⟩
  · exact ⟨by norm_num, 773, by decide, by decide⟩
  · exact ⟨by norm_num, 4521, by decide, by decide⟩
  · exact ⟨by norm_num, 2129, by decide, by decide⟩
  · exact ⟨by norm_num, 7763, by decide, by decide⟩
  · exact ⟨by norm_num, 89553, by decide, by decide⟩
  · exact ⟨by norm_num, 1011055, by decide, by decide⟩
  · exact ⟨by norm_num, 3917157, by decide, by decide⟩
  · exact ⟨by norm_num, 15847742, by decide, by decide⟩
  · exact ⟨by norm_num, 33693668, by decide, by decide⟩
  · exact ⟨by norm_num, 42933944, by decide, by decide⟩
  · exact ⟨by norm_num, 36385376, by decide, by decide⟩

private abbrev constant29 : ℕ := 2735850033508372087067941013799794412919529957130011404885199962712211814078316416277902

private def multiplier29 {R : Type*} [CommRing R] (t : R) : R :=
  - 4210829203759187042518857632708818149734855837317694768496206436841669988913101147009220 * t ^ 27
  + 58951608852628618595264006857923454096287981722447726758946890115783379844783416058129080 * t ^ 26
  - 530487919142680162444708073081269242823156828405850742088883994841207799909304905506182600 * t ^ 25
  + 3447597270445090519045592560227936248024756831416688833015460844961531059207388093162843500 * t ^ 24
  - 17233703296105679136289241535455936178265685217525198954074482884691021847051758432358104800 * t ^ 23
  + 68910739953314446159373410701796545885123328213082149397971032106804194478322943954031176600 * t ^ 22
  - 226313857982587874636719512937715592098203730319377135403276686600515615517715084222577286640 * t ^ 21
  + 621973258087522852237423628013484830420126849312630159150892132546640944237710590713460968560 * t ^ 20
  - 1450086016276082858512250037235939735518217855432087460940784299511705165444839960859937947050 * t ^ 19
  + 2897116918856125511724192109416320561466525176419049870548135029455484468440933008753464997500 * t ^ 18
  - 4997353054780553300159102828776646165075947498178271276492169582833416858482326666759964027800 * t ^ 17
  + 7483096916377277181932585981288921971961174567548767542690657225235243429788945103713452644150 * t ^ 16
  - 9764045292828516758511402894721519386754033560622777616231663368686219399655164371916073728000 * t ^ 15
  + 11127535124302804958610899530857911454890123020212054210114285878657814910997860107399523567800 * t ^ 14
  - 11087474618158589099059217858056432219782889168890091142630817089504438503266783967786334589600 * t ^ 13
  + 9656622666872745725408103256512569620683474840849732948757886342671948064711273433970724034000 * t ^ 12
  - 7340240199574643497057407411179897346685375864958282298138366966214954387328250914799429542340 * t ^ 11
  + 4855269309546254829922138829989221831276683502425877214635107740313176894391226912544587155160 * t ^ 10
  - 2782035703024439574674166422654218605061521215806650056661260597532749869929347932770435041400 * t ^ 9
  + 1371957296107576713483447065052542656866658738518777319171220732943097059962371274768064083100 * t ^ 8
  - 577092083037248839247434753005191641288405667983901496091857244377093417292451881811459287200 * t ^ 7
  + 204506204066363454232743067920439267496727231156439290115487356580922180394654795466071273800 * t ^ 6
  - 60013160521138450020662366506460526004278543461389511603663198095638238658859205277559984240 * t ^ 5
  + 14228068723660712819469298667300688237213874333800861661782117820439069510386066281965794860 * t ^ 4
  - 2625810916833150798869460060872215015757304838863733631958861533051358184535951887620628245 * t ^ 3
  + 355030117673746888824262517284232964867063661538647839073086854025408572227016675546715630 * t ^ 2
  - 31393368085377462844794984244330732092749249752966901871199394705378881740859134760383784 * t
  + 1367925016754186043533970506899897206459764978565005702442599981356105907039158208138951

set_option maxRecDepth 8192 in
set_option maxHeartbeats 12000000 in
private theorem bezout29 {R : Type*} [CommRing R] (t : R) :
    multiplier29 (-t) * (t^29 - (t-1)^29) + multiplier29 t * ((t+1)^29 - t^29) =
      (constant29 : R) := by
  unfold multiplier29 constant29
  ring

private theorem dvd_constant29 {p : ℕ} (h : ActivePrime 29 p) : p ∣ constant29 := by
  obtain ⟨_,x,h₁,h₂⟩ := h
  have he := bezout29 (x+1)
  have hs : x+1+1 = x+2 := by ring
  simp only [add_sub_cancel_right, hs, ← h₂, h₁, sub_self, mul_zero, add_zero] at he
  exact (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp he.symm

private theorem product29 : ∏ p ∈ activePrimes29, p = 23185169775494678703965601811862664516267203026525520380383050531459422153206071324389 := by decide

theorem mem_activePrimes29_iff (p : ℕ) : p ∈ activePrimes29 ↔ ActivePrime 29 p := by
  refine ⟨active29_of_mem, fun h => ?_⟩
  have hp := h.1
  have hd : constant29 ∣ (2 * ∏ q ∈ activePrimes29, q)^2 := by rw [product29]; decide
  rcases hp.dvd_mul.mp (hp.dvd_of_dvd_pow ((dvd_constant29 h).trans hd)) with h₂ | hprod
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2)).mp h₂
    have hh : ¬ ActivePrime 29 2 := by unfold ActivePrime; decide
    exact (hh h).elim
  · obtain ⟨q,hq,hpq⟩ := ((Nat.prime_iff.mp hp).dvd_finset_prod_iff id).mp hprod
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (active29_of_mem hq).1).mp hpq
    exact hq

theorem leastPeriod_twenty_nine : leastPeriod 29 (by decide) = 23185169775494678703965601811862664516267203026525520380383050531459422153206071324389 :=
  (leastPeriod_eq_prod 29 (by decide) activePrimes29 mem_activePrimes29_iff).trans product29

/-- In place of the two proposed composite values, the actual greatest factor. -/
theorem greatest_prime_factor_twenty_nine :
    PowerDifferences.IsGreatestPrimeFactor (leastPeriod 29 (by decide)) 108050869 := by
  have hm : 108050869 ∈ activePrimes29 := by decide
  have hp := active29_of_mem hm
  have occurs := mem_primeFactors_iff_active 29 (by decide)
  refine ⟨hp.1, (Nat.mem_primeFactors.mp ((occurs _).mpr hp)).2.1, ?_⟩
  intro q hq hd
  have ha := (occurs q).mp (Nat.mem_primeFactors.mpr ⟨hq,hd,(leastPeriod_spec 29 (by decide)).1.ne'⟩)
  have hs := (mem_activePrimes29_iff q).mpr ha
  simp only [activePrimes29, Finset.mem_insert, Finset.mem_singleton] at hs
  omega

end PowerPeriods
