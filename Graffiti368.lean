import Graffiti.FirstZeroProfiles
import Graffiti.DegreeCoverage
import Graffiti.ParityNonleaf

/-! # The smallest counterexamples to WoW II 368 and 369

DeLaViña, Larson, Pepper and Waller exhibit a tree with `γₜ = k = 8` and
ask whether a smaller counterexample to 368 exists (p. 13, Figure 5).
The minimum order is 29. The same 29-vertex tree is also a smallest
counterexample to 369 under the ordinary count of one for a unique mode.
Definition 45 specifies the count expressly only for ties. This witness
does not refute a version restricted to trees with two or more modes.
The 29-vertex witness and a Python minimality check for 369 were previously
reported by adamben04. Here both lower bounds are checked in Lean.

https://www.uhd.edu/documents/academics/sciences/boca2009-dlpw.pdf#page=13
https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json
https://github.com/google-deepmind/formal-conjectures/pull/8319
-/

namespace Graffiti.FirstZero

open Finset SimpleGraph

/-- Both proposed inequalities hold for every tree of orders 3 through 28. -/
theorem smaller_trees_satisfy {V : Type*} [Fintype V] [DecidableEq V] {T : SimpleGraph V}
    [DecidableRel T.Adj] (ht : T.IsTree) (hn : 2 < Fintype.card V) (hi : Fintype.card V < 29) :
    1 + firstZeroStep (degrees T) ≤ totalDominationNumber T ∧
    (modes (degrees T)).card + (Fintype.card V % 2) * firstZeroStep (degrees T) ≤ totalDominationNumber T := by
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨len, sum, sorted, pos, hnon⟩ := degree_list_facts ht hn
  obtain ⟨b, hk, hm, excl⟩ := small_degree_profile hn (by omega) _ len sum sorted pos
  obtain ⟨D, hd, size⟩ := exists_min_total_set ht.isConnected
  have more : b < D.card := by
    by_contra! h
    rcases excl with bad | bad | bad
    · have := two_le_totalDominationNumber ht.isConnected; omega
    · have := nonleaf_parity_budget ht hd; omega
    · exact (Nat.not_lt_of_ge (degree_prefix_cover hd h)) bad
  omega

/-- Orders of counterexamples to the original tree conjecture 368. -/
def orders368 : Set ℕ := {n | 2 < n ∧ ∃ (T : SimpleGraph (Fin n)) (da : DecidableRel T.Adj),
    T.IsTree ∧ totalDominationNumber T < 1 + firstZeroStep (@degrees _ _ T da)}

/-- Orders of counterexamples to its parity-and-modes variant 369. -/
def orders369 : Set ℕ := {n | 2 < n ∧ ∃ (T : SimpleGraph (Fin n)) (da : DecidableRel T.Adj),
    T.IsTree ∧ totalDominationNumber T < (modes (@degrees _ _ T da)).card +
      (n % 2) * firstZeroStep (@degrees _ _ T da)}

/-- Exact answer to the smaller-counterexample question following Conjecture 7. -/
theorem least_counterexample_368 : IsLeast orders368 29 := by
  constructor
  · obtain ⟨ht, hd, _, hk⟩ := certificate
    exact ⟨by decide, tree, inferInstance, ht, by rw [hd, hk]; decide⟩
  · rintro n ⟨hn, T, da, ht, bad⟩
    letI := da
    by_contra! h
    have lower := (smaller_trees_satisfy ht (by simpa using hn) (by simpa using h)).1
    exact (Nat.not_lt_of_ge lower) bad

/-- The same order is optimal for the conjecture with all modal degrees counted. -/
theorem least_counterexample_369 : IsLeast orders369 29 := by
  constructor
  · obtain ⟨ht, hd, hm, hk⟩ := certificate
    exact ⟨by decide, tree, inferInstance, ht, by rw [hd, hm, hk]; decide⟩
  · rintro n ⟨hn, T, da, ht, bad⟩
    letI := da
    by_contra! h
    have lower := (smaller_trees_satisfy ht (by simpa using hn) (by simpa using h)).2
    rw [Fintype.card_fin] at lower
    exact (Nat.not_lt_of_ge lower) bad

end Graffiti.FirstZero

#print axioms Graffiti.FirstZero.least_counterexample_368
#print axioms Graffiti.FirstZero.least_counterexample_369
