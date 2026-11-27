import Graffiti.HavelPotential
import Graffiti.TiedModeProfile
import Graffiti368

/-! # The two readings of WoW II 369 give different answers

Definition 45 says: “In case there is more than one mode, dd_mode(G) is the
number of distinct modes.” Counting a unique mode as one gives a false
unrestricted conjecture, with minimum counterexample order 29. Restricting
to the stated tie domain instead gives a **true** inequality. In a tree the
only possible tied modal degrees are 1 and 2. Two decreasing potentials for
the zero-free prefix bound the Havel–Hakimi index in terms of the number
and total degree of its nonleaves. At order 29 and above the parity factor
can be omitted altogether on trees with tied degrees.

https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/definitions.json
https://github.com/adamben04/graffiti-pc-369-counterexample
-/

namespace Graffiti.FirstZero

private theorem zero_free_prefix (t : ℕ) {ds : List ℕ} (sort : ds.Pairwise (· ≥ ·))
    (leaves : 2 ≤ ds.count 1) (safe : ∀ j : ℕ, 0 < j → j ≤ t → 0 ∉ step^[j] ds) :
    6*t ≤ nonleafWeight ds ∧ 3*t ≤ branchBudget ds := by
  induction t generalizing ds with
  | zero => simp
  | succ t ih =>
    have no : 0 ∉ step ds := by simpa using safe 1 (by decide) (by omega)
    obtain ⟨sort',leaves',cost₁,cost₂⟩ := safe_step sort leaves no
    have rest (j : ℕ) (hj : 0 < j) (hjt : j ≤ t) : 0 ∉ step^[j] (step ds) := by
      simpa only [Function.iterate_succ_apply] using safe (j+1) (by omega) (by omega)
    obtain ⟨r₁,r₂⟩ := ih sort' leaves' rest
    constructor <;> omega

/-- Upper estimates on the first-zero step. They require neither a tree nor
graphicality: sortedness and two entries equal to one are sufficient. -/
theorem first_zero_potentials {ds : List ℕ} (sort : ds.Pairwise (· ≥ ·)) (leaves : 2 ≤ ds.count 1) :
    6*(firstZeroStep ds-1) ≤ nonleafWeight ds ∧ 3*(firstZeroStep ds-1) ≤ branchBudget ds := by
  apply zero_free_prefix _ sort leaves
  intro j hj hjt h0
  have h : firstZeroStep ds ≤ j := Nat.sInf_le (s := {i : ℕ | 0 < i ∧ 0 ∈ step^[i] ds}) ⟨hj,h0⟩
  omega

variable {V : Type*} [Fintype V] [DecidableEq V] {T : SimpleGraph V} [DecidableRel T.Adj]

/-- With a tie and at least 29 vertices, the parity multiplier is not needed. -/
theorem tied_large_bound (ht : T.IsTree) (hn : 29 ≤ Fintype.card V)
    (tie : 2 ≤ (modes (degrees T)).card) :
    (modes (degrees T)).card + firstZeroStep (degrees T) ≤ totalDominationNumber T := by
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨len,sum,sort,pos,count⟩ := degree_list_facts ht (by omega)
  obtain ⟨modes_eq,leaves,order,branches,weight⟩ := tied_profile len sum pos tie
  have modecard : (modes (degrees T)).card = 2 := by rw [modes_eq]; decide
  obtain ⟨cost₁,cost₂⟩ := first_zero_potentials sort leaves
  change nonleafCount (degrees T) = _ at count
  obtain ⟨D,hd,size⟩ := exists_min_total_set ht.isConnected
  have parity := nonleaf_parity_budget ht hd
  have h : 2 * firstZeroStep (degrees T) < nonleafCount (degrees T) := by
    by_cases c : 5 ≤ branchCount (degrees T)
    · omega
    · unfold branchBudget at cost₂; omega
  omega

/-- WOWII 369 is true on the domain where the catalog expressly defines its mode count. -/
theorem graffiti369_on_ties (ht : T.IsTree) (hn : 2 < Fintype.card V)
    (tie : 2 ≤ (modes (degrees T)).card) :
    (modes (degrees T)).card + (Fintype.card V % 2) * firstZeroStep (degrees T) ≤ totalDominationNumber T := by
  by_cases small : Fintype.card V < 29
  · exact (smaller_trees_satisfy ht hn small).2
  · have pm : Fintype.card V % 2 ≤ 1 := by omega
    have mult : (Fintype.card V % 2) * firstZeroStep (degrees T) ≤ firstZeroStep (degrees T) := by
      simpa using Nat.mul_le_mul_right (firstZeroStep (degrees T)) pm
    exact (Nat.add_le_add_left mult _).trans (tied_large_bound ht (by omega) tie)

end Graffiti.FirstZero

#print axioms Graffiti.FirstZero.first_zero_potentials
#print axioms Graffiti.FirstZero.graffiti369_on_ties
