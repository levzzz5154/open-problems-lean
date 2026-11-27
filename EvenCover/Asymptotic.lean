import EvenCover.Formula
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace EvenCover

/-- The prime upper bound asked for in the OSF manuscript holds even without
primality or the pair-sum assumption, and without its additive `+1`. -/
theorem width_bound (n m : ℕ) (hm : m < 2^n) : 19*m ≤ 30*sequence n := by
  by_cases hn : 9 ≤ n
  · have h := scaled_exact n hn
    omega
  cases n with
  | zero =>
    have : m = 0 := by simpa using hm
    simp [this]
  | succ N =>
    rw [sequence_succ]
    suffices hu : 19*(2^(N+1)-1) ≤ 30*number N by omega
    have hh : N=0 ∨ N=1 ∨ N=2 ∨ N=3 ∨ N=4 ∨ N=5 ∨ N=6 ∨ N=7 := by omega
    rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Every covering `n`-bit integer is between the two consecutive thresholds. -/
theorem width_interval {n m : ℕ} (hn : 0 < n) (hm : m < 2^n) (hc : Covers n m) :
    sequence n ≤ m ∧ m < sequence (n+1) := by
  constructor
  · obtain ⟨N,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    rw [sequence_succ]
    exact number_le_of_covers hc
  · rw [sequence_succ]
    exact lt_of_lt_of_le hm (Nat.testBit_implies_ge (number_top n))

/-- The asymptotic constant is exactly `19/30`. -/
theorem normalized_limit : Filter.Tendsto (fun n : ℕ => (sequence n : ℝ) / 2^n)
    Filter.atTop (nhds (19/30 : ℝ)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := exists_nat_gt ((266 : ℝ)/ε)
  refine ⟨max 9 N, fun n hn => ?_⟩
  have h₉ : 9 ≤ n := le_trans (le_max_left _ _) hn
  have hnN : N ≤ n := le_trans (le_max_right _ _) hn
  have hlarge : (266 : ℝ) / ε < 2^n := calc
    (266:ℝ)/ε < (N:ℝ) := hN
    _ ≤ (n:ℝ) := by exact_mod_cast hnN
    _ < (2:ℝ)^n := by exact_mod_cast Nat.lt_two_pow_self (n := n)
  have hg : (266:ℝ) < 2^n * ε := (div_lt_iff₀ hε).mp hlarge
  have hp : (0:ℝ) < 2^n := pow_pos (by norm_num) _
  have hs : 30*(sequence n : ℝ) = 19*2^n + (correction n : ℝ) := by exact_mod_cast scaled_exact n h₉
  have hc : correction n ≤ 266 := by unfold correction; split <;> (try split) <;> (try split) <;> decide
  have hc' : (correction n : ℝ) ≤ 266 := by exact_mod_cast hc
  have hex : (sequence n : ℝ)/2^n - 19/30 = (correction n : ℝ)/(30*2^n) := by
    have hnum : (sequence n : ℝ)*30 - 2^n*19 = (correction n : ℝ) := by linarith
    field_simp
    rw [hnum, mul_comm (30:ℝ) (2^n)]
  rw [Real.dist_eq, hex, abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (by positivity))]
  apply (div_lt_iff₀ (by positivity : (0:ℝ)<30*2^n)).mpr
  nlinarith [mul_pos hε hp]

end EvenCover
