import SelfBanning.Clock
import SelfBanning.Bound
import SelfBanning.Periodicity
import SelfBanning.SmallRows
import SelfBanning.LinearBound

/-! # Eventual periodicity of every row of A398589

The source https://oeis.org/A398589 labels eventual periodicity a conjecture.
The counting argument gives an explicit bound for the entire row, including
its preperiod; deterministic continuation of a repeated finite window finishes.
-/

namespace SelfBanning

theorem value_le_square (k t : ℕ) : row k t ≤ (k+1)^2 :=
  row_bounded (isRow k) (minimum_iff (isRow k)) t

/-- Every greedy self-banning row is eventually periodic, at every starting value. -/
theorem all_rows_eventually_periodic (k : ℕ) : EventuallyPeriodic (row k) :=
  periodic_of_bounded (isRow k) (value_le_square k)

end SelfBanning
