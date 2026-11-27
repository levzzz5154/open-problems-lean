import DivisorAdj.Records
import DivisorAdj.FirstEight

/-! # Exact first occurrences for the first 150 values of OEIS A251758

`primeRun` constructs a proposed prime prefix using only the reciprocal products
of adjacent primes. `ListedChecks` verifies the proposal by the independent
least-index theorem; no comparison of all earlier indices is performed. -/

namespace DivisorAdj

private def stopAt (k last : ℕ) (s : ℚ) : List ℕ → List ℕ
  | [] => []
  | p :: ps =>
    let t := s + 1 / ((last : ℚ)*p)
    p :: (if 1 < ((k : ℚ)+1)*t then [] else stopAt k p t ps)

def primeRun (k ceiling : ℕ) : List ℕ :=
  stopAt k 1 0 ((List.range' k (ceiling+1-k)).filter fun p => decide p.Prime)

/-- Candidate, not assumed correct for arbitrary targets or cutoffs. -/
def firstCandidate (k ceiling : ℕ) : ℕ :=
  if k.Prime then k else if (k+1).Prime then (k+1)^2 else (primeRun k ceiling).prod

private def listedChecks (k : ℕ) (ps : List ℕ) : Prop :=
  let m := ps.length-1
  let P (i : Fin (m+1)) := ps.getD i.val 0
  0 < m ∧ TableChecks k P ∧ (∏ i, P i) = ps.prod

private instance (k : ℕ) (ps : List ℕ) : Decidable (listedChecks k ps) := by
  unfold listedChecks; infer_instance

private theorem listed_least {k : ℕ} {ps : List ℕ} (h : listedChecks k ps) :
    IsLeast {n : ℕ | 2 ≤ n ∧ a n = k} ps.prod := by
  let m := ps.length-1
  let P (i : Fin (m+1)) := ps.getD i.val 0
  obtain ⟨hm,hc,he⟩ := h
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  exact he ▸ first_of_table hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
private theorem check_tables : ∀ i : Fin 151, 0 < i.val → i.val ≠ 8 → ¬ i.val.Prime →
    ¬ (i.val+1).Prime → listedChecks i.val (primeRun i.val 300) := by decide +kernel

/-- The first index is fully determined for *every* value from 1 through 150. -/
theorem first_through_150 {k : ℕ} (hk : 0 < k) (hK : k ≤ 150) :
    IsLeast {n : ℕ | 2 ≤ n ∧ a n = k} (firstCandidate k 300) := by
  by_cases hp : k.Prime
  · simpa [firstCandidate,hp] using first_prime hp
  by_cases hs : (k+1).Prime
  · simpa [firstCandidate,hp,hs] using first_prime_pred hs (by simpa using hp)
  by_cases he : k = 8
  · subst k; rw [show firstCandidate 8 300 = 35336848261 by decide +kernel]; exact first_eight
  simpa only [firstCandidate,if_neg hp,if_neg hs] using
    listed_least (check_tables ⟨k,by omega⟩ hk he hp hs)

end DivisorAdj
