import Graffiti369

namespace Graffiti.FirstZero

/-- Vertices of degree at least two, and vertices of degree at least three. -/
def nonleafCount (ds : List ℕ) : ℕ := (ds.filter (fun d => 1 < d)).length
def branchCount (ds : List ℕ) : ℕ := (ds.filter (fun d => 2 < d)).length

/-- Total degree of the nonleaves; on a safe Havel–Hakimi step it drops by six or more. -/
def nonleafWeight (ds : List ℕ) : ℕ := (ds.filter (fun d => 1 < d)).sum

/-- A safe step drops this quantity by at least three, even if there are few branch vertices. -/
def branchBudget (ds : List ℕ) : ℕ := nonleafCount ds + 2*(branchCount ds-2)

end Graffiti.FirstZero
