import Mathlib.Combinatorics.SimpleGraph.Metric
import Lean.Elab.Tactic.Omega

namespace Graffiti

open SimpleGraph

/-- A breadth-first distance certificate: adjacent labels differ by at most
one; every nonroot vertex has a neighbor with label one smaller. -/
theorem distance_label {V : Type*} {G : SimpleGraph V} (hc : G.Connected) (r : V) (d : V → ℕ)
    (base : d r = 0) (edge : ∀ x y, G.Adj x y → d x ≤ d y + 1)
    (down : ∀ x ≠ r, ∃ y, G.Adj x y ∧ d y + 1 = d x) (x : V) : G.dist x r = d x := by
  have along {a b : V} (p : G.Walk a b) : d a ≤ p.length + d b := by
    induction p with
    | nil => simp
    | cons e _ ih => have := edge _ _ e; simp only [Walk.length_cons]; omega
  apply le_antisymm
  · induction x using (measure d).wf.induction with
    | h x ih =>
      by_cases eq : x = r
      · simp [eq,dist_self,base]
      obtain ⟨y,ha,hy⟩ := down x eq
      have step := ih y (show d y < d x by omega)
      have tri := hc.dist_triangle (u := x) (v := y) (w := r)
      rw [dist_eq_one_iff_adj.mpr ha] at tri
      omega
  · obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist x r
    simpa [hp,base] using along p

end Graffiti
