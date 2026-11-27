import Graffiti.PeripheralTripod
import Graffiti363

namespace Graffiti.PeripheralTripod
open SimpleGraph Finset
variable {m N : ℕ}

private theorem root_bound (x : Vertex m N) : (tree m N).dist x root ≤ depth x := by
  induction x using (measure (@depth m N)).wf.induction with
  | h x ih =>
    by_cases e : x = root
    · simp [e, dist_self]
    have d := parent_depth x e
    have ne : x ≠ parent x := fun h => by rw [← h] at d; omega
    have adj : (tree m N).Adj x (parent x) := ⟨ne, Or.inl rfl⟩
    have h := ih (parent x) (show depth (parent x) < depth x by omega)
    have t := (isTree m N).isConnected.dist_triangle (u := x) (v := parent x) (w := root)
    rw [dist_eq_one_iff_adj.mpr adj] at t
    omega

private theorem via_root (x y : Vertex m N) : (tree m N).dist x y ≤ depth x + depth y := by
  have h := (isTree m N).isConnected.dist_triangle (u := x) (v := root) (w := y)
  rw [dist_comm (u := root) (v := y)] at h
  exact h.trans (Nat.add_le_add (root_bound x) (root_bound y))

private def potential (a : Fin 3) (x : Vertex m N) : ℤ :=
  if arm x = some a then depth x else -(depth x : ℤ)

private theorem parent_step (a : Fin 3) (x : Vertex m N) :
    potential a x ≤ potential a (parent x) + 1 ∧ potential a (parent x) ≤ potential a x + 1 := by
  by_cases e : x = root
  · subst x; simp [parent]
  have d := parent_depth x e
  by_cases h : parent x = root
  · rw [h] at d ⊢
    change 0 + 1 = depth x at d
    have p : potential a (root : Vertex m N) = 0 := by simp [potential, arm, depth]
    rw [p]
    simp only [potential, ← d]; split <;> decide
  · simp only [potential, parent_arm x h]; split <;> constructor <;> omega

private theorem cross_bound (x y : Vertex m N) (a : Fin 3) (hx : arm x = some a)
    (hy : arm y ≠ some a) : depth x + depth y ≤ (tree m N).dist x y := by
  have edge (u v : Vertex m N) (e : (tree m N).Adj u v) : potential a u ≤ potential a v + 1 := by
    rcases e.2 with h | h
    · subst v; exact (parent_step a u).1
    · subst u; exact (parent_step a v).2
  have along {u v : Vertex m N} (p : (tree m N).Walk u v) :
      potential a u ≤ (p.length : ℤ) + potential a v := by
    induction p with
    | nil => simp
    | cons e _ ih => have := edge _ _ e; simp only [Walk.length_cons, Nat.cast_add, Nat.cast_one]; omega
  obtain ⟨p,h⟩ := (isTree m N).isConnected.exists_walk_length_eq_dist x y
  have ineq := along p
  simp [potential, hx, hy, h] at ineq
  omega

private theorem depth_cap (x : Vertex m N) : depth x ≤ 5*m+7 ∧
    (arm x = some 2 → depth x ≤ 5*m+2) := by
  rcases x with ((_|⟨a,i⟩)|⟨⟨a,i⟩,hi⟩)|j
  · simp [depth, arm]
  · have h := i.isLt
    by_cases e : a = 2 <;> simp [depth, arm, blocks, e] at * <;> omega
  · have h := i.isLt
    by_cases e : a = 2 <;> simp [depth, arm, blocks, e] at * <;> omega
  · simp [depth, arm]

private def tip (m N : ℕ) (a : Fin 3) : Vertex m N :=
  sprout ⟨lastSeg m a, Or.inl (by simp [lastSeg])⟩

private theorem tip_depth (a : Fin 3) (ha : a ≠ 2) : depth (tip m N a) = 5*m+7 := by
  simp [tip, depth, lastSeg, blocks, ha, Nat.mul_add]

private theorem tip_dist : (tree m N).dist (tip m N 0) (tip m N 1) = 2*(5*m+7) := by
  have low := cross_bound (tip m N 0) (tip m N 1) 0 rfl (by change some (1 : Fin 3) ≠ some 0; decide)
  have high := via_root (tip m N 0) (tip m N 1)
  rw [tip_depth 0 (by decide), tip_depth 1 (by decide)] at low high
  omega

private theorem diam_eq : (tree m N).diam = 2*(5*m+7) := by
  have lo := (tree m N).dist_le_diam (connected_iff_ediam_ne_top.mp (isTree m N).isConnected)
    (u := tip m N 0) (v := tip m N 1)
  rw [tip_dist] at lo
  letI : Nonempty (Vertex m N) := ⟨root⟩
  obtain ⟨a,b,hab⟩ := (tree m N).exists_dist_eq_diam
  have := via_root a b; have := (depth_cap a).1; have := (depth_cap b).1
  omega

private theorem peripheral_depth (x : Vertex m N) (hx : x ∈ peripheralVertices (tree m N)) :
    depth x = 5*m+7 := by
  obtain ⟨z,h⟩ := (tree m N).exists_edist_eq_eccent_of_finite x
  have eq : (tree m N).dist x z = (tree m N).diam := congrArg ENat.toNat (h.trans (mem_filter.mp hx).2)
  rw [diam_eq] at eq
  have := via_root x z; have := (depth_cap x).1; have := (depth_cap z).1
  omega

theorem bunch_nonperipheral (m N : ℕ) (i : Fin N) : bunch (m:=m) i ∉ peripheralVertices (tree m N) := by
  intro h
  have eq := peripheral_depth _ h
  change 5*m+2 = 5*m+7 at eq
  omega

theorem bunch_distance (m N : ℕ) (i : Fin N) : 10*m+9 ≤
    distanceToVertices (tree m N) (peripheralVertices (tree m N)) (bunch i) := by
  have hm : tip m N 0 ∈ peripheralVertices (tree m N) :=
    peripheral_of_dist_eq_diam (isTree m N).isConnected (y := tip m N 1) (by rw [tip_dist, diam_eq])
  unfold distanceToVertices
  apply le_csInf
  · exact ⟨_, _, hm, rfl⟩
  · rintro k ⟨x,hx,rfl⟩
    have d := peripheral_depth x hx
    have ha : arm x ≠ some 2 := fun h => by have := (depth_cap x).2 h; omega
    have low := cross_bound (bunch i) x 2 rfl ha
    change 5*m+2+depth x ≤ _ at low
    omega

end Graffiti.PeripheralTripod
