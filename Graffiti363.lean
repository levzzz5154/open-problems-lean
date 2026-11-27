import Graffiti.ParentForest
import Graffiti.DistanceLabels
import Graffiti365
import Graffiti235

/-! # Counterexample to Written on the Wall II, Graffiti.pc 363

Take the path `0,…,14`. Attach one leaf at each of `3,6,8,11`, and 32
further leaves at `6`. Adding those leaves does not change the periphery,
supports or total domination number. It raises the average distance to the
periphery just past the conjectured threshold: `295/49 > 6`.
An earlier 27-vertex counterexample and infinite family (Gebendorfer):
https://github.com/google-deepmind/formal-conjectures/issues/7360 .

UHD definition 55: boundary means periphery. Definition 109: average the
*positive distances to the set*, not the distances between pairs of members.
https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json
https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/definitions.json
-/

namespace Graffiti

open Finset SimpleGraph SupportCounting

noncomputable def distanceToVertices {V : Type*} (G : SimpleGraph V) (S : Finset V) (x : V) : ℕ :=
  sInf {k | ∃ y ∈ S, G.dist x y = k}

private theorem distanceToVertices_pair {V : Type*} [DecidableEq V] (G : SimpleGraph V) (a b x : V) :
    distanceToVertices G {a,b} x = min (G.dist x a) (G.dist x b) := by
  let U : Set ℕ := {k | ∃ y ∈ ({a,b} : Finset V), G.dist x y = k}
  have ha : G.dist x a ∈ U := ⟨a,mem_insert_self ..,rfl⟩
  have hb : G.dist x b ∈ U := ⟨b,mem_insert_of_mem (mem_singleton_self _),rfl⟩
  apply le_antisymm (le_min (Nat.sInf_le ha) (Nat.sInf_le hb))
  obtain ⟨y,hy,he⟩ := Nat.sInf_mem (show U.Nonempty from ⟨_,ha⟩)
  rw [← he]
  rcases mem_insert.mp hy with rfl | h
  · exact min_le_left ..
  · rw [mem_singleton.mp h]; exact min_le_right ..

namespace PeripheralMean

abbrev Vertex := Fin 51

private def foot (x : Vertex) : Vertex :=
  if x.val < 15 then x else if x = 15 then 3 else if x = 17 then 8 else if x = 18 then 11 else 6

def parent (x : Vertex) : Vertex := if x.val < 15 then ⟨x.val-1,by omega⟩ else foot x

abbrev tree := ParentForest.graph parent

private theorem connected : tree.Connected :=
  ParentForest.connected_of_unique_root parent Fin.val (by decide) 0 (by decide)

theorem isTree : tree.IsTree := by
  have hs : (∑ x, tree.degree x) = 100 := by decide
  have he := tree.sum_degrees_eq_twice_card_edges
  apply isTree_iff_connected_and_card.mpr
  refine ⟨connected,?_⟩
  rw [Nat.card_eq_fintype_card,← edgeFinset_card,Nat.card_eq_fintype_card,Fintype.card_fin]
  omega

private def supports : Finset Vertex := {1,3,6,8,11,13}
private def leaves : Finset Vertex := univ.filter fun v => v = 0 ∨ v = 14 ∨ 15 ≤ v.val

private theorem sups : supportVertices tree = supports := by
  have l : degreeClass tree 1 = leaves := by decide
  unfold supportVertices; rw [l]; decide

theorem isolate_count : (isolatedSupports tree).card = 6 := by rw [isolatedSupports,sups]; decide

theorem total_number : totalDominationNumber tree = 9 := by
  let D₀ := supports ∪ ({2,7,12} : Finset Vertex)
  have h₀ : TotallyDominates tree D₀ := by unfold TotallyDominates; decide
  have upper : totalDominationNumber tree ≤ 9 := Nat.sInf_le ⟨_,h₀,by decide⟩
  obtain ⟨D,hD,he⟩ := exists_min_total_set connected
  have forced : supports ⊆ D := sups ▸ support_forced tree hD
  let W : Finset Vertex := {1,6,13}
  have bound := forced_plus_disjoint_neighborhoods tree (W := W) hD forced (by decide) (by decide)
  have hs : supports.card = 6 := by decide
  have hw : W.card = 3 := by decide
  omega

private def mark : Finset Vertex := {0,7,14}
private def label (r x : Vertex) : ℕ :=
  max r.val (foot x).val - min r.val (foot x).val + if x.val < 15 then 0 else 1

set_option maxRecDepth 8192 in
private theorem distances {r : Vertex} (hr : r ∈ mark) (x : Vertex) : tree.dist x r = label r x := by
  have z : ∀ r ∈ mark, label r r = 0 := by decide
  have e : ∀ r ∈ mark, ∀ x y, tree.Adj x y → label r x ≤ label r y + 1 := by decide
  have d : ∀ r ∈ mark, ∀ x ≠ r, ∃ y, tree.Adj x y ∧ label r y + 1 = label r x := by decide
  exact distance_label connected r _ (z r hr) (e r hr) (d r hr) x

private theorem via_middle (x y : Vertex) : tree.dist x y ≤ label 7 x + label 7 y := by
  have h := connected.dist_triangle (u := x) (v := 7) (w := y)
  rwa [dist_comm (u := (7 : Vertex)) (v := y),distances (r := 7) (by decide),distances (r := 7) (by decide)] at h

private theorem cap : ∀ x, label 7 x ≤ 7 := by decide
private theorem end_dist : tree.dist 14 0 = 14 := (distances (r := 0) (by decide) 14).trans (by decide)

theorem diameter : tree.diam = 14 := by
  have low := tree.dist_le_diam (connected_iff_ediam_ne_top.mp connected) (u := 14) (v := 0)
  obtain ⟨a,b,hab⟩ := tree.exists_dist_eq_diam
  have := via_middle a b; have := cap a; have := cap b
  rw [end_dist] at low
  omega

theorem periphery : peripheralVertices tree = {0,14} := by
  ext x; constructor
  · intro hx
    obtain ⟨z,ez⟩ := tree.exists_edist_eq_eccent_of_finite x
    have eq : tree.dist x z = tree.diam := congrArg ENat.toNat (ez.trans (mem_filter.mp hx).2)
    have h := via_middle x z
    rw [eq,diameter] at h
    have hz := cap z
    have char_ : ∀ v, 7 ≤ label 7 v → v ∈ ({0,14} : Finset Vertex) := by decide
    exact char_ x (by omega)
  · intro hx
    rcases mem_insert.mp hx with rfl | h
    · exact peripheral_of_dist_eq_diam connected (y := 14) (by rw [dist_comm,end_dist,diameter])
    · rw [mem_singleton.mp h]
      exact peripheral_of_dist_eq_diam connected (y := 0) (by rw [end_dist,diameter])

theorem peripheral_mean : (peripheralVertices tree)ᶜ.card = 49 ∧
    (∑ v ∈ (peripheralVertices tree)ᶜ, distanceToVertices tree (peripheralVertices tree) v) = 295 := by
  rw [periphery]
  refine ⟨by decide,?_⟩
  have eq (v : Vertex) : distanceToVertices tree {0,14} v = min (label 0 v) (label 14 v) := by
    rw [distanceToVertices_pair,distances (r := 0) (by decide),distances (r := 14) (by decide)]
  simp_rw [eq]; decide

/-- The catalog lower bound, after multiplying by twice the positive
sample size, would require `882 ≥ 883`. -/
theorem graffiti363_counterexample : tree.IsTree ∧ 2 < Fintype.card Vertex ∧
    2*(peripheralVertices tree)ᶜ.card*totalDominationNumber tree <
      2*(peripheralVertices tree)ᶜ.card*(isolatedSupports tree).card +
      ∑ v ∈ (peripheralVertices tree)ᶜ, distanceToVertices tree (peripheralVertices tree) v := by
  exact ⟨isTree,by decide,by rw [total_number,isolate_count,peripheral_mean.1,peripheral_mean.2]; decide⟩

end PeripheralMean
end Graffiti
