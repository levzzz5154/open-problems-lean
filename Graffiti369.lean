import Graffiti258
import Graffiti.ParentForest
import Mathlib.Data.Multiset.Sort

/-! # Written on the Wall II, Graffiti.pc 369: counterexample

Take the path `0–1–2–3–4–5–6–7–8` and attach leaves to `0,1,3,4,7,8`
until all six vertices have degree five. These vertices are forced by their
leaves and totally dominate in pairs. There are 29 vertices; the sole degree
mode is 1, and the first Havel–Hakimi zero occurs on step 6.

The related published Figure 5 of DeLaViña, Larson, Pepper and Waller is a
counterexample to *368*, with total domination number and first-zero step both
8. Here the smaller witness has odd order, so the parity factor in 369 is 1.
The identical witness and its exact invariants also appear in adamben04's
earlier https://github.com/adamben04/graffiti-pc-369-counterexample .
As in that reference a unique modal degree contributes one. Catalog
definition 45 states the count explicitly only in the presence of ties.

Sources: https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json
and `definitions.json` (entries 45 and 110); https://www.uhd.edu/documents/academics/sciences/boca2009-dlpw.pdf#page=13
-/

namespace Graffiti.FirstZero
open Finset SimpleGraph

/-- Degree sequence in nonincreasing order, with multiplicities. -/
def degrees {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : List ℕ :=
  ((univ : Finset V).val.map (fun v => G.degree v)).sort (· ≥ ·)

/-- All occurring degrees of greatest multiplicity, retaining ties. -/
def modes (ds : List ℕ) : Finset ℕ :=
  ds.toFinset.filter fun d => ∀ e ∈ ds.toFinset, ds.count e ≤ ds.count d

/-- One Havel–Hakimi step on a nonincreasing list. Sort the result before
returning it, so iteration always takes the next largest entry. -/
def step : List ℕ → List ℕ
  | [] => []
  | d :: rest => (((rest.take d).map Nat.pred) ++ rest.drop d).insertionSort (· ≥ ·)

/-- First positive iteration whose resulting sequence contains a zero. -/
noncomputable def firstZeroStep (ds : List ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ 0 ∈ step^[k] ds}

private def parent (v : Fin 29) : Fin 29 :=
  if v.val < 9 then ⟨v.val - 1, by omega⟩ else
  if v.val < 13 then 0 else if v.val < 16 then 1 else if v.val < 19 then 3 else
  if v.val < 22 then 4 else if v.val < 25 then 7 else 8

abbrev tree := ParentForest.graph parent

private def centers : Finset (Fin 29) := {0,1,3,4,7,8}

private def ds : List ℕ := List.replicate 6 5 ++ List.replicate 3 2 ++ List.replicate 20 1

private theorem tree_isTree : tree.IsTree := by
  have hc := ParentForest.connected_of_unique_root parent Fin.val (by decide) 0 (by decide)
  have hs : (∑ v, tree.degree v) = 56 := by decide
  have he := tree.sum_degrees_eq_twice_card_edges
  apply isTree_iff_connected_and_card.mpr
  refine ⟨hc, ?_⟩
  rw [Nat.card_eq_fintype_card, ← edgeFinset_card, Nat.card_eq_fintype_card, Fintype.card_fin]
  omega

private theorem total_number : totalDominationNumber tree = 6 := by
  have witness : TotallyDominates tree centers := by unfold TotallyDominates; decide
  have size : centers.card = 6 := by decide
  apply le_antisymm
  · exact Nat.sInf_le ⟨centers,witness,size⟩
  obtain ⟨D,hD,hsize⟩ := exists_min_total_set tree_isTree.isConnected
  rw [← hsize, ← size]
  apply card_le_card
  have leaves : ∀ s ∈ centers, ∃ l : Fin 29, ∀ y : Fin 29, tree.Adj l y ↔ y = s := by decide
  intro s hs
  obtain ⟨l,hl⟩ := leaves s hs
  obtain ⟨y,hy,had⟩ := hD l
  exact (hl y).mp had ▸ hy

private theorem step_number : firstZeroStep ds = 6 := by
  let S : Set ℕ := {k | 0 < k ∧ 0 ∈ step^[k] ds}
  have hit : 6 ∈ S := by change 0 < 6 ∧ 0 ∈ step^[6] ds; decide
  have early : ∀ i : Fin 6, 0 ∉ step^[i.val] ds := by decide
  change sInf S = 6
  apply le_antisymm (Nat.sInf_le hit)
  have hm := Nat.sInf_mem (show S.Nonempty from ⟨6,hit⟩)
  exact Nat.le_of_not_gt fun h => early ⟨sInf S,h⟩ hm.2

/-- Exact independently checkable invariants of the 29-vertex witness. -/
theorem certificate : tree.IsTree ∧ totalDominationNumber tree = 6 ∧
    modes (degrees tree) = {1} ∧ firstZeroStep (degrees tree) = 6 := by
  have seq : (univ : Finset (Fin 29)).val.map (fun v => tree.degree v) = (ds : Multiset ℕ) := by
    decide
  have hd : degrees tree = ds := by
    rw [degrees,seq,Multiset.coe_sort,List.mergeSort_eq_insertionSort]
    decide
  rw [hd]
  exact ⟨tree_isTree,total_number,by decide,step_number⟩

/-- Negation of the proposed lower bound on a nontrivial tree. -/
theorem graffiti369_counterexample : tree.IsTree ∧ 2 < Fintype.card (Fin 29) ∧
    totalDominationNumber tree < (modes (degrees tree)).card +
      (Fintype.card (Fin 29) % 2) * firstZeroStep (degrees tree) := by
  obtain ⟨ht,hd,hm,hk⟩ := certificate
  exact ⟨ht,by decide,by rw [hd,hm,hk]; decide⟩

end Graffiti.FirstZero

#print axioms Graffiti.FirstZero.graffiti369_counterexample
