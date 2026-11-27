import Graffiti.ForcedSupports
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace Graffiti

open Finset SimpleGraph SupportCounting

variable {V : Type*} [Fintype V]

noncomputable def degreeTwoComponents (T : SimpleGraph V) [DecidableRel T.Adj] : ℕ :=
  Nat.card (T.induce ((degreeClass T 2 : Finset V) : Set V)).ConnectedComponent

private abbrev twoGraph (T : SimpleGraph V) [DecidableRel T.Adj] :=
  T.induce ((degreeClass T 2 : Finset V) : Set V)

variable {T : SimpleGraph V} [DecidableRel T.Adj]

private theorem neighbor_pair {v x y z : V} (hd : T.degree v = 2) (hx : T.Adj v x)
    (hy : T.Adj v y) (hxy : x ≠ y) (hz : T.Adj v z) : z = x ∨ z = y := by
  classical
  have hs : ({x,y} : Finset V) ⊆ T.neighborFinset v := by
    simpa [insert_subset_iff, singleton_subset_iff] using And.intro hx hy
  have he := eq_of_subset_of_card_le hs (by simpa [card_pair hxy] using hd.le)
  simpa [← he] using (T.mem_neighborFinset v z).mpr hz

/-- Along the degree-two path every neighbor is accounted for by its predecessor
or successor, including the two prescribed neighbors just beyond the endpoints. -/
private theorem path_closed {a b : ↥(degreeClass T 2)} (p : (twoGraph T).Walk a b)
    (hp : p.IsPath) {P : V → Prop} (inside : ∀ z ∈ p.support, P z.val)
    {l r : V} (hl : T.Adj a.val l) (hr : T.Adj b.val r) (pl : P l) (pr : P r)
    (fresh : ∀ z ∈ p.support, z.val ≠ l) (dr : T.degree r = 1) (hne : l ≠ r) :
    ∀ z ∈ p.support, ∀ w, T.Adj z.val w → P w := by
  induction p generalizing l with
  | @nil a =>
    intro z hz w hw
    simp only [Walk.support_nil, List.mem_singleton] at hz
    subst z
    rcases neighbor_pair ((mem_degreeClass T).mp a.property) hl hr hne hw with h | h
    · exact h ▸ pl
    · exact h ▸ pr
  | @cons a c b e p ih =>
    have nd := hp.support_nodup
    rw [Walk.support_cons, List.nodup_cons] at nd
    intro z hz w hw
    rcases List.mem_cons.mp hz with rfl | hz
    · have hc := p.start_mem_support
      rcases neighbor_pair ((mem_degreeClass T).mp z.property) hl (show T.Adj z.val c.val from e)
          (fresh c (List.mem_cons_of_mem _ hc)).symm hw with h | h
      · exact h ▸ pl
      · exact h ▸ inside c (List.mem_cons_of_mem _ hc)
    · apply ih hp.of_cons (fun x hx => inside x (List.mem_cons_of_mem _ hx))
          (show T.Adj c.val a.val from T.symm e) hr (inside a List.mem_cons_self)
          (fun x hx h => nd.1 ((Subtype.ext h : x = a) ▸ hx)) _ _ hz _ hw
      intro h
      have ha := (mem_degreeClass T).mp a.property
      rw [h, dr] at ha
      contradiction

omit [Fintype V] in
private theorem walk_closed {G : SimpleGraph V} {P : V → Prop}
    (step : ∀ u, P u → ∀ v, G.Adj u v → P v) {a b : V} (p : G.Walk a b) : P a → P b := by
  induction p with
  | nil => exact id
  | cons e _ ih => exact fun ha => ih (step _ ha _ e)

/-- Distinct support ends in one degree-two component saturate a path from leaf
 to leaf. By connectedness no vertex can lie outside this path. -/
theorem two_support_ends [DecidableEq V] (ht : T.IsTree) (_hn : 2 < Fintype.card V) :
    (supportVertices T ∩ degreeClass T 2).card ≤ degreeTwoComponents T ∨
    (degreeTwoComponents T = 1 ∧ (supportVertices T ∩ degreeClass T 2).card ≤ 2) := by
  classical
  let S := supportVertices T ∩ degreeClass T 2
  let vert (x : ↥S) : ↥(degreeClass T 2) := ⟨x.val, (mem_inter.mp x.property).2⟩
  let f (x : ↥S) := (twoGraph T).connectedComponentMk (vert x)
  letI : Finite (twoGraph T).ConnectedComponent :=
    Finite.of_surjective (twoGraph T).connectedComponentMk Quot.mk_surjective
  letI : Fintype (twoGraph T).ConnectedComponent := Fintype.ofFinite _
  by_cases inj : Function.Injective f
  · left
    change S.card ≤ Nat.card (twoGraph T).ConnectedComponent
    rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
    exact Fintype.card_le_of_injective f inj
  right
  unfold Function.Injective at inj
  push_neg at inj
  obtain ⟨x,y,hc,hxy⟩ := inj
  obtain ⟨l,dl,el⟩ := (support_iff_pendant T).mp (mem_inter.mp x.property).1
  obtain ⟨r,dr,er⟩ := (support_iff_pendant T).mp (mem_inter.mp y.property).1
  have lr : l ≠ r := by
    rintro rfl
    exact hxy (Subtype.ext (unique_neighbor_at_leaf T dl el.symm er.symm))
  obtain ⟨p,hp⟩ := (ConnectedComponent.exact hc).exists_isPath
  let P (v : V) := v = l ∨ v = r ∨ ∃ z ∈ p.support, z.val = v
  have inside : ∀ z ∈ p.support, P z.val := fun z hz => Or.inr (Or.inr ⟨z,hz,rfl⟩)
  have fresh (z : ↥(degreeClass T 2)) (a : V) (ha : T.degree a = 1) : z.val ≠ a := by
    intro h
    have hz := (mem_degreeClass T).mp z.property
    rw [h,ha] at hz
    contradiction
  have step (v : V) (hv : P v) (w : V) (hw : T.Adj v w) : P w := by
    rcases hv with rfl | rfl | ⟨z,hz,rfl⟩
    · rw [unique_neighbor_at_leaf T dl hw el.symm]; exact inside _ p.start_mem_support
    · rw [unique_neighbor_at_leaf T dr hw er.symm]; exact inside _ p.end_mem_support
    · exact path_closed p hp inside el er (Or.inl rfl) (Or.inr (Or.inl rfl))
        (fun t _ => fresh t l dl) dr lr z hz w hw
  have allP (v : V) : P v := (ht.isConnected l v).elim fun q => walk_closed step q (Or.inl rfl)
  have uniqueC (z : ↥(degreeClass T 2)) : (twoGraph T).connectedComponentMk z = f x := by
    rcases allP z.val with h | h | ⟨u,hu,h⟩
    · exact (fresh z l dl h).elim
    · exact (fresh z r dr h).elim
    · obtain rfl : u = z := Subtype.ext h
      exact (ConnectedComponent.sound ⟨p.takeUntil u hu⟩).symm
  constructor
  · letI : Unique (twoGraph T).ConnectedComponent :=
      { default := f x, uniq := fun c => ConnectedComponent.ind uniqueC c }
    exact Nat.card_unique
  · have hs : S ⊆ {x.val,y.val} := by
      intro v hv
      obtain ⟨w,dw,e⟩ := (support_iff_pendant T).mp (mem_inter.mp hv).1
      rcases allP w with rfl | rfl | ⟨z,_,rfl⟩
      · simp [unique_neighbor_at_leaf T dl e.symm el.symm]
      · simp [unique_neighbor_at_leaf T dr e.symm er.symm]
      · exact (fresh z _ dw rfl).elim
    exact (card_le_card hs).trans (card_insert_le .. |>.trans (by simp))

end Graffiti
