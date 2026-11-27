import Graffiti434d
import Mathlib.Algebra.Group.Fin.Basic

namespace Graffiti

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Two distinct neighbors exhaust the neighborhood in maximum degree two. -/
private theorem only_neighbors (hd : ∀ v, G.degree v ≤ 2) {v x y z : V}
    (hx : G.Adj v x) (hy : G.Adj v y) (hxy : x ≠ y) (hz : G.Adj v z) : z = x ∨ z = y := by
  have hs : ({x,y} : Finset V) ⊆ G.neighborFinset v := by
    simpa [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hx hy
  have he := Finset.eq_of_subset_of_card_le hs (by simpa [Finset.card_pair hxy] using hd v)
  have hm := (G.mem_neighborFinset v z).mpr hz
  simpa [← he] using hm

omit [DecidableEq V] [DecidableRel G.Adj] in
private theorem longest_path (hc : G.Connected) :
    ∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ ∀ {c d} (q : G.Walk c d), q.IsPath → q.length ≤ p.length := by
  classical
  let S := (Finset.range (Fintype.card V)).filter (fun k => ∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ p.length = k)
  obtain ⟨u⟩ := hc.nonempty
  have mem {a b} (p : G.Walk a b) (hp : p.IsPath) : p.length ∈ S :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hp.length_lt, a,b,p,hp,rfl⟩
  have hS : S.Nonempty := ⟨_, mem (.nil : G.Walk u u) (by simp)⟩
  obtain ⟨a,b,p,hp,hl⟩ := (Finset.mem_filter.mp (S.max'_mem hS)).2
  exact ⟨a,b,p,hp,fun q hq => hl ▸ S.le_max' _ (mem q hq)⟩

/-- A longest path orders all vertices. Interior vertices already use both edges, so the only
possible nonconsecutive edge joins the endpoints. -/
private theorem graph_order (hc : G.Connected) (hd : ∀ v, G.degree v ≤ 2) :
    ∃ (n : ℕ) (e : Fin (n+1) ≃ V),
      (∀ i j : Fin (n+1), i.val + 1 = j.val → G.Adj (e i) (e j)) ∧
      ∀ i j : Fin (n+1), G.Adj (e i) (e j) → i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
        (i.val = 0 ∧ j.val = n) ∨ (j.val = 0 ∧ i.val = n) := by
  classical
  obtain ⟨a,b,p,hp,hmax⟩ := longest_path hc
  have middle {i : ℕ} (hi : 0 < i) (hi' : i < p.length) {v : V} (hv : G.Adj (p.getVert i) v) :
      v = p.getVert (i-1) ∨ v = p.getVert (i+1) := by
    have hprev := (p.adj_getVert_succ (i := i-1) (by omega)).symm
    rw [show i-1+1 = i by omega] at hprev
    apply only_neighbors hd hprev (p.adj_getVert_succ hi') _ hv
    intro he
    have := hp.getVert_injOn (show i-1 ≤ p.length by omega) (show i+1 ≤ p.length by omega) he
    omega
  have covered (v : V) : v ∈ p.support := by
    by_contra hn
    obtain ⟨q⟩ := hc a v
    obtain ⟨d,_,hu,hv⟩ := q.exists_boundary_dart {x | x ∈ p.support} p.start_mem_support hn
    obtain ⟨i,hi,hib⟩ := Walk.mem_support_iff_exists_getVert.mp hu
    have hadj : G.Adj (p.getVert i) d.snd := hi ▸ d.adj
    by_cases h0 : i = 0
    · subst i
      have edge : G.Adj d.snd a := by simpa using hadj.symm
      have h := hmax (p.cons edge) ((Walk.cons_isPath_iff _ _).mpr ⟨hp,hv⟩)
      simp at h
    by_cases he : i = p.length
    · rw [he, Walk.getVert_length] at hadj
      have h := hmax (p.reverse.cons hadj.symm) ((Walk.cons_isPath_iff _ _).mpr
        ⟨hp.reverse,by simpa [Walk.support_reverse] using hv⟩)
      simp at h
    rcases middle (by omega) (by omega) hadj with he | he <;> exact hv (he ▸ p.getVert_mem_support _)
  let f : Fin (p.length+1) → V := fun i => p.getVert i.val
  have inj : Function.Injective f := fun i j hij => Fin.ext (hp.getVert_injOn
    (Nat.le_of_lt_succ i.isLt) (Nat.le_of_lt_succ j.isLt) hij)
  have surj : Function.Surjective f := by
    intro v
    obtain ⟨i,hi,hb⟩ := Walk.mem_support_iff_exists_getVert.mp (covered v)
    exact ⟨⟨i,by omega⟩,hi⟩
  refine ⟨p.length, Equiv.ofBijective f ⟨inj,surj⟩, ?_, ?_⟩
  · intro i j hij
    change G.Adj (p.getVert i.val) (p.getVert j.val)
    rw [← hij]
    exact p.adj_getVert_succ (by have := j.isLt; omega)
  · intro i j h
    change G.Adj (p.getVert i.val) (p.getVert j.val) at h
    have aux {s t : Fin (p.length+1)} (hs : 0 < s.val) (hs' : s.val < p.length)
        (ht : G.Adj (p.getVert s.val) (p.getVert t.val)) :
        s.val + 1 = t.val ∨ t.val + 1 = s.val := by
      have hb := Nat.le_of_lt_succ t.isLt
      rcases middle hs hs' ht with he | he
      · have := hp.getVert_injOn hb (show s.val-1 ≤ p.length by omega) he
        omega
      · have := hp.getVert_injOn hb (show s.val+1 ≤ p.length by omega) he
        omega
    have hi := i.isLt
    have hj := j.isLt
    have hne : i.val ≠ j.val := fun eq => h.ne (congrArg p.getVert eq)
    by_cases hii : 0 < i.val ∧ i.val < p.length
    · have := aux hii.1 hii.2 h; tauto
    by_cases hjj : 0 < j.val ∧ j.val < p.length
    · have := aux hjj.1 hjj.2 h.symm; omega
    omega

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem walk_label_bound (label : V → ℕ) (h : ∀ {u v}, G.Adj u v → label v ≤ label u + 1)
    {u v : V} (p : G.Walk u v) : label v ≤ label u + p.length := by
  induction p with
  | nil => simp
  | cons he p ih => have := h he; simp only [Walk.length_cons]; omega

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem chain_distance (hc : G.Connected) {n : ℕ} (e : Fin (n+1) ≃ V)
    (step : ∀ i j : Fin (n+1), i.val + 1 = j.val → G.Adj (e i) (e j))
    (i j : Fin (n+1)) (hij : i.val ≤ j.val) : G.dist (e i) (e j) ≤ j.val - i.val := by
  obtain ⟨j,hj⟩ := j
  change i.val ≤ j at hij
  induction j with
  | zero =>
    have he : i = ⟨0,hj⟩ := Fin.ext (Nat.eq_zero_of_le_zero hij)
    simp [he, dist_self]
  | succ j ih =>
    by_cases he : i.val = j+1
    · have h : i = ⟨j+1,hj⟩ := Fin.ext he
      simp [h,dist_self]
    let k : Fin (n+1) := ⟨j,by omega⟩
    have hprev := ih k.isLt (by omega)
    have hedge : G.dist (e k) (e ⟨j+1,hj⟩) = 1 := dist_eq_one_iff_adj.mpr (step _ _ rfl)
    have ht := hc.dist_triangle (u := e i) (v := e k) (w := e ⟨j+1,hj⟩)
    change G.dist (e i) (e k) ≤ j-i.val at hprev
    change G.dist (e i) (e ⟨j+1,hj⟩) ≤ j+1-i.val
    omega

omit [DecidableEq V] [DecidableRel G.Adj] in
private theorem path_peripheral (hc : G.Connected) {n : ℕ} (e : Fin (n+1) ≃ V)
    (step : ∀ i j : Fin (n+1), i.val + 1 = j.val → G.Adj (e i) (e j))
    (lin : ∀ i j : Fin (n+1), G.Adj (e i) (e j) → i.val+1 = j.val ∨ j.val+1 = i.val)
    (i : Fin (n+1)) (hi : e i ∈ peripheralVertices G) : i.val = 0 ∨ i.val = n := by
  classical
  letI : Nonempty V := hc.nonempty
  have hlabel {u v : V} (h : G.Adj u v) : (e.symm v).val ≤ (e.symm u).val + 1 := by
    have := lin (e.symm u) (e.symm v) (by simpa using h); omega
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist (e 0) (e (Fin.last n))
  have hl := walk_label_bound (fun v => (e.symm v).val) @hlabel p
  simp only [e.symm_apply_apply, Fin.val_zero, Fin.val_last, zero_add, hp] at hl
  have hdiam := (dist_le_diam (connected_iff_ediam_ne_top.mp hc) (u := e 0) (v := e (Fin.last n)))
  obtain ⟨y,hy⟩ := G.exists_edist_eq_eccent_of_finite (e i)
  obtain ⟨j,rfl⟩ := e.surjective y
  have hper : G.eccent (e i) = G.ediam := (Finset.mem_filter.mp hi).2
  have hdist : G.dist (e i) (e j) = G.diam := congrArg ENat.toNat (hy.trans hper)
  have hib := i.isLt
  have hjb := j.isLt
  rcases le_total i.val j.val with h | h
  · have := chain_distance hc e step i j h; omega
  · have hu := chain_distance hc e step j i h
    rw [dist_comm] at hu; omega

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem eccent_hom_le (hc : G.Connected) (f : G →g G) (hs : Function.Surjective f) (x : V) :
    G.eccent (f x) ≤ G.eccent x := by
  apply iSup_le
  intro y
  obtain ⟨z,rfl⟩ := hs y
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_edist x z
  calc G.edist (f x) (f z) ≤ (p.map f).length := edist_le _
       _ = G.edist x z := by simpa using hp
       _ ≤ G.eccent x := edist_le_eccent

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- In the closed-path case, translations of the cyclic ordering take any vertex to any other. -/
private theorem cycle_peripheral (hc : G.Connected) {n : ℕ} (e : Fin (n+1) ≃ V)
    (cy : ∀ i j : Fin (n+1), G.Adj (e i) (e j) ↔ j = i+1 ∨ i = j+1) (x : V) :
    x ∈ peripheralVertices G := by
  classical
  letI : Nonempty V := hc.nonempty
  obtain ⟨y,hy⟩ := G.exists_eccent_eq_ediam_of_finite (α := V)
  let k := e.symm y - e.symm x
  let t : V ≃ V := (e.symm.trans (Equiv.addRight k)).trans e
  have apply_t (v : V) : t v = e (e.symm v + k) := rfl
  let f : G →g G :=
    { toFun := t
      map_rel' := by
        intro u v huv
        rw [apply_t,apply_t,cy]
        rcases (cy (e.symm u) (e.symm v)).mp (by simpa using huv) with h | h
        · left; rw [h]; ac_rfl
        · right; rw [h]; ac_rfl }
  have h := eccent_hom_le hc f t.surjective x
  have hf : f x = y := by change e (e.symm x + (e.symm y - e.symm x)) = y; simp
  rw [hf,hy] at h
  simpa [peripheralVertices] using (le_antisymm (eccent_le_ediam (G := G) (u := x)) h)

/-- In a connected graph of maximum degree two, at most two nonperipheral vertices are adjacent
 to a peripheral vertex. This includes two-vertex paths. -/
theorem peripheral_external_card_le_two (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (hd : ∀ v, G.degree v ≤ 2) :
    ((Finset.univ : Finset V).filter (fun x => x ∉ peripheralVertices G ∧
      ∃ y ∈ peripheralVertices G, G.Adj x y)).card ≤ 2 := by
  classical
  letI : Nonempty V := hc.nonempty
  obtain ⟨n,e,step,edges⟩ := graph_order hc hd
  by_cases closed : G.Adj (e 0) (e (Fin.last n))
  · have next (i j : Fin (n+1)) : j = i+1 ↔
        i.val+1 = j.val ∨ (i.val = n ∧ j.val = 0) := by
      rw [Fin.ext_iff, Fin.val_add_one]
      by_cases hi : i = Fin.last n
      · simp [hi]; omega
      · have hlt : i.val < n := by have := i.isLt; have h := mt (@Fin.ext _ i (Fin.last n)) hi; simp at h; omega
        simp [hi]; omega
    have cy (i j : Fin (n+1)) : G.Adj (e i) (e j) ↔ j = i+1 ∨ i = j+1 := by
      rw [next,next]
      constructor
      · intro h; have := edges i j h; tauto
      · rintro ((h | ⟨hi,hj⟩) | (h | ⟨hj,hi⟩))
        · exact step i j h
        · have ei : i = Fin.last n := Fin.ext hi
          have ej : j = 0 := Fin.ext hj
          simpa [ei,ej] using closed.symm
        · exact (step j i h).symm
        · have ej : j = Fin.last n := Fin.ext hj
          have ei : i = 0 := Fin.ext hi
          simpa [ei,ej] using closed
    have all := cycle_peripheral hc e cy
    simp [all]
  · have lin (i j : Fin (n+1)) (h : G.Adj (e i) (e j)) : i.val+1 = j.val ∨ j.val+1 = i.val := by
      rcases edges i j h with h' | h' | ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
      · exact Or.inl h'
      · exact Or.inr h'
      · exact (closed (by simpa [show i = 0 from Fin.ext h₁, show j = Fin.last n from Fin.ext h₂] using h)).elim
      · exact (closed (by simpa [show j = 0 from Fin.ext h₁, show i = Fin.last n from Fin.ext h₂] using h.symm)).elim
    let a : Fin (n+1) := ⟨min 1 n, by omega⟩
    let b : Fin (n+1) := ⟨n-1, by omega⟩
    apply (Finset.card_le_card (t := {e a, e b}) ?_).trans Finset.card_le_two
    intro x hx
    obtain ⟨_,y,hy,hxy⟩ := (Finset.mem_filter.mp hx).2
    obtain ⟨i,rfl⟩ := e.surjective x
    obtain ⟨j,rfl⟩ := e.surjective y
    have hz := path_peripheral hc e step lin j hy
    have ha := lin i j hxy
    have hi := i.isLt
    have hb : i = a ∨ i = b := by
      rcases hz with hz | hz
      · left; apply Fin.ext; change i.val = min 1 n; omega
      · right; apply Fin.ext; change i.val = n-1; omega
    rcases hb with rfl | rfl <;> simp

end Graffiti
