import Graffiti434
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.BigOperators

/-! # Certificates for small quotients of graphs with true twins

Replacing a vertex by a nonempty clique of equally connected vertices does
not change which types can occur in an independent dominating set. Degrees
are computed as weighted neighborhood sums. This avoids enumerating subsets
of graphs with hundreds of vertices. -/

namespace Graffiti.CliqueFiber

open SimpleGraph

variable {C : Type*}

abbrev Vertex (w : C → ℕ) := Σ i, Fin (w i)

def liftGraph (Q : SimpleGraph C) (w : C → ℕ) : SimpleGraph (Vertex w) where
  Adj x y := x ≠ y ∧ (x.1 = y.1 ∨ Q.Adj x.1 y.1)
  symm := fun _ _ ⟨ne,h⟩ => ⟨ne.symm,h.elim (fun e => Or.inl e.symm) (fun e => Or.inr e.symm)⟩
  loopless := fun _ h => h.1 rfl

variable [DecidableEq C]

instance (Q : SimpleGraph C) [DecidableRel Q.Adj] (w : C → ℕ) : DecidableRel (liftGraph Q w).Adj :=
  fun x y => inferInstanceAs (Decidable (x ≠ y ∧ (x.1 = y.1 ∨ Q.Adj x.1 y.1)))

def fibers (w : C → ℕ) (S : Finset C) : Finset (Vertex w) := S.sigma (fun _ => Finset.univ)

omit [DecidableEq C] in
@[simp] theorem mem_fibers {w : C → ℕ} {S : Finset C} {x : Vertex w} : x ∈ fibers w S ↔ x.1 ∈ S := by
  simp [fibers]

variable [Fintype C]

def closedWeight (Q : SimpleGraph C) [DecidableRel Q.Adj] (w : C → ℕ) (i : C) : ℕ :=
  ∑ j ∈ Finset.univ.filter (fun j => i = j ∨ Q.Adj i j), w j

omit [DecidableEq C] in
theorem vertex_card (w : C → ℕ) : Fintype.card (Vertex w) = ∑ j, w j := by simp [Vertex]

theorem degree_add_one (Q : SimpleGraph C) [DecidableRel Q.Adj] (w : C → ℕ) (x : Vertex w) :
    (liftGraph Q w).degree x + 1 = closedWeight Q w x.1 := by
  let G := liftGraph Q w
  let T := Finset.univ.filter (fun j => x.1 = j ∨ Q.Adj x.1 j)
  have eq : insert x (G.neighborFinset x) = fibers w T := by
    ext y
    rw [Finset.mem_insert,SimpleGraph.mem_neighborFinset,mem_fibers]
    change y = x ∨ x ≠ y ∧ (x.1 = y.1 ∨ Q.Adj x.1 y.1) ↔ y.1 ∈ T
    by_cases e : y = x
    · subst y; simp [T]
    · simp [T,e,Ne.symm e]
  have hc := congrArg Finset.card eq
  rw [Finset.card_insert_of_not_mem (G.not_mem_neighborFinset_self x)] at hc
  simpa only [SimpleGraph.card_neighborFinset_eq_degree,fibers,Finset.card_sigma,Finset.card_univ,
    Fintype.card_fin,closedWeight,T,G] using hc

def majority (G : SimpleGraph C) [DecidableRel G.Adj] : Finset C :=
  Finset.univ.filter (fun v => Fintype.card C < 2 * G.degree v)

theorem fibers_eq_majority (Q : SimpleGraph C) [DecidableRel Q.Adj] (w : C → ℕ) (M : Finset C)
    (n : ℕ) (hn : ∑ i, w i = n) (h : ∀ i, (n < 2 * (closedWeight Q w i - 1)) ↔ i ∈ M) :
    fibers w M = majority (liftGraph Q w) := by
  ext x
  have hd := degree_add_one Q w x
  simp only [mem_fibers,majority,Finset.mem_filter,Finset.mem_univ,true_and,vertex_card,hn,← h x.1]
  omega

theorem fibers_eq_max (Q : SimpleGraph C) [DecidableRel Q.Adj] (w : C → ℕ) (M : Finset C)
    (pos : ∀ i, 0 < w i) (hne : M.Nonempty) (D : ℕ)
    (h : ∀ i, closedWeight Q w i ≤ D ∧ (closedWeight Q w i = D ↔ i ∈ M)) :
    fibers w M = maxVertices (liftGraph Q w) := by
  let G := liftGraph Q w
  obtain ⟨a,ha⟩ := hne
  have big := G.degree_le_maxDegree (⟨a,⟨0,pos a⟩⟩ : Vertex w)
  have h₁ := degree_add_one Q w (⟨a,⟨0,pos a⟩⟩ : Vertex w)
  have h₂ := (h a).2.mpr ha
  have all : G.maxDegree ≤ D-1 := G.maxDegree_le_of_forall_degree_le _ (fun x => by
    have := degree_add_one Q w x
    have := (h x.1).1
    dsimp only [G]; omega)
  change (liftGraph Q w).degree _ ≤ (liftGraph Q w).maxDegree at big
  change (liftGraph Q w).maxDegree ≤ _ at all
  change (liftGraph Q w).degree _ + 1 = closedWeight Q w a at h₁
  ext x
  have := degree_add_one Q w x
  rw [mem_fibers,mem_maxVertices,← (h x.1).2]
  omega

/-- The ball of radius `n` computed by repeated neighborhood expansion. -/
def reached (Q : SimpleGraph C) [DecidableRel Q.Adj] (r : C) : ℕ → Finset C
  | 0 => {r}
  | n+1 => let S := reached Q r n
           Finset.univ.filter (fun v => v ∈ S ∨ ∃ z ∈ S, Q.Adj z v)

private theorem reached_sound (Q : SimpleGraph C) [DecidableRel Q.Adj] (r : C) :
    ∀ n, ∀ x ∈ reached Q r n, Q.Reachable r x
  | 0,x,h => (Finset.mem_singleton.mp h) ▸ Reachable.rfl
  | n+1,x,h => by
    rcases (Finset.mem_filter.mp h).2 with old | ⟨z,hz,e⟩
    · exact reached_sound Q r n x old
    · exact (reached_sound Q r n z hz).trans e.reachable

omit [Fintype C] in
private theorem connected_lift (Q : SimpleGraph C) (w : C → ℕ) (pos : ∀ i, 0 < w i)
    (hc : Q.Connected) : (liftGraph Q w).Connected := by
  let rep (i : C) : Vertex w := ⟨i,⟨0,pos i⟩⟩
  let f : Q →g liftGraph Q w := ⟨rep,fun {a b} e => ⟨fun h => e.ne (congrArg Sigma.fst h),Or.inr e⟩⟩
  have near (x : Vertex w) : (liftGraph Q w).Reachable x (f x.1) := by
    by_cases e : x = f x.1
    · rw [← e]
    · exact (show (liftGraph Q w).Adj x (f x.1) from ⟨e,Or.inl rfl⟩).reachable
  letI : Nonempty (Vertex w) := hc.nonempty.map rep
  exact ⟨fun x y => (near x).trans (((hc x.1 y.1).map f).trans (near y).symm)⟩

/-- Enumerate only independent sets, rather than filtering the full powerset. -/
def choices (Q : SimpleGraph C) [DecidableRel Q.Adj] : List C → List (Finset C)
  | [] => [∅]
  | a::cs => let rest := choices Q cs
             rest ++ (rest.filter (fun I => decide (∀ x ∈ I, ¬Q.Adj a x))).map (insert a)

private theorem choices_complete (Q : SimpleGraph C) [DecidableRel Q.Adj] :
    ∀ (L : List C) (I : Finset C), (∀ x ∈ I, x ∈ L) → Q.IsIndepSet I → I ∈ choices Q L
  | [],I,hd,_ => by
    have e : I = ∅ := Finset.eq_empty_iff_forall_not_mem.mpr (fun x hx => by simpa using hd x hx)
    simp [e,choices]
  | a::cs,I,hd,hi => by
    rw [choices,List.mem_append]
    by_cases ha : a ∈ I
    · right
      have rest : I.erase a ∈ choices Q cs := choices_complete Q cs _ (fun x hx =>
        (List.mem_cons.mp (hd x (Finset.mem_of_mem_erase hx))).resolve_left (Finset.mem_erase.mp hx).1)
        (fun _ hx _ hy h => hi (Finset.mem_of_mem_erase hx) (Finset.mem_of_mem_erase hy) h)
      refine List.mem_map.mpr ⟨I.erase a,List.mem_filter.mpr ⟨rest,?_⟩,Finset.insert_erase ha⟩
      exact decide_eq_true (fun _ hx => independent_nonadj Q hi ha (Finset.mem_of_mem_erase hx))
    · left
      exact choices_complete Q cs I (fun x hx => (List.mem_cons.mp (hd x hx)).resolve_left
        (fun e => ha (e ▸ hx))) hi

instance (Q : SimpleGraph C) [DecidableRel Q.Adj] (I : Finset C) : Decidable (Dominates Q I) :=
  inferInstanceAs (Decidable (∀ v, v ∈ I ∨ ∃ w ∈ I, Q.Adj v w))

def boundsPass (Q : SimpleGraph C) [DecidableRel Q.Adj] (L : List C) (M : Finset C) (a d : ℕ) : Bool :=
  (choices Q L).all (fun I => decide ((I.card ≤ a ∨ ¬Disjoint I M) ∧ (d ≤ I.card ∨ ¬Dominates Q I)))

/-- The inputs to the kernel-checkable quotient certificate. -/
structure Certificate (Q : SimpleGraph C) [DecidableRel Q.Adj] (w : C → ℕ) (M : Finset C) (a d k n : ℕ) : Prop where
  positive : ∀ i, 0 < w i
  order_eq : ∑ i, w i = n
  hubs_eq : ∑ i ∈ M, w i = k
  singleton_hubs : ∀ i ∈ M, w i = 1
  indep_hubs : Q.IsIndepSet M
  seen : ∃ (r : C) (steps : ℕ), reached Q r steps = Finset.univ
  checked : ∃ L : List C, (∀ i, i ∈ L) ∧ boundsPass Q L M a d = true

structure Witness (G : SimpleGraph C) (S : Finset C) (a d k n : ℕ) : Prop where
  connected : G.Connected
  order_eq : Fintype.card C = n
  size : S.card = k
  independent : G.IsIndepSet S
  alpha_le : (G.induce (Sᶜ : Set C)).indepNum ≤ a
  dom_ge : d ≤ independentDominationNumber G

omit [Fintype C] in
private theorem project (Q : SimpleGraph C) (w : C → ℕ) {I : Finset (Vertex w)}
    (hi : (liftGraph Q w).IsIndepSet I) :
    Q.IsIndepSet (I.image Sigma.fst : Finset C) ∧ (I.image Sigma.fst).card = I.card := by
  constructor
  · intro a ha b hb hab e
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hb
    exact independent_nonadj _ hi hx hy ⟨fun h => hab (congrArg Sigma.fst h),Or.inr e⟩
  · apply Finset.card_image_iff.mpr
    intro x hx y hy eq
    by_contra ne
    exact independent_nonadj _ hi hx hy ⟨ne,Or.inl eq⟩

theorem realize (Q : SimpleGraph C) [DecidableRel Q.Adj] (w : C → ℕ) (M : Finset C) (a d k n : ℕ)
    (cert : Certificate Q w M a d k n) : Witness (liftGraph Q w) (fibers w M) a d k n := by
  classical
  let G := liftGraph Q w
  let S := fibers w M
  obtain ⟨L,hL,hok⟩ := cert.checked
  have check {J : Finset C} (hj : Q.IsIndepSet J) :
      (J.card ≤ a ∨ ¬Disjoint J M) ∧ (d ≤ J.card ∨ ¬Dominates Q J) := by
    have hmem := choices_complete Q L J (fun i _ => hL i) hj
    exact of_decide_eq_true (List.all_eq_true.mp hok J hmem)
  constructor
  · obtain ⟨r,t,ht⟩ := cert.seen
    have reach (x : C) := reached_sound Q r t x (ht ▸ Finset.mem_univ x)
    exact connected_lift Q w cert.positive (Q.connected_iff_exists_forall_reachable.mpr ⟨r,reach⟩)
  · exact (vertex_card w).trans cert.order_eq
  · simpa only [fibers,Finset.card_sigma,Finset.card_univ,Fintype.card_fin] using cert.hubs_eq
  · rintro ⟨i,x⟩ hx ⟨j,y⟩ hy ne ⟨_,e|e⟩
    · change i = j at e
      subst j
      have h1 := cert.singleton_hubs i (mem_fibers.mp hx)
      have h2 := x.isLt
      have h3 := y.isLt
      exact ne (congrArg (Sigma.mk i) (Fin.ext (show x.val = y.val by omega)))
    · exact independent_nonadj Q cert.indep_hubs (mem_fibers.mp hx) (mem_fibers.mp hy) e
  · let R := (S : Set (Vertex w))ᶜ
    let H := G.induce R
    obtain ⟨I,hI⟩ := H.exists_isNIndepSet_indepNum
    let J := I.map (Function.Embedding.subtype R)
    have hj : G.IsIndepSet J := by
      intro x hx y hy _ he
      obtain ⟨p,hp,rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hy
      exact independent_nonadj H hI.isIndepSet hp hq he
    obtain ⟨hp,hs⟩ := project Q w hj
    have hdis : Disjoint (J.image Sigma.fst) M := by
      apply Finset.disjoint_left.mpr
      intro c hc hM
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨p,_,rfl⟩ := Finset.mem_map.mp hy
      exact p.property (mem_fibers.mpr hM)
    have hb := (check hp).1.resolve_right (not_not.mpr hdis)
    rw [hs,Finset.card_map,hI.card_eq] at hb
    exact hb
  · have h₀ : G.IsIndepSet ((∅ : Finset (Vertex w)) : Set (Vertex w)) := by simp
    obtain ⟨E,_,hE,hdom⟩ := extend_independent G h₀
    have hex : {m | ∃ I : Finset (Vertex w), G.IsIndepSet I ∧ Dominates G I ∧ I.card = m}.Nonempty :=
      ⟨E.card,E,hE,hdom,rfl⟩
    obtain ⟨I,hi,hd,heq⟩ : ∃ I : Finset (Vertex w), G.IsIndepSet I ∧ Dominates G I ∧ I.card = independentDominationNumber G :=
      Nat.sInf_mem hex
    obtain ⟨hp,hs⟩ := project Q w hi
    have hproj : Dominates Q (I.image Sigma.fst) := by
      intro c
      let x : Vertex w := ⟨c,⟨0,cert.positive c⟩⟩
      rcases hd x with hx | ⟨y,hy,_,eq|e⟩
      · exact Or.inl (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
      · exact Or.inl (Finset.mem_image.mpr ⟨y,hy,eq.symm⟩)
      · exact Or.inr ⟨y.1,Finset.mem_image.mpr ⟨y,hy,rfl⟩,e⟩
    simpa only [hs,heq] using (check hp).2.resolve_right (not_not.mpr hproj)

end Graffiti.CliqueFiber
