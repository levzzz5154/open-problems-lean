import Graffiti426

/-! # A low-degree vertex outside every proper clique

In a `k−1`-degenerate graph whose maximal cliques all have at least `k`
vertices, each proper clique misses a vertex of degree at most `k−1`.
We work in the complement: `room G S v` is the closed neighborhood of `v`
in the complement induced on `S` (when `v ∈ S`). -/

namespace Graffiti

variable {V : Type*} (G : SimpleGraph V)

noncomputable def room (S : Finset V) (v : V) : Finset V := by
  classical
  exact S.filter (fun w => ¬G.Adj v w)

@[simp] theorem mem_room {S : Finset V} {v w : V} : w ∈ room G S v ↔ w ∈ S ∧ ¬G.Adj v w := by
  classical simp [room]

theorem independent_nonadj {I : Finset V} (hi : G.IsIndepSet I) {v w : V}
    (hv : v ∈ I) (hw : w ∈ I) : ¬G.Adj v w := fun e => hi hv hw e.ne e

def ExtendsTo (S : Finset V) (k : ℕ) : Prop :=
  ∀ B : Finset V, B ⊆ S → G.IsIndepSet B →
    ∃ I : Finset V, B ⊆ I ∧ I ⊆ S ∧ G.IsIndepSet I ∧ k ≤ I.card

def PeelsAt (S : Finset V) (k : ℕ) : Prop :=
  ∀ T : Finset V, T ⊆ S → T.Nonempty → ∃ v ∈ T, (room G T v).card ≤ k

/-- A relative peeling lemma, including the case of a proper subclique in a clique. -/
theorem low_outside_clique (S B : Finset V) (k : ℕ) (hb : B ⊆ S) (hind : G.IsIndepSet B)
    (hout : ∃ v ∈ S, v ∉ B) (peel : PeelsAt G S k) (extend : ExtendsTo G S k) :
    ∃ v ∈ S, v ∉ B ∧ (room G S v).card ≤ k := by
  classical
  obtain ⟨b,hbS,hbB⟩ := hout
  obtain ⟨v,hvS,hv⟩ := peel S (Finset.Subset.rfl) ⟨b,hbS⟩
  by_cases hvB : v ∉ B
  · exact ⟨v,hvS,hvB,hv⟩
  push_neg at hvB
  obtain ⟨K,hBK,hKS,hK,hsize⟩ := extend B hb hind
  have inside {I : Finset V} (hI : G.IsIndepSet I) {T : Finset V} (hIT : I ⊆ T) {w : V}
      (hw : w ∈ I) : I ⊆ room G T w := fun _ hy => (mem_room G).mpr ⟨hIT hy,independent_nonadj G hI hw hy⟩
  have hKeq : K = room G S v := Finset.eq_of_subset_of_card_le (inside hK hKS (hBK hvB)) (hv.trans hsize)
  have hk : K.card ≤ k := hKeq ▸ hv
  by_cases hall : S ⊆ K
  · have hsmall : room G S b ⊆ K := fun _ hy => hall ((mem_room G).mp hy).1
    exact ⟨b,hbS,hbB,(Finset.card_le_card hsmall).trans hk⟩
  obtain ⟨w,hwS,hwK⟩ := Finset.not_subset.mp hall
  -- Keep all vertices outside K and exactly the vertices of K that are
  -- compatible with something outside K. In particular v is deleted.
  let T := S.filter (fun a => ∃ y ∈ S, y ∉ K ∧ ¬G.Adj a y)
  have memT {a : V} : a ∈ T ↔ a ∈ S ∧ ∃ y ∈ S, y ∉ K ∧ ¬G.Adj a y := Finset.mem_filter
  have hTS : T ⊆ S := fun _ ha => (memT.mp ha).1
  have outsideT {a : V} (haS : a ∈ S) (haK : a ∉ K) : a ∈ T :=
    memT.mpr ⟨haS,a,haS,haK,G.loopless a⟩
  have hvT : v ∉ T := by
    intro hy
    obtain ⟨a,haS,haK,hva⟩ := (memT.mp hy).2
    exact haK (hKeq ▸ (mem_room G).mpr ⟨haS,hva⟩)
  have less : T.card < S.card := Finset.card_lt_card <| Finset.ssubset_iff_subset_ne.mpr
    ⟨hTS,fun eq => hvT (eq ▸ hvS)⟩
  have eqRoom {a : V} (ha : a ∈ S) (hn : a ∉ K) : room G T a = room G S a := by
    ext y
    simp only [mem_room]
    exact ⟨fun ⟨hy,hn'⟩ => ⟨hTS hy,hn'⟩,
      fun ⟨hy,hn'⟩ => ⟨memT.mpr ⟨hy,a,ha,hn,fun e => hn' e.symm⟩,hn'⟩⟩
  have finish {a : V} (ha : a ∈ T) (hn : a ∉ K) (hc : (room G T a).card ≤ k) :
      ∃ v ∈ S, v ∉ B ∧ (room G S v).card ≤ k :=
    ⟨a,hTS ha,fun hy => hn (hBK hy),eqRoom (hTS ha) hn ▸ hc⟩
  have stay {J : Finset V} (hj : G.IsIndepSet J) (hJS : J ⊆ S) {y : V} (hyJ : y ∈ J)
      (hy : y ∉ K) : J ⊆ T := fun a ha =>
    memT.mpr ⟨hJS ha,y,hJS hyJ,hy,independent_nonadj G hj ha hyJ⟩
  obtain ⟨z,hzT,hz⟩ := peel T hTS ⟨w,outsideT hwS hwK⟩
  by_cases hzK : z ∉ K
  · exact finish hzT hzK hz
  push_neg at hzK
  -- The remaining part of K belongs to a large independent set in T.
  obtain ⟨y,hyS,hyK,hzy⟩ := (memT.mp hzT).2
  have pair : G.IsIndepSet (({z,y} : Finset V) : Set V) := by
    intro a ha b hb _
    simp only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;>
      first | exact G.loopless _ | exact hzy | exact fun e => hzy e.symm
  have hpS : ({z,y} : Finset V) ⊆ S := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl|ha
    · exact hTS hzT
    · exact Finset.mem_singleton.mp ha ▸ hyS
  obtain ⟨J,hpJ,hJS,hJ,hj⟩ := extend {z,y} hpS pair
  have hJT := stay hJ hJS (hpJ (by simp : y ∈ ({z,y} : Finset V))) hyK
  have eqJ : J = room G T z := Finset.eq_of_subset_of_card_le
    (inside hJ hJT (hpJ (by simp : z ∈ ({z,y} : Finset V)))) (hz.trans hj)
  have hcover : K ∩ T ⊆ J := by
    intro a ha
    exact eqJ ▸ (mem_room G).mpr ⟨(Finset.mem_inter.mp ha).2,
      independent_nonadj G hK hzK (Finset.mem_inter.mp ha).1⟩
  have extT : ExtendsTo G T k := by
    intro C hCT hC
    by_cases hCK : C ⊆ K
    · exact ⟨J,fun _ ha => hcover (Finset.mem_inter.mpr ⟨hCK ha,hCT ha⟩),hJT,hJ,hj⟩
    · obtain ⟨a,haC,haK⟩ := Finset.not_subset.mp hCK
      obtain ⟨L,hCL,hLS,hL,hkL⟩ := extend C (hCT.trans hTS) hC
      exact ⟨L,hCL,stay hL hLS (hCL haC) haK,hL,hkL⟩
  have subInd : G.IsIndepSet ((K ∩ T : Finset V) : Set V) :=
    fun _ ha _ hb hne => hK (Finset.mem_inter.mp ha).1 (Finset.mem_inter.mp hb).1 hne
  obtain ⟨a,ha,han,hc⟩ := low_outside_clique T (K ∩ T) k Finset.inter_subset_right subInd
    ⟨w,outsideT hwS hwK,fun h => hwK (Finset.mem_inter.mp h).1⟩
    (fun U hUT => peel U (hUT.trans hTS)) extT
  exact finish ha (fun h => han (Finset.mem_inter.mpr ⟨h,ha⟩)) hc
termination_by S.card

end Graffiti
