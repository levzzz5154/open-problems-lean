import Graffiti.ExtremalCenter
import Graffiti.SpanningArms
import Graffiti.TreeCenterCover

/-! # The independent domination number and the eccentricity of the center

DeLaViña–Pepper–Waller, *Graffiti.pc on the Independent-Domination Number
of a Graph*, Conjecture 3.2 / Written on the Wall II 434e.
https://www.uhd.edu/documents/academics/sciences/dpw-cn2011.pdf
-/

namespace Graffiti

open SimpleGraph

variable {V : Type*} [DecidableEq V]

private def skipped (I : Finset V) (L : List V) : List V := L.filter (fun x => decide (x ∉ I))

/-- Every consecutive pair contributes at least one omitted vertex. -/
private theorem path_skips (G : SimpleGraph V) (I : Finset V) (hi : G.IsIndepSet I) :
    ∀ (L : List V), L.Chain' G.Adj → L.length ≤ 2 * (skipped I L).length + 1
  | [], _ => by simp [skipped]
  | [a], _ => by simp [skipped]
  | a::b::L, h => by
    have hh := path_skips G I hi L h.tail.tail
    by_cases ha : a ∈ I <;> by_cases hb : b ∈ I
    · exact (independent_nonadj G hi ha hb h.rel_head).elim
    all_goals (simp [skipped,ha,hb] at hh ⊢; omega)

/-- For a chain of at least two vertices, prescribing its second vertex
removes the rounding loss: the first and (if present) third must be omitted. -/
private theorem tight_path (G : SimpleGraph V) (L : List V) (h : L.Chain' G.Adj) (hlen : 2 ≤ L.length) :
    ∃ z ∈ L, ∀ I : Finset V, G.IsIndepSet I → z ∈ I → L.length ≤ 2 * (skipped I L).length := by
  cases L with
  | nil => simp at hlen
  | cons a L => cases L with
    | nil => simp at hlen
    | cons b L =>
      refine ⟨b,by simp,?_⟩
      intro I hI hb
      have ha : a ∉ I := fun ha => independent_nonadj G hI ha hb h.rel_head
      cases L with
      | nil => simp [skipped,ha,hb]
      | cons c L =>
        have hc : c ∉ I := fun hc => independent_nonadj G hI hb hc h.tail.rel_head
        have hh := path_skips G I hI L h.tail.tail.tail
        simp [skipped,ha,hb,hc] at hh ⊢
        omega

variable [Fintype V]

private theorem savings (G : SimpleGraph V) (v : V) (t : ℕ) (P Q : List V) (ht : 3 ≤ t)
    (hn : (P ++ Q).Nodup) (hp : P.Chain' G.Adj) (hq : Q.Chain' G.Adj)
    (far : ∀ x ∈ P ++ Q, x ≠ v ∧ ¬G.Adj v x) (hlen : 2*t ≤ P.length + Q.length + 2) :
    independentDominationNumber G + t ≤ (room G Finset.univ v).card + 1 := by
  classical
  have pick : ∃ z ∈ P ++ Q, ∀ I : Finset V, G.IsIndepSet I → z ∈ I →
      P.length + Q.length ≤ 2 * ((skipped I P).length + (skipped I Q).length) + 1 := by
    by_cases h : 2 ≤ P.length
    · obtain ⟨z,hz,hc⟩ := tight_path G P hp h
      refine ⟨z,List.mem_append.mpr (Or.inl hz),?_⟩
      intro I hi hz
      have := hc I hi hz
      have := path_skips G I hi Q hq
      omega
    · obtain ⟨z,hz,hc⟩ := tight_path G Q hq (by omega)
      refine ⟨z,List.mem_append.mpr (Or.inr hz),?_⟩
      intro I hi hz
      have := hc I hi hz
      have := path_skips G I hi P hp
      omega
  obtain ⟨z,hz,hs⟩ := pick
  have hvz := (far z hz).2
  have hpair : G.IsIndepSet (({v,z} : Finset V) : Set V) := by
    intro a ha b hb _
    simp only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;>
      first | exact G.loopless _ | exact hvz | exact fun e => hvz e.symm
  obtain ⟨I,hpI,hI,hd⟩ := extend_independent G hpair
  have hcount := hs I hI (hpI (by simp : z ∈ ({v,z} : Finset V)))
  let E := (skipped I (P ++ Q)).toFinset
  have memE {x : V} : x ∈ E ↔ x ∈ P ++ Q ∧ x ∉ I := by
    simp only [E,skipped,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
  have hcard : E.card = (skipped I P).length + (skipped I Q).length := by
    calc E.card = (skipped I (P ++ Q)).length := List.toFinset_card_of_nodup (hn.filter _)
         _ = _ := by simp [skipped,List.filter_append]
  have dis : Disjoint E I := Finset.disjoint_left.mpr (fun _ h => (memE.mp h).2)
  have sub : E ∪ I ⊆ room G Finset.univ v := by
    intro x hx
    refine (mem_room G).mpr ⟨Finset.mem_univ _,?_⟩
    rcases Finset.mem_union.mp hx with he|hi
    · exact (far x (memE.mp he).1).2
    · exact independent_nonadj G hI (hpI (by simp : v ∈ ({v,z} : Finset V))) hi
  have hspace := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint dis] at hspace
  have hi : independentDominationNumber G ≤ I.card := Nat.sInf_le ⟨I,hI,hd,rfl⟩
  omega

private theorem depth_of_extremal (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (ht : degeneracy Gᶜ < independentDominationNumber G) : centerDepth G ≤ 1 := by
  classical
  letI : Nonempty V := hc.nonempty
  have hfin : G.radius ≠ ⊤ := radius_ne_top_iff.mpr hc
  apply centerDepth_le
  intro v
  by_cases hr : G.radius.toNat ≤ 1
  · obtain ⟨c,hc'⟩ := G.exists_eccent_eq_radius
    exact ⟨c,hc', (ENat.toNat_le_toNat ((edist_le_eccent (G := G)).trans_eq hc') hfin).trans hr⟩
  · obtain ⟨c,hd,he⟩ := extremal_center_cover G hc ht v
    have hb (x : V) : G.dist c x ≤ 2 := by
      rcases he x with rfl | e | ⟨y,h₁,h₂⟩
      · rw [dist_self]; decide
      · rw [dist_eq_one_iff_adj.mpr e]; decide
      · have h := hc.dist_triangle (u := c) (v := y) (w := x)
        rw [dist_eq_one_iff_adj.mpr h₁,dist_eq_one_iff_adj.mpr h₂] at h
        exact h
    have hcent : c ∈ G.center := by
      rw [mem_center_iff]
      apply le_antisymm _ radius_le_eccent
      rw [← ENat.coe_toNat hfin]
      apply iSup_le
      intro x
      rw [← ENat.coe_toNat (edist_ne_top_iff_reachable.mpr (hc c x))]
      apply ENat.coe_le_coe.mpr
      change G.dist c x ≤ G.radius.toNat
      have := hb x
      omega
    refine ⟨c,hcent,?_⟩
    rcases hd with rfl | e
    · rw [dist_self]; decide
    · exact (dist_eq_one_iff_adj.mpr e.symm).le

/-- The additive statement is equivalent to the conjecture over the integers;
it does not weaken it through truncated subtraction on naturals. -/
theorem conjecture434e (G : SimpleGraph V) (hc : G.Connected) :
    independentDominationNumber G + centerDepth G ≤ degeneracy Gᶜ + 2 := by
  classical
  letI : Nonempty V := hc.nonempty
  by_cases ht : 3 ≤ centerDepth G
  · obtain ⟨v,_,hv⟩ := peel_univ G Finset.univ Finset.Subset.rfl Finset.univ_nonempty
    obtain ⟨T,hTG,hT,P,Q,hn,hp,hq,hfar,hlen⟩ := exists_far_arms G hc v
    have hlen' := (centerDepth_le_tree_diam G T hTG hT).trans hlen
    have hs := savings G v (centerDepth G) P Q ht hn hp hq hfar hlen'
    omega
  · have hi := independent_domination_le_degeneracy_succ G
    by_cases here : degeneracy Gᶜ < independentDominationNumber G
    · have := depth_of_extremal G hc here
      omega
    · omega

end Graffiti
