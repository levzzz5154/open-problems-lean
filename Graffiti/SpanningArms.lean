import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Data.List.TakeDrop

namespace Graffiti

open SimpleGraph List

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
private theorem second_edge_mem {H : SimpleGraph V} {a b : V} (p : H.Walk a b)
    (hl : 2 ≤ p.length) : s(p.getVert 1, p.getVert 2) ∈ p.edges := by
  cases p with
  | nil => simp at hl
  | cons h q =>
    cases q with
    | nil => simp at hl
    | cons k q => simp

theorem tree_with_star (G : SimpleGraph V) (hc : G.Connected) (v : V) :
    ∃ T ≤ G, T.IsTree ∧ ∀ x, G.Adj v x → T.Adj v x := by
  classical
  let S := {H : SimpleGraph V | H.Connected ∧ ∀ x, G.Adj v x → H.Adj v x}
  have hg : G ∈ S := ⟨hc, fun _ h => h⟩
  obtain ⟨T, hTG, hm⟩ := S.toFinite.exists_minimal_le hg
  obtain ⟨hcon, hs⟩ : T.Connected ∧ ∀ x, G.Adj v x → T.Adj v x := hm.prop
  refine ⟨T, hTG, ⟨hcon, ?_⟩, hs⟩
  intro u c hcy
  obtain ⟨a, p, hp, ha⟩ : ∃ (a : V) (p : T.Walk a a), p.IsCycle ∧
      (a = v ∨ v ∉ p.support) := by
    by_cases h : v ∈ c.support
    · exact ⟨v, c.rotate h, hcy.rotate h, Or.inl rfl⟩
    · exact ⟨u, c, hcy, Or.inr h⟩
  have hl := hp.three_le_length
  have hne (i : ℕ) (hi : 0 < i) (hi' : i < p.length) : p.getVert i ≠ v := by
    rcases ha with rfl | ha
    · intro he
      have := (hp.getVert_endpoint_iff hi'.le).mp he
      omega
    · exact fun he => ha (he ▸ p.getVert_mem_support i)
  let x := p.getVert 1
  let y := p.getVert 2
  have hx : x ≠ v := hne 1 (by decide) (by omega)
  have hy : y ≠ v := hne 2 (by decide) (by omega)
  have he : s(x,y) ∈ p.edges := second_edge_mem p (by omega)
  have hnb : ¬ T.IsBridge s(x,y) := fun hb =>
    (isBridge_iff_adj_and_forall_cycle_not_mem.mp hb).2 p hp he
  apply hm.not_prop_of_lt (y := T.deleteEdges {s(x,y)})
  · refine lt_of_le_of_ne (T.deleteEdges_le _) (fun h => ?_)
    have bad : (T.deleteEdges {s(x,y)}).Adj x y := h.ge (p.adj_of_mem_edges he)
    exact (deleteEdges_adj.mp bad).2 rfl
  · refine ⟨hcon.connected_delete_edge_of_not_isBridge hnb, fun z hz => ?_⟩
    exact deleteEdges_adj.mpr ⟨hs z hz, by simp [Sym2.eq_iff, Ne.symm hx, Ne.symm hy]⟩

omit [Fintype V] [DecidableEq V] in
private theorem take_length_le {H : SimpleGraph V} {a b : V} (p : H.Walk a b) (i : ℕ) :
    (p.take i).length ≤ i := by
  induction p generalizing i with
  | nil => cases i <;> simp [Walk.take]
  | cons h q ih => cases i with
    | zero => simp [Walk.take]
    | succ i => simpa [Walk.take] using Nat.succ_le_succ (ih i)

omit [Fintype V] [DecidableEq V] in
private theorem drop_length_eq {H : SimpleGraph V} {a b : V} (p : H.Walk a b) (i : ℕ) :
    (p.drop i).length = p.length - i := by
  induction p generalizing i with
  | nil => cases i <;> simp [Walk.drop]
  | cons h q ih => cases i with
    | zero => simp [Walk.drop]
    | succ i => simp [Walk.drop, ih]

/-- Cutting a diametral tree path around the closed neighborhood of `v` leaves
at most two arms and removes at most three vertices. -/
theorem exists_far_arms (G : SimpleGraph V) (hc : G.Connected) (v : V) :
    ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree ∧ ∃ P Q : List V,
      (P ++ Q).Nodup ∧ List.Chain' G.Adj P ∧ List.Chain' G.Adj Q ∧
      (∀ x ∈ P ++ Q, x ≠ v ∧ ¬G.Adj v x) ∧ T.diam ≤ P.length + Q.length + 2 := by
  classical
  letI : Nonempty V := ⟨v⟩
  obtain ⟨T, hTG, ht, hs⟩ := tree_with_star G hc v
  obtain ⟨a, b, hab⟩ := T.exists_dist_eq_diam
  obtain ⟨p, hp, hd⟩ := ht.isConnected.exists_path_of_dist a b
  have hchain := p.chain'_adj_support.imp (fun _ _ h => hTG h)
  let near (x : V) := x = v ∨ G.Adj v x
  have hnear {x : V} (hx : near x) : T.dist v x ≤ 1 := by
    rcases hx with h | hx
    · rw [h, dist_self]; decide
    · exact (dist_eq_one_iff_adj.mpr (hs _ hx)).le
  have hget (i : ℕ) (h : i < p.support.length) : p.support[i] = p.getVert i := by
    have hi : i ≤ p.length := by rw [Walk.length_support] at h; omega
    simpa [List.getElem?_eq_getElem h] using (p.getVert_eq_support_get? hi).symm
  let bad (i : ℕ) := i ≤ p.length ∧ near (p.getVert i)
  refine ⟨T, hTG, ht, ?_⟩
  by_cases hex : ∃ i, bad i
  · let k := Nat.find hex
    have hk : bad k := Nat.find_spec hex
    have hkl := hk.1
    have hgap {j : ℕ} (hj : bad j) : j ≤ k + 2 := by
      have h1 := (dist_le (p.take k)).trans (take_length_le p k)
      have h2 := dist_le (p.drop j)
      rw [drop_length_eq] at h2
      have h3 : T.dist (p.getVert k) (p.getVert j) ≤ 2 := by
        have h := ht.isConnected.dist_triangle (u := p.getVert k) (v := v) (w := p.getVert j)
        rw [dist_comm (u := p.getVert k) (v := v)] at h
        have := hnear hk.2
        have := hnear hj.2
        omega
      have h4 := ht.isConnected.dist_triangle (u := a) (v := p.getVert k) (w := b)
      have h5 := ht.isConnected.dist_triangle (u := p.getVert k) (v := p.getVert j) (w := b)
      have := hj.1
      omega
    refine ⟨p.support.take k, p.support.drop (k + 3), ?_, hchain.take _, hchain.drop _, ?_, ?_⟩
    · apply hp.support_nodup.sublist
      calc
        p.support.take k ++ p.support.drop (k + 3) =
            p.support.take k ++ (p.support.drop k).drop 3 := by simp [List.drop_drop, Nat.add_comm]
        _ <+ p.support.take k ++ p.support.drop k := (List.drop_sublist ..).append_left _
        _ = p.support := List.take_append_drop ..
    · intro x hx
      suffices hn : ¬ near x from ⟨fun h => hn (Or.inl h), fun h => hn (Or.inr h)⟩
      intro hn
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
        rw [List.getElem_take, hget] at hn
        simp only [List.length_take, lt_min_iff] at hi
        have hlen := p.length_support
        exact Nat.find_min hex hi.1 ⟨by omega, hn⟩
      · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
        rw [List.getElem_drop, hget] at hn
        simp only [List.length_drop, Walk.length_support] at hi
        have := hgap (j := k + 3 + i) ⟨by omega, hn⟩
        omega
    · simp only [List.length_take, List.length_drop, Walk.length_support]
      omega
  · refine ⟨p.support, [], by simpa using hp.support_nodup, hchain, by simp, ?_, ?_⟩
    · intro x hx
      simp only [List.append_nil] at hx
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
      rw [hget]
      have hlen := p.length_support
      have hn : ¬ near (p.getVert i) := fun h => hex ⟨i, by exact ⟨by omega, h⟩⟩
      exact ⟨fun h => hn (Or.inl h), fun h => hn (Or.inr h)⟩
    · simp only [Walk.length_support, List.length_nil]
      omega

end Graffiti
