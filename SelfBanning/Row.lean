import SelfBanning.Core
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Find

namespace SelfBanning

private def Eligible (k t : ℕ) (past : Fin t → ℕ) (v : ℕ) : Prop :=
  k ≤ v ∧ ∀ s, t ≤ s.val + v → past s ≠ v

private theorem exists_eligible (k t : ℕ) (past : Fin t → ℕ) : ∃ v, Eligible k t past v := by
  let M := Finset.univ.sup past
  refine ⟨k+M+1, by omega, ?_⟩
  intro s _
  have hs : past s ≤ M := Finset.le_sup (Finset.mem_univ s)
  omega

private noncomputable def pick (k t : ℕ) (past : Fin t → ℕ) : ℕ := by
  classical
  exact Nat.find (exists_eligible k t past)

/-- The recursively constructed row; only its `t` previous values are queried. -/
noncomputable def row (k t : ℕ) : ℕ := pick k t (fun s => row k s.val)
termination_by t

theorem isRow (k : ℕ) : IsRow k (row k) := by
  classical
  have eqn (t : ℕ) : row k t = pick k t (fun i => row k i.val) := by rw [row]
  have valid (t : ℕ) : Eligible k t (fun i => row k i.val) (row k t) := by
    rw [eqn t]
    exact Nat.find_spec _
  refine ⟨fun t => (valid t).1, fun t s hs hb => (valid t).2 ⟨s,hs⟩ hb, ?_⟩
  intro t v hv hlt
  apply Classical.byContradiction
  intro hno
  have he : Eligible k t (fun i => row k i.val) v :=
    ⟨hv, fun s hs he => hno ⟨s.val,s.isLt,hs,he⟩⟩
  have hle : row k t ≤ v := by rw [eqn t]; exact Nat.find_min' _ he
  omega

/-- The rules determine every time step, not just the eventual part. -/
theorem unique_row {k : ℕ} {a b : ℕ → ℕ} (ha : IsRow k a) (hb : IsRow k b) : a = b := by
  funext t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    rcases lt_trichotomy (a t) (b t) with h | e | h
    · obtain ⟨s,hs,hd,hv⟩ := hb.skipped t (a t) (ha.lower t) h
      exact ((ha.allowed t s hs hd) ((ih s hs).trans hv)).elim
    · exact e
    · obtain ⟨s,hs,hd,hv⟩ := ha.skipped t (b t) (hb.lower t) h
      exact ((hb.allowed t s hs hd) ((ih s hs).symm.trans hv)).elim

/-- The minimum starts at time zero and occurs every `k+1` time steps. -/
theorem minimum_iff {k : ℕ} {a : ℕ → ℕ} (h : IsRow k a) (t : ℕ) : a t = k ↔ k+1 ∣ t := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    constructor
    · intro ht
      by_contra hd
      let s := (k+1)*(t/(k+1))
      have he : t%(k+1)+s=t := Nat.mod_add_div t (k+1)
      have hrem : t%(k+1) ≠ 0 := fun hz => hd (Nat.dvd_of_mod_eq_zero hz)
      have hsmall := Nat.mod_lt t (show 0 < k+1 by omega)
      have hs : s < t := by omega
      have hprev : a s = k := (ih s hs).2 ⟨t/(k+1),rfl⟩
      exact (h.allowed t s hs (by omega)) (hprev.trans ht.symm)
    · intro hd
      apply le_antisymm _ (h.lower t)
      by_contra! hv
      obtain ⟨s,hs,hb,he⟩ := h.skipped t k le_rfl hv
      have hgap := Nat.le_of_dvd (show 0 < t-s by omega) (Nat.dvd_sub hd ((ih s hs).1 he))
      omega

end SelfBanning
