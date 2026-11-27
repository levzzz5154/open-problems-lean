import SelfBanning.Preperiod
import SelfBanning.Row
import Mathlib.Data.Fintype.Basic

namespace SelfBanning

/-- A small word is a certificate only if it respects bans *across* the wrap
and every skipped label has a witness even in the very first copy. -/
private abbrev CycleCheck (k P M : ℕ) (f : ℕ → ℕ) : Prop :=
  ∀ i : Fin P, k ≤ f i ∧ f i ≤ M ∧
    (∀ d : Fin (M+1), 0 < d.val → d.val ≤ f i → f ((i.val+P-d.val)%P) ≠ f i) ∧
    (∀ v : Fin (M+1), k ≤ v.val → v.val < f i → ∃ d : Fin (M+1),
      0 < d.val ∧ d.val ≤ i.val ∧ d.val ≤ v.val ∧ f (i.val-d.val) = v.val)

private theorem certified_period {k P M : ℕ} {f : ℕ → ℕ} (hp : 0 < P) (hm : M ≤ P)
    (hc : CycleCheck k P M f) : Function.Periodic (row k) P := by
  let a (t : ℕ) := f (t%P)
  have hr : IsRow k a := by
    refine ⟨fun t => (hc ⟨t%P,Nat.mod_lt _ hp⟩).1, ?_, ?_⟩
    · intro t s hs hb
      let i : Fin P := ⟨t%P,Nat.mod_lt _ hp⟩
      have hf : a t ≤ M := (hc i).2.1
      let d : Fin (M+1) := ⟨t-s,by omega⟩
      have hd : d.val ≤ a t := by dsimp [d]; omega
      have hprev := (hc i).2.2.1 d (by dsimp [d]; omega) hd
      have he : (i.val+P-d.val)%P = s%P := calc
        _ = (t%P+(P-d.val))%P := by
          have hdi : d.val ≤ P := by omega
          exact congrArg (· % P) (show t%P+P-d.val = t%P+(P-d.val) by omega)
        _ = (t+(P-d.val))%P := Nat.mod_add_mod _ _ _
        _ = (s+P)%P := by dsimp [d]; congr 1; omega
        _ = s%P := Nat.add_mod_right _ _
      rw [he] at hprev
      exact hprev
    · intro t v hk hv
      let i : Fin P := ⟨t%P,Nat.mod_lt _ hp⟩
      have hf : a t ≤ M := (hc i).2.1
      obtain ⟨d,hd,hi,hw,he⟩ := (hc i).2.2.2 ⟨v,by omega⟩ hk hv
      have hj : t%P ≤ t := Nat.mod_le t P
      change d.val ≤ t%P at hi
      change d.val ≤ v at hw
      have hs : t-d.val = P*(t/P)+(t%P-d.val) := by have := Nat.mod_add_div t P; omega
      refine ⟨t-d.val, by omega, by omega, ?_⟩
      change f ((t-d.val)%P) = v
      rw [hs, Nat.mul_add_mod, Nat.mod_eq_of_lt (by have := Nat.mod_lt t hp; omega)]
      exact he
  rw [unique_row (isRow k) hr]
  intro t
  simp [a]

private def word1 : List ℕ := [1,2,1,3]
private def word2 : List ℕ := [2,3,4,2,5,3,2,4,6,2,3,5,2,4,3,2,6,5,2,3,4,2,7,3,2,4,5,2,3,6,2,4,3,2,5,7]

/-- Exactly the starts `0, 1, 2` give purely periodic rows. -/
theorem pure_iff (k : ℕ) : (∃ T > 0, Function.Periodic (row k) T) ↔ k ≤ 2 := by
  constructor
  · rintro ⟨T,hT,hp⟩
    by_contra! hk
    exact not_purely_periodic (isRow k) hk hT hp
  · intro hk
    have h : k=0 ∨ k=1 ∨ k=2 := by omega
    rcases h with rfl | rfl | rfl
    · have hz (t : ℕ) : row 0 t = 0 := (minimum_iff (isRow 0) t).2 (one_dvd _)
      exact ⟨1, by decide, fun t => (hz (t+1)).trans (hz t).symm⟩
    · exact ⟨4, by decide, certified_period (f := fun i => word1.getD i 0) (M := 3)
        (by decide) (by decide) (by decide)⟩
    · exact ⟨36, by decide, certified_period (f := fun i => word2.getD i 0) (M := 7)
        (by decide) (by decide) (by decide)⟩

end SelfBanning
