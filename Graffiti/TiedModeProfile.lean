import Graffiti.FirstZeroStats

namespace Graffiti.FirstZero

private theorem profile_accounts (ds : List ℕ) (hp : ∀ d ∈ ds, 0 < d) :
    ds.count 1 + nonleafCount ds = ds.length ∧
    ds.count 2 + branchCount ds = nonleafCount ds ∧
    nonleafWeight ds + ds.count 1 = ds.sum ∧
    2 * ds.length + branchCount ds ≤ ds.sum + ds.count 1 := by
  induction ds with
  | nil => simp [nonleafCount, branchCount, nonleafWeight]
  | cons d ds ih =>
    obtain ⟨a,b,c,e⟩ := ih (fun x hx => hp x (List.mem_cons_of_mem _ hx))
    have hd := hp d (List.mem_cons_self ..)
    simp only [nonleafCount, branchCount, nonleafWeight] at *
    rcases d with _ | _ | _ | k
    · omega
    all_goals (simp [List.count_cons, List.filter_cons]; omega)

private theorem count_le_branches {d : ℕ} (hd : 2 < d) (ds : List ℕ) :
    ds.count d ≤ branchCount ds := by
  induction ds with
  | nil => simp [branchCount]
  | cons x xs ih =>
    by_cases h : x = d
    · subst x
      simpa [branchCount, List.filter_cons, hd] using Nat.succ_le_succ ih
    · rw [List.count_cons_of_ne h]
      by_cases hx : 2 < x <;> simp [branchCount, List.filter_cons, hx] at * <;> omega

/-- In a positive tree degree profile with a tie, exactly degrees one and two are modal. -/
theorem tied_profile {ds : List ℕ} {n : ℕ} (hlen : ds.length = n)
    (hsum : ds.sum + 2 = 2*n) (hp : ∀ d ∈ ds, 0 < d) (htie : 2 ≤ (modes ds).card) :
    modes ds = {1,2} ∧ 2 ≤ ds.count 1 ∧ ds.count 1 + nonleafCount ds = n ∧
    ds.count 1 + branchCount ds = nonleafCount ds ∧ nonleafWeight ds + ds.count 1 + 2 = 2*n := by
  obtain ⟨a,b,c,e⟩ := profile_accounts ds hp
  have leaves : 2 ≤ ds.count 1 := by omega
  have one : 1 ∈ ds.toFinset := List.mem_toFinset.mpr (List.count_pos_iff.mp (by omega))
  have sub : modes ds ⊆ ({1,2} : Finset ℕ) := by
    intro d hd
    obtain ⟨mem,maximal⟩ := Finset.mem_filter.mp hd
    have pos := hp d (List.mem_toFinset.mp mem)
    have bound := maximal 1 one
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra! h
    have := count_le_branches (d := d) (by omega) ds
    omega
  have eqm := Finset.eq_of_subset_of_card_le sub (show ({1,2} : Finset ℕ).card ≤ _ by simpa using htie)
  have modal (d : ℕ) (hd : d ∈ ({1,2} : Finset ℕ)) :
      d ∈ ds.toFinset ∧ ∀ x ∈ ds.toFinset, ds.count x ≤ ds.count d :=
    Finset.mem_filter.mp (show d ∈ modes ds from eqm.symm ▸ hd)
  have h₁ := modal 1 (by decide)
  have h₂ := modal 2 (by decide)
  have := le_antisymm (h₂.2 1 h₁.1) (h₁.2 2 h₂.1)
  exact ⟨eqm, leaves, by omega, by omega, by omega⟩

end Graffiti.FirstZero
