import DivisorAdj.Basic

namespace DivisorAdj

private def eightPrimes : Fin 8 → ℕ := ![11, 13, 17, 19, 23, 29, 31, 37]

/-- No prime lies strictly between two consecutive entries of the table. -/
private theorem next_bound (j : Fin 7) (p : ℕ) (hp : p.Prime)
    (h : eightPrimes j.castSucc < p) : eightPrimes j.succ ≤ p := by
  have htop : ∀ i : Fin 8, eightPrimes i ≤ 37 := by decide
  by_cases hlt : p < 37
  · have table : ∀ i : Fin 7, ∀ q : Fin 37, q.val.Prime →
        eightPrimes i.castSucc < q.val → eightPrimes i.succ ≤ q.val := by decide
    exact table j ⟨p, hlt⟩ hp h
  · exact (htop _).trans (Nat.le_of_not_lt hlt)

/-- The gap condition propagates a lower bound along an increasing list of primes. -/
private theorem rank_lower {m k : ℕ} (P : Fin (m+1) → ℕ)
    (hnext : ∀ i : Fin m, ∀ p : ℕ, p.Prime → P i.castSucc < p → P i.succ ≤ p)
    (f : Fin k → ℕ) (hm : StrictMono f)
    (hp : ∀ i, (f i).Prime) (hl : ∀ i, P 0 ≤ f i) (j : Fin (m+1)) :
    ∀ hj : j.val < k, P j ≤ f ⟨j.val, hj⟩ := by
  induction j using Fin.induction with
  | zero => intro h; exact hl ⟨0, h⟩
  | succ i ih =>
    intro hi
    have hprev : i.val < k := by change i.val + 1 < k at hi; omega
    apply hnext i _ (hp _)
    exact lt_of_le_of_lt (ih hprev) (hm (show (⟨i.val, hprev⟩ : Fin k) < ⟨i.succ.val, hi⟩ from Nat.lt_succ_self _))

/-- Either the whole table bounds a product dividing `n`, or its initial segment
can accommodate all distinct prime factors in order. -/
theorem rank_threshold_of_table {m n : ℕ} (P : Fin (m+1) → ℕ)
    (hnext : ∀ i : Fin m, ∀ p : ℕ, p.Prime → P i.castSucc < p → P i.succ ≤ p)
    (hn : 0 < n) (hmin : ∀ p ∈ n.primeFactors, P 0 ≤ p) :
    (m+1 ≤ n.primeFactors.card → (∏ j, P j) ≤ n) ∧
    (n.primeFactors.card ≤ m → Nonempty (Slots (fun i : Fin m => P i.castSucc) n)) := by
  classical
  let e := n.primeFactors.orderIsoOfFin rfl
  let f : Fin n.primeFactors.card → ℕ := fun i => (e i).val
  have hm : StrictMono f := fun _ _ hij => e.strictMono hij
  have hb := rank_lower P hnext f hm (fun i => Nat.prime_of_mem_primeFactors (e i).property)
    (fun i => hmin _ (e i).property)
  constructor
  · intro h
    let g : Fin (m+1) → ℕ := fun j => f ⟨j.val, j.isLt.trans_le h⟩
    have hg : StrictMono g := fun _ _ hij => hm hij
    have hs : Finset.univ.image g ⊆ n.primeFactors := by
      intro p hp
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hp
      exact (e _).property
    have hd := Finset.prod_dvd_prod_of_subset _ _ (fun p : ℕ => p) hs
    rw [Finset.prod_image (fun _ _ _ _ he => hg.injective he)] at hd
    have hprod : (∏ j, g j) ≤ n := Nat.le_of_dvd hn (hd.trans (Nat.prod_primeFactors_dvd n))
    exact (Finset.prod_le_prod' (fun j _ => hb j _) : (∏ j, P j) ≤ ∏ j, g j).trans hprod
  intro hc
  let slot : n.primeFactors → Fin m := fun p => (e.symm p).castLE hc
  refine ⟨⟨slot, fun _ _ hij => e.symm.strictMono hij, ?_⟩⟩
  intro p
  have hp := hb (slot p).castSucc (e.symm p).isLt
  simpa [slot, f] using hp

theorem rank_threshold {n : ℕ} (hn : 0 < n) (hmin : ∀ p ∈ n.primeFactors, 11 ≤ p) :
    (8 ≤ n.primeFactors.card → 35336848261 ≤ n) ∧ (n.primeFactors.card ≤ 7 → Nonempty (Slots firstPrime n)) := by
  obtain ⟨low, pack⟩ := rank_threshold_of_table eightPrimes next_bound hn hmin
  have hval : (∏ j, eightPrimes j) = 35336848261 := by decide
  have heq : (fun i : Fin 7 => eightPrimes i.castSucc) = firstPrime :=
    funext (by decide)
  rw [hval] at low
  rw [heq] at pack
  exact ⟨low, pack⟩

theorem exists_slots {n : ℕ} (hn : 0 < n) (hmin : ∀ p ∈ n.primeFactors, 11 ≤ p)
    (hlt : n < 35336848261) : Nonempty (Slots firstPrime n) := by
  obtain ⟨low, pack⟩ := rank_threshold hn hmin
  exact pack (by by_contra! h; exact (not_le_of_gt hlt) (low h))

end DivisorAdj
