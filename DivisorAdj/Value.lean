import DivisorAdj.Basic

namespace DivisorAdj

private theorem prodSum_snoc (l : List ℕ) (x y : ℕ) :
    prodSum (l ++ [x,y]) = prodSum (l ++ [x]) + x*y := by
  induction l with
  | nil => simp [prodSum]
  | cons h t ih =>
    cases t with
    | nil => simp [prodSum]
    | cons z t =>
      change h*z + prodSum ((z :: t) ++ [x,y]) = h*z + prodSum ((z :: t) ++ [x]) + x*y
      rw [ih, Nat.add_assoc]

private theorem prodSum_reverse : ∀ l : List ℕ, prodSum l.reverse = prodSum l
  | [] => rfl
  | [_] => rfl
  | x :: y :: t => by
    rw [List.reverse_cons, List.reverse_cons, List.append_assoc]
    change prodSum (t.reverse ++ [y,x]) = _
    rw [prodSum_snoc, ← List.reverse_cons, prodSum_reverse (y :: t), prodSum]
    rw [Nat.mul_comm y x, Nat.add_comm]

private theorem first_coordinates (n : ℕ) :
    divs n = n.divisorsAntidiagonalList.map Prod.fst := by
  apply (Finset.sort_sorted_lt n.divisors).eq_of_mem_iff
    (Nat.sorted_divisorsAntidiagonalList_fst.map Prod.fst (fun _ _ h => h))
  intro d
  simp only [Finset.mem_sort, Nat.mem_divisors, List.mem_map]
  constructor
  · rintro ⟨⟨k, hk⟩, hn⟩
    exact ⟨(d,k), Nat.mem_divisorsAntidiagonalList.mpr ⟨hk.symm, hn⟩, rfl⟩
  · rintro ⟨⟨d,k⟩, hdk, rfl⟩
    obtain ⟨h, hn⟩ := Nat.mem_divisorsAntidiagonalList.mp hdk
    exact ⟨⟨k, h.symm⟩, hn⟩

private theorem paired_value {n : ℕ} (hn : 0 < n) :
    ∀ l : List (ℕ × ℕ), (∀ v ∈ l, v.1*v.2 = n) →
      (prodSum (l.map Prod.snd) : ℚ) = (n : ℚ)^2 * recipSum (l.map Prod.fst)
  | [], _ => by simp [prodSum, recipSum]
  | [_], _ => by simp [prodSum, recipSum]
  | (a,b) :: (c,d) :: t, h => by
    have hab : a*b = n := h (a,b) (by simp)
    have hcd : c*d = n := h (c,d) (by simp)
    have ha : 0 < a := Nat.pos_of_ne_zero (fun he => by simp [he] at hab; omega)
    have hc : 0 < c := Nat.pos_of_ne_zero (fun he => by simp [he] at hcd; omega)
    have he : (b : ℚ)*d = (n : ℚ)^2 * (1 / ((a : ℚ)*c)) := by
      rw [mul_one_div, eq_div_iff (by positivity)]
      calc
        _ = ((a : ℚ)*b)*((c : ℚ)*d) := by ring
        _ = (n : ℚ)^2 := by exact_mod_cast (by rw [hab, hcd, pow_two] : (a*b)*(c*d) = n^2)
    simp only [List.map_cons, prodSum, Nat.cast_add, Nat.cast_mul, recipSum, mul_add]
    exact congrArg₂ (· + ·) he (paired_value hn ((c,d) :: t) (fun v hv => h v (.tail _ hv)))

/-- Complementing each divisor reverses the divisor list; each adjacent pair
then contributes `n²` times the reciprocal of its old product. -/
theorem ratio_identity {n : ℕ} (hn : 0 < n) :
    (prodSum (divs n) : ℚ) = (n : ℚ)^2 * recipSum (divs n) := by
  rw [first_coordinates]
  rw [← prodSum_reverse, ← List.map_reverse, Nat.reverse_divisorsAntidiagonalList, List.map_map]
  exact paired_value hn _ (fun v hv => (Nat.mem_divisorsAntidiagonalList.mp hv).1)

private theorem recipSum_nonnegative : ∀ l : List ℕ, 0 ≤ recipSum l
  | [] => le_rfl
  | [_] => le_rfl
  | x :: y :: t => add_nonneg (by positivity) (recipSum_nonnegative (y :: t))

private theorem initial_pair {n : ℕ} (hn : 2 ≤ n) :
    ∃ b t, divs n = 1 :: b :: t ∧ b ≤ n.minFac := by
  have h0 : n ≠ 0 := by omega
  have h1 : 1 ∈ divs n := by simp [divs, h0]
  have hm : n.minFac ∈ divs n := by simp [divs, h0, Nat.minFac_dvd]
  have hmn := (Nat.minFac_prime (by omega : n ≠ 1)).two_le
  have hs : (divs n).Sorted (· < ·) := Finset.sort_sorted_lt _
  cases he : divs n with
  | nil => simp [he] at h1
  | cons x xs =>
    rw [he] at h1 hm hs
    have hxmem : x ∈ divs n := he ▸ List.mem_cons_self
    have hxpos : 0 < x := Nat.pos_of_mem_divisors ((Finset.mem_sort (· ≤ ·)).mp hxmem)
    have hx : x = 1 := by
      rcases List.mem_cons.mp h1 with h | h
      · exact h.symm
      · have := List.rel_of_pairwise_cons hs h
        omega
    subst x
    cases xs with
    | nil => simp at hm; omega
    | cons b t =>
      refine ⟨b, t, rfl, ?_⟩
      rcases List.mem_cons.mp hm with heq | htail
      · omega
      rcases List.mem_cons.mp htail with heq | ht
      · exact heq.ge
      · exact (List.rel_of_pairwise_cons (List.sorted_cons.mp hs).2 ht).le

/-- Both defining floor inequalities, normalized by the square of the index. -/
theorem floor_recipSum {n : ℕ} (hn : 2 ≤ n) :
    (a n : ℚ) * recipSum (divs n) ≤ 1 ∧ 1 < ((a n : ℚ) + 1) * recipSum (divs n) := by
  have hn' : 0 < n := by omega
  have hs : 0 < (n : ℚ)^2 := by positivity
  have hl : (a n : ℚ) * prodSum (divs n) ≤ (n : ℚ)^2 := by
    exact_mod_cast Nat.div_mul_le_self (n^2) (prodSum (divs n))
  have hu : (n : ℚ)^2 < (prodSum (divs n) : ℚ) * ((a n : ℚ)+1) := by
    exact_mod_cast Nat.lt_mul_div_succ (n^2) (prodSum_pos hn)
  rw [ratio_identity hn'] at hl hu
  constructor
  · apply (mul_le_mul_left hs).mp
    simpa [mul_comm,mul_left_comm,mul_assoc] using hl
  · apply (mul_lt_mul_left hs).mp
    simpa [mul_comm,mul_left_comm,mul_assoc] using hu

/-- The first reciprocal edge bounds the sequence by the smallest prime factor. -/
theorem a_le_minFactor {n : ℕ} (hn : 2 ≤ n) : a n ≤ n.minFac := by
  have hr := (floor_recipSum hn).1
  obtain ⟨b, t, he, hbm⟩ := initial_pair hn
  have hbmem : b ∈ divs n := by simp [he]
  have hbpos : 0 < (b : ℚ) := by
    exact_mod_cast Nat.pos_of_mem_divisors ((Finset.mem_sort (· ≤ ·)).mp hbmem)
  rw [he] at hr
  simp only [recipSum, Nat.cast_one, one_mul] at hr
  have hfrac : (a n : ℚ) * (1 / b) ≤ 1 := by
    nlinarith [mul_nonneg (show 0 ≤ (a n : ℚ) by positivity) (recipSum_nonnegative (b :: t))]
  rw [mul_one_div, div_le_iff₀ hbpos, one_mul] at hfrac
  exact le_trans (by exact_mod_cast hfrac : a n ≤ b) hbm

/-- Each occurrence of a prime factor gives the choice of including it or not. -/
private def subproducts : List ℕ → List ℕ
  | [] => [1]
  | p :: ps => let ds := subproducts ps; ds ++ ds.map (p * ·)

private theorem mem_subproducts {d : ℕ} (ps : List ℕ) (hp : ∀ p ∈ ps, Nat.Prime p) :
    d ∈ subproducts ps ↔ d ∣ ps.prod := by
  induction ps generalizing d with
  | nil => simp [subproducts]
  | cons p ps ih =>
    have prime := hp p (by simp)
    have rest : ∀ q ∈ ps, Nat.Prime q := fun q hq => hp q (.tail _ hq)
    simp only [subproducts, List.mem_append, List.mem_map, List.prod_cons, Nat.dvd_mul]
    constructor
    · rintro (hd | ⟨q, hq, rfl⟩)
      · exact ⟨1, d, one_dvd _, (ih rest).mp hd, one_mul _⟩
      · exact ⟨p, q, dvd_rfl, (ih rest).mp hq, rfl⟩
    · rintro ⟨x, y, hx, hy, rfl⟩
      rcases (Nat.dvd_prime prime).mp hx with rfl | rfl
      · exact Or.inl (by simpa using (ih rest).mpr hy)
      · exact Or.inr ⟨y, (ih rest).mpr hy, rfl⟩

private def candidateFactors : List ℕ := [11, 13, 17, 19, 23, 29, 31, 37]

private def candidateList : List ℕ :=
  (subproducts candidateFactors).insertionSort (· ≤ ·)

private theorem candidate_divisors : divs 35336848261 = candidateList := by
  have hprime : ∀ p ∈ candidateFactors, Nat.Prime p := by
    intro p hp
    simp only [candidateFactors, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with h|h|h|h|h|h|h|h <;> subst p <;> decide
  have hs : candidateList.Sorted (· < ·) :=
    List.chain'_iff_pairwise.mp (by decide +kernel : candidateList.Chain' (· < ·))
  apply (Finset.sort_sorted_lt _).eq_of_mem_iff hs
  intro d
  unfold candidateList
  rw [(List.perm_insertionSort (· ≤ ·) (subproducts candidateFactors)).mem_iff,
    mem_subproducts _ hprime]
  have hval : candidateFactors.prod = 35336848261 := rfl
  simp [hval]

/-- Only the 256 subset products of the eight primes are evaluated. -/
theorem candidate_value : a 35336848261 = 8 := by
  unfold a
  rw [candidate_divisors]
  decide +kernel

private theorem prodSum_zip : ∀ l : List ℕ,
    prodSum l = ((l.zip l.tail).map (fun p => p.1*p.2)).sum
  | [] => rfl
  | [_] => rfl
  | x :: y :: t => by
    change x*y + prodSum (y :: t) = x*y + _
    exact congrArg (x*y + ·) (prodSum_zip (y :: t))

/-- Range-and-filter formulation of the catalog definition. -/
theorem a_eq_range_spec {n : ℕ} (hn : 0 < n) :
    a n = let ds := (List.range (n+1)).filter (fun d => decide (d ∣ n))
          n^2 / ((ds.zip ds.tail).map (fun p => p.1*p.2)).sum := by
  have he : divs n = (List.range (n+1)).filter (fun d => decide (d ∣ n)) := by
    apply (Finset.sort_sorted_lt _).eq_of_mem_iff ((List.sorted_lt_range _).filter _)
    intro d
    simp only [Finset.mem_sort, Nat.mem_divisors, List.mem_filter, List.mem_range,
      decide_eq_true_eq]
    exact ⟨fun h => ⟨by have := Nat.le_of_dvd hn h.1; omega, h.1⟩,
      fun h => ⟨h.2, hn.ne'⟩⟩
  unfold a
  rw [prodSum_zip, he]

end DivisorAdj
