import DivisorAdj.Steps
import DivisorAdj.Monotone

/-! # Adding a new largest prime cannot skip a value of A251758

This supplies an intermediate-value theorem for the primorial quotients in
[Wilson's conjecture](https://oeis.org/A251758). It does not assume that the
endpoint of each run falls far enough to cover the preceding prime gap.
-/

namespace DivisorAdj

open Finset

private theorem left_weight {x y z : ℕ} (hx : 0 < x) (hy : 0 < y) (h : x ≤ z) :
    weight (z,y) ≤ weight (x,y) := by
  unfold weight
  apply one_div_le_one_div_of_le (by dsimp; positivity)
  exact_mod_cast Nat.mul_le_mul_right y h

/-- Every nonfinal old divisor has an old divisor strictly between `d` and `q*d`:
attach a prime factor of the unused cofactor. -/
private theorem next_before_multiple {n q d : ℕ} (hd : d ∈ n.divisors) (hlt : d < n)
    (hs : ∀ p ∈ n.primeFactors, p < q) : ∃ z ∈ n.divisors, d < z ∧ z < q*d := by
  obtain ⟨m,hm⟩ := Nat.dvd_of_mem_divisors hd
  have hm1 : m ≠ 1 := by rintro rfl; simp at hm; omega
  let p := m.minFac
  have hp : p.Prime := Nat.minFac_prime hm1
  have hpm : p ∣ m := Nat.minFac_dvd m
  have hpn : p ∣ n := hm ▸ dvd_mul_of_dvd_right hpm d
  have hpq := hs p (Nat.mem_primeFactors.mpr ⟨hp,hpn,(Nat.mem_divisors.mp hd).2⟩)
  have hdpos := Nat.pos_of_mem_divisors hd
  refine ⟨d*p,Nat.mem_divisors.mpr ⟨hm ▸ Nat.mul_dvd_mul_left d hpm,(Nat.mem_divisors.mp hd).2⟩,
    lt_mul_of_one_lt_right hdpos hp.one_lt,?_⟩
  simpa [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_left hpq hdpos

private def budget (q : ℕ) (z : Fin 3 × (ℕ × ℕ)) : ℚ := weight z.2 / (q : ℚ)^z.1.val

private def endpoint (q : ℕ) (z : Fin 3 × (ℕ × ℕ)) : ℕ :=
  if z.1 = 0 then z.2.2 else if z.1 = 1 then q*z.2.1 else q*z.2.2

private theorem charge_step {n q x y : ℕ} (hn : 2 ≤ n) (hq : q.Prime)
    (hs : ∀ p ∈ n.primeFactors, p < q) (he : (x,y) ∈ steps (n*q).divisors) :
    ∃ z ∈ (univ : Finset (Fin 3)) ×ˢ steps n.divisors,
      y = endpoint q z ∧ weight (x,y) ≤ budget q z := by
  have hnp : 0 < n := by omega
  have hlarge : n*q ≠ 0 := (Nat.mul_pos hnp hq.pos).ne'
  have old {d : ℕ} (hd : d ∈ n.divisors) : d ∈ (n*q).divisors :=
    Nat.mem_divisors.mpr ⟨dvd_mul_of_dvd_left (Nat.dvd_of_mem_divisors hd) q,hlarge⟩
  have newD {d : ℕ} (hd : d ∈ n.divisors) : q*d ∈ (n*q).divisors := by
    apply Nat.mem_divisors.mpr ⟨_,hlarge⟩
    simpa only [Nat.mul_comm q n] using Nat.mul_dvd_mul_left q (Nat.dvd_of_mem_divisors hd)
  obtain ⟨hx,hy,hxy,hgap⟩ := mem_steps.mp he
  have prev {z : ℕ} (h : z ∈ (n*q).divisors) (hz : z < y) : z ≤ x :=
    (hgap z h).resolve_right (not_le_of_gt hz)
  have h1 : 1 ∈ n.divisors := Nat.mem_divisors.mpr ⟨one_dvd _,hnp.ne'⟩
  by_cases hyold : y ∈ n.divisors
  · have hxp := Nat.pos_of_mem_divisors hx
    obtain ⟨b,hb⟩ := exists_step_before hyold h1 (show 1 < y by omega)
    have hb' := mem_steps.mp hb
    refine ⟨(0,(b,y)),mem_product.mpr ⟨mem_univ _,hb⟩,rfl,?_⟩
    simpa [budget] using left_weight (Nat.pos_of_mem_divisors hb'.1)
      (Nat.pos_of_mem_divisors hyold) (prev (old hb'.1) hb'.2.2.1)
  obtain ⟨d,b,hd,hb,hyb⟩ := Nat.dvd_mul.mp (Nat.dvd_of_mem_divisors hy)
  have hd' : d ∈ n.divisors := Nat.mem_divisors.mpr ⟨hd,hnp.ne'⟩
  have hde : y = q*d := by
    rcases (Nat.dvd_prime hq).mp hb with hb1 | hbq
    · rw [hb1, mul_one] at hyb
      exact (hyold (hyb ▸ hd')).elim
    · simpa [hbq, Nat.mul_comm] using hyb.symm
  have htop : n ∈ n.divisors := Nat.mem_divisors.mpr ⟨dvd_rfl,hnp.ne'⟩
  by_cases hdtop : d = n
  · subst d
    obtain ⟨b,hb⟩ := exists_step_before htop h1 (by omega : 1 < n)
    have hb' := mem_steps.mp hb
    have hleft := prev (newD hb'.1) (hde ▸ Nat.mul_lt_mul_of_pos_left hb'.2.2.1 hq.pos)
    refine ⟨(2,(b,n)),mem_product.mpr ⟨mem_univ _,hb⟩,hde,?_⟩
    rw [hde]
    calc weight (x,q*n) ≤ weight (q*b,q*n) :=
           left_weight (Nat.mul_pos hq.pos (Nat.pos_of_mem_divisors hb'.1)) (Nat.mul_pos hq.pos hnp) hleft
         _ = _ := by simp [budget,weight,div_eq_mul_inv,pow_two,Nat.cast_mul,mul_comm,mul_left_comm,mul_assoc]
  · have hdt : d < n := lt_of_le_of_ne (Nat.le_of_dvd hnp hd) hdtop
    obtain ⟨z,hz,hdz,hzq⟩ := next_before_multiple hd' hdt hs
    obtain ⟨b,hb⟩ := exists_step_after hd' hz hdz
    have hb' := mem_steps.mp hb
    have hbz := (hb'.2.2.2 z hz).resolve_left (not_le_of_gt hdz)
    have hleft := prev (old hb'.2.1) (hde ▸ hbz.trans_lt hzq)
    refine ⟨(1,(d,b)),mem_product.mpr ⟨mem_univ _,hb⟩,hde,?_⟩
    rw [hde]
    calc weight (x,q*d) ≤ weight (b,q*d) :=
           left_weight (Nat.pos_of_mem_divisors hb'.2.1) (Nat.mul_pos hq.pos (Nat.pos_of_mem_divisors hd')) hleft
         _ = _ := by simp [budget,weight,div_eq_mul_inv,Nat.cast_mul,mul_comm,mul_left_comm,mul_assoc]

/-- The three charges on an old edge have relative sizes 1, 1/q and 1/q².
The last charge is used on just the final edge. -/
theorem new_prime_recip_bound {n q : ℕ} (hn : 2 ≤ n) (hq : q.Prime)
    (hs : ∀ p ∈ n.primeFactors, p < q) :
    recipSum (divs (n*q)) ≤ (1 + 1/(q:ℚ) + 1/(q:ℚ)^2) * recipSum (divs n) := by
  classical
  let S := steps (n*q).divisors
  let T := (univ : Finset (Fin 3)) ×ˢ steps n.divisors
  have claim (e : S) := charge_step hn hq hs e.property
  choose f hm hy hcost using claim
  have hinj : Function.Injective f := by
    intro e j h
    have hends : e.val.2 = j.val.2 := (hy e).trans (h ▸ (hy j).symm)
    exact Subtype.ext (same_step_of_end e.property j.property hends)
  have sub : S.attach.image f ⊆ T := by
    intro z hz
    obtain ⟨e,_,rfl⟩ := mem_image.mp hz
    exact hm e
  calc
    recipSum (divs (n*q)) = ∑ e ∈ S.attach, weight e.val := (divisor_steps _).trans (sum_attach S _).symm
    _ ≤ ∑ e ∈ S.attach, budget q (f e) := sum_le_sum fun e _ => hcost e
    _ = ∑ z ∈ S.attach.image f, budget q z := (sum_image hinj.injOn).symm
    _ ≤ ∑ z ∈ T, budget q z := sum_le_sum_of_subset_of_nonneg sub (by intros; unfold budget weight; positivity)
    _ = _ := by
      rw [divisor_steps,show T = (univ : Finset (Fin 3)) ×ˢ steps n.divisors from rfl,sum_product,
        Fin.sum_univ_three]
      simp only [budget,Fin.val_zero,pow_zero,div_one,Fin.val_one,pow_one,
        show (2 : Fin 3).val = 2 from rfl,← sum_div]
      ring

/-- Along an increasing prime run the floor either stays put or drops by one. -/
theorem new_prime_step {n q : ℕ} (hn : 2 ≤ n) (hq : q.Prime)
    (hs : ∀ p ∈ n.primeFactors, p < q) : a (n*q) ≤ a n ∧ a n ≤ a (n*q)+1 := by
  have hqpos : 0 < (q : ℚ) := by exact_mod_cast hq.pos
  have hlarge : 2 ≤ n*q := hn.trans (Nat.le_mul_of_pos_right n hq.pos)
  refine ⟨a_antitone_dvd hn hlarge (dvd_mul_right _ _),?_⟩
  have hmin := hs n.minFac (Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega),Nat.minFac_dvd n,by omega⟩)
  have han := a_le_minFactor hn
  by_contra! H
  have hsmall : (a (n*q) : ℚ)+1 ≤ (q : ℚ)-1 := by
    apply (le_sub_iff_add_le).mpr
    exact_mod_cast (show (a (n*q)+1)+1 ≤ q by omega)
  have hdiff : ((q : ℚ)-1) * (1/(q:ℚ)+1/(q:ℚ)^2) ≤ 1 := by
    calc
      _ = 1 - 1/(q:ℚ)^2 := by field_simp [hqpos.ne']; ring
      _ ≤ _ := sub_le_self _ (by positivity)
  have hcost : ((a (n*q) : ℚ)+1) * (1+1/(q:ℚ)+1/(q:ℚ)^2) ≤ (a n : ℚ) := by
    have hle : (a (n*q) : ℚ)+2 ≤ (a n : ℚ) := by exact_mod_cast (show a (n*q)+2 ≤ a n by omega)
    nlinarith [mul_le_mul_of_nonneg_right hsmall (by positivity : 0 ≤ 1/(q:ℚ)+1/(q:ℚ)^2)]
  have hS : 0 ≤ recipSum (divs n) := by rw [divisor_steps]; apply sum_nonneg; intros; unfold weight; positivity
  have bad := calc
    1 < ((a (n*q) : ℚ)+1) * recipSum (divs (n*q)) := (floor_recipSum hlarge).2
    _ ≤ ((a (n*q) : ℚ)+1) * ((1+1/(q:ℚ)+1/(q:ℚ)^2) * recipSum (divs n)) :=
      mul_le_mul_of_nonneg_left (new_prime_recip_bound hn hq hs) (by positivity)
    _ ≤ (a n : ℚ) * recipSum (divs n) := by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hcost hS
    _ ≤ 1 := (floor_recipSum hn).1
  exact lt_irrefl _ bad

/-- Every integer between the endpoints occurs, even when the appended primes
are not consecutive and the starting integer is not squarefree. -/
theorem prime_run_intermediate (ps : List ℕ) {n k : ℕ} (hn : 2 ≤ n)
    (hp : ∀ q ∈ ps, Nat.Prime q) (hord : ps.Sorted (· < ·))
    (hs : ∀ q ∈ ps, ∀ p ∈ n.primeFactors, p < q) (hlo : a (n*ps.prod) ≤ k) (hhi : k ≤ a n) :
    ∃ before after, ps = before ++ after ∧ a (n*before.prod) = k := by
  by_cases e : a n = k
  · exact ⟨[],ps,rfl,by simpa using e⟩
  induction ps generalizing n with
  | nil => simp at hlo; omega
  | cons q qs ih =>
    have hq := hp q List.mem_cons_self
    have step := (new_prime_step hn hq (hs q List.mem_cons_self)).2
    have hqn : 2 ≤ n*q := hn.trans (Nat.le_mul_of_pos_right n hq.pos)
    have low : a ((n*q)*qs.prod) ≤ k := by simpa [Nat.mul_assoc] using hlo
    have cap : k ≤ a (n*q) := by omega
    by_cases he : a (n*q) = k
    · exact ⟨[q],qs,rfl,by simpa using he⟩
    have fresh (r : ℕ) (hr : r ∈ qs) (p : ℕ) (h : p ∈ (n*q).primeFactors) : p < r := by
      obtain ⟨prime,hd,_⟩ := Nat.mem_primeFactors.mp h
      rcases prime.dvd_mul.mp hd with hpn|hpq
      · exact hs r (.tail _ hr) p (Nat.mem_primeFactors.mpr ⟨prime,hpn,by omega⟩)
      · rcases (Nat.dvd_prime hq).mp hpq with h1|rfl
        · exact (prime.ne_one h1).elim
        · exact List.rel_of_pairwise_cons hord hr
    obtain ⟨b,c,eqs,hk⟩ := ih hqn (fun r hr => hp r (.tail _ hr)) (List.sorted_cons.mp hord).2 fresh low cap he
    exact ⟨q :: b,c,by simp [eqs],by simpa [Nat.mul_assoc] using hk⟩

end DivisorAdj
