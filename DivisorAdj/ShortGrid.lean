import DivisorAdj.RunDensity

/-! # Short prefix certificates for the small gaps in Wilson's conjecture

Each row covers an entire interval of targets. Rounding every reciprocal edge
*down* after multiplication by 10¹² makes verification pure integer arithmetic.
The prime list need not be complete: the actual product includes every prime.
-/

namespace DivisorAdj

private def units (b x : ℕ) : List ℕ → ℕ
  | [] => 0
  | y :: ys => b/(x*y) + units b y ys

private theorem units_le (b x : ℕ) (xs : List ℕ) :
    (units b x xs : ℚ) ≤ (b : ℚ)*recipSum (x :: xs) := by
  induction xs generalizing x with
  | nil => simp [units,recipSum]
  | cons y ys ih =>
    simp only [units,Nat.cast_add,recipSum,mul_add]
    apply add_le_add _ (ih y)
    simpa only [Nat.cast_mul, div_eq_mul_inv, one_mul] using
      (Nat.cast_div_le (m := b) (n := x*y) (α := ℚ))

private abbrev scale : ℕ := 1000000000000

private def pool : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,
  101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,
  233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,
  383,389,397,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,503,509,521,523,541,
  547,557,563,569,571,577,587,593,599,601]

private def sample (p m : ℕ) := (pool.dropWhile fun q => decide (q<p)).take m

private def rows : List (ℕ × ℕ) := [(2,2),(5,5),(7,2),(11,8),(13,2),(17,5),(19,2),(23,5),(29,13),
  (31,2),(37,10),(41,4),(43,2),(47,4),(53,8),(59,7),(61,2),(67,7),(73,8),(79,7),(83,4),(89,7),
  (97,10),(101,4),(107,7),(113,7),(127,30),(131,4),(139,10),(149,13),(157,9),(163,6),(167,4),
  (173,6),(181,9),(191,12),(199,10),(211,16),(223,15),(229,6),(239,12),(251,15),(257,6),(263,6),
  (269,6),(277,9),(283,6),(293,12),(307,18),(317,12),(331,18),(337,6),(347,11),(359,14),(367,8),
  (379,14),(389,11),(397,8),(409,14),(421,13),(431,10),(443,13),(457,16),(467,11),(479,14),
  (487,8),(499,14),(509,11),(521,13)]

private def good (lo p : ℕ) (xs : List ℕ) : Prop :=
  xs.Chain' (· < ·) ∧ (∀ q ∈ xs, q.Prime ∧ p ≤ q ∧ q ≤ 601) ∧ scale < (lo+1)*units scale 1 xs

private instance (lo p : ℕ) (xs : List ℕ) : Decidable (good lo p xs) := by unfold good; infer_instance

private def check (lo : ℕ) : List (ℕ × ℕ) → Bool
  | [] => decide (511 < lo)
  | (p,m) :: rs => decide (good lo p (sample p m)) && check (p+1) rs

private theorem sound {lo k : ℕ} {rs : List (ℕ × ℕ)} (hc : check lo rs = true)
    (hl : lo ≤ k) (hk : k ≤ 511) : WilsonValue k := by
  induction rs generalizing lo with
  | nil => simp only [check,decide_eq_true_eq] at hc; omega
  | cons r rs ih =>
    obtain ⟨p,m⟩ := r
    obtain ⟨hrow,htail⟩ := Bool.and_eq_true_iff.mp hc
    by_cases hp : k ≤ p
    · let xs := sample p m
      obtain ⟨hs,hm,hr⟩ := (of_decide_eq_true hrow : good lo p xs)
      apply wilson_of_prefix (t := 601) xs (List.chain'_iff_pairwise.mp hs)
      · intro q h; obtain ⟨hq,hpq,hq'⟩ := hm q h; exact ⟨hq,hp.trans hpq,hq'⟩
      · have h₁ : (scale : ℚ) < ((lo : ℚ)+1)*units scale 1 xs := by exact_mod_cast hr
        have h₂ : ((lo : ℚ)+1)*(units scale 1 xs : ℚ) ≤ ((k : ℚ)+1)*(scale * recipSum (1 :: xs)) :=
          mul_le_mul (by exact_mod_cast Nat.add_le_add_right hl 1) (units_le ..) (by positivity) (by positivity)
        have h₃ : (scale : ℚ)*1 < (scale : ℚ)*(((k : ℚ)+1)*recipSum (1 :: xs)) := by
          calc _ = (scale : ℚ) := mul_one _
               _ < _ := h₁.trans_le h₂
               _ = _ := by ring
        exact (mul_lt_mul_left (by norm_num : 0 < (scale : ℚ))).mp h₃
    · exact ih htail (by omega)

set_option maxRecDepth 6000 in
private theorem checked : check 1 rows = true := by decide +kernel

theorem wilson_small {k : ℕ} (hk : 0 < k) (h : k < 512) : WilsonValue k :=
  sound checked hk (by omega)

end DivisorAdj
