import Graffiti.TripodRelayCost
import Graffiti.TripodDistance
import Graffiti.PeripheralCover
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # The best coefficient in Written on the Wall II, 363

The largest real constant `c` for which `γₜ ≥ i(S) + c · mean(d(·,B))` holds
on all nontrivial trees in the catalog domain is **3/10**. The positive bound
even holds for arbitrary finite connected graphs of order at least two.
For every larger coefficient the deficit is unbounded already on trees.

Gebendorfer's earlier family ruled out every `c > 1/3`, and explicitly left
`1/3` and unbounded additive deficit unresolved:
https://github.com/google-deepmind/formal-conjectures/issues/7360 .
The average below is definition 109, over nonperipheral vertices only:
https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/definitions.json .
-/

namespace Graffiti
open Finset SimpleGraph SupportCounting
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Denominator and numerator of the positive-distance peripheral mean. -/
noncomputable def peripheralSamples (G : SimpleGraph V) := (peripheralVertices G)ᶜ.card
noncomputable def peripheralDistanceSum (G : SimpleGraph V) :=
  ∑ x ∈ (peripheralVertices G)ᶜ, distanceToVertices G (peripheralVertices G) x

noncomputable def peripheralMean (G : SimpleGraph V) : ℝ := peripheralDistanceSum G / (peripheralSamples G : ℝ)

/-- Positive values violate the proposed lower bound at coefficient `c`. -/
noncomputable def peripheralDeficit (c : ℝ) (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  (isolatedSupports G).card + c * peripheralMean G - totalDominationNumber G

/-- Every isolated support belongs to the total dominating set. Removing all
of them leaves a distance-two dominating set, because an isolated support
has no support as a neighbor. -/
theorem peripheral_mean_budget {G : SimpleGraph V} [DecidableRel G.Adj] (hc : G.Connected)
    {D : Finset V} (hd : TotallyDominates G D) :
    ((isolatedSupports G).card : ℝ) + (3/10 : ℝ) * peripheralMean G ≤ D.card := by
  let I := isolatedSupports G
  let R := D \ I
  have sub : I ⊆ D := fun x hx => support_forced G hd (mem_filter.mp hx).1
  have cover (x : V) : ∃ r ∈ R, G.dist x r ≤ 2 := by
    obtain ⟨y,hy,hxy⟩ := hd x
    by_cases h : y ∈ I
    · obtain ⟨z,hz,hyz⟩ := hd y
      have out : z ∉ I := by
        intro hzi
        have hp := card_pos.mpr (show ((supportVertices G).filter (G.Adj y)).Nonempty from
          ⟨z,mem_filter.mpr ⟨(mem_filter.mp hzi).1,hyz⟩⟩)
        have eq : ((supportVertices G).filter (G.Adj y)).card = 0 := (mem_filter.mp h).2
        omega
      refine ⟨z,mem_sdiff.mpr ⟨hz,out⟩,?_⟩
      simpa only [dist_eq_one_iff_adj.mpr hxy,dist_eq_one_iff_adj.mpr hyz] using
        hc.dist_triangle (u := x) (v := y) (w := z)
    · exact ⟨y,mem_sdiff.mpr ⟨hy,h⟩,by rw [dist_eq_one_iff_adj.mpr hxy]; decide⟩
  have sum : 3 * peripheralDistanceSum G ≤ peripheralSamples G * (10*R.card) := by
    unfold peripheralDistanceSum peripheralSamples
    rw [mul_sum]
    simpa only [sum_const, smul_eq_mul] using
      (sum_le_sum (s := (peripheralVertices G)ᶜ) (fun x _ => peripheral_distance_budget hc cover x))
  have bound : (3/10 : ℝ)*peripheralMean G ≤ R.card := by
    by_cases h0 : peripheralSamples G = 0
    · simp [peripheralMean,h0]
    have hp : 0 < (peripheralSamples G : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h0
    have hs : (3:ℝ)*(peripheralDistanceSum G : ℝ) ≤ (peripheralSamples G : ℝ)*(10*(R.card : ℝ)) := by exact_mod_cast sum
    rw [peripheralMean,← mul_div_assoc,div_le_iff₀ hp]
    nlinarith only [hs]
  have part : (R.card : ℝ) + (I.card : ℝ) = D.card := by exact_mod_cast card_sdiff_add_card_eq_card sub
  change (I.card : ℝ) + _ ≤ _
  linarith

/-- The positive side of the sharp result; no tree hypothesis. -/
theorem peripheral_three_tenths {G : SimpleGraph V} [DecidableRel G.Adj] [Nontrivial V]
    (hc : G.Connected) : peripheralDeficit (3/10) G ≤ 0 := by
  obtain ⟨D,hd,he⟩ := exists_min_total_set hc
  unfold peripheralDeficit
  rw [← he]
  exact sub_nonpos.mpr (peripheral_mean_budget hc hd)

namespace PeripheralTripod

open scoped Classical

private theorem bouquet_mass (m N : ℕ) : N ≤ peripheralSamples (tree m N) ∧
    peripheralSamples (tree m N) ≤ Fintype.card (Base m) + N ∧
    N * (10*m+9) ≤ peripheralDistanceSum (tree m N) := by
  let f (i : Fin N) : Vertex m N := bunch i
  let B := univ.image f
  have inj : Function.Injective f := fun _ _ h => Sum.inr.inj h
  have size : B.card = N := by
    change (univ.image f).card = N
    rw [card_image_of_injective _ inj,card_univ,Fintype.card_fin]
  let S := (peripheralVertices (tree m N))ᶜ
  let d (x : Vertex m N) := distanceToVertices (tree m N) (peripheralVertices (tree m N)) x
  have sub : B ⊆ S := by
    intro x hx; obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    exact mem_compl.mpr (bunch_nonperipheral m N i)
  refine ⟨size.symm.le.trans (card_le_card sub), ?_, ?_⟩
  · change S.card ≤ _
    simpa only [Vertex,Fintype.card_sum,Fintype.card_fin] using S.card_le_univ
  · have lo : ∑ _ ∈ B, (10*m+9) ≤ ∑ x ∈ B, d x := by
      apply sum_le_sum; intro x hx; obtain ⟨i,_,rfl⟩ := mem_image.mp hx
      exact bunch_distance m N i
    have hi := sum_le_sum_of_subset_of_nonneg (f := d) sub (fun _ _ _ => Nat.zero_le _)
    simpa only [sum_const,smul_eq_mul,size] using lo.trans hi

/-- Arbitrarily large violations for every `c > 3/10`. All displayed trees
have order greater than two and a nonempty positive-distance sample. -/
theorem deficit_unbounded (c : ℝ) (hc : 3/10 < c) (K : ℕ) :
    ∃ m N : ℕ, 2 < Fintype.card (Vertex m N) ∧ 0 < peripheralSamples (tree m N) ∧
      (K : ℝ) < peripheralDeficit c (tree m N) := by
  have slope : 0 < 10*c - 3 := by linarith
  have posc : 0 ≤ c := by linarith
  obtain ⟨m,hm⟩ := exists_nat_gt (((K : ℝ)+3-9*c)/(10*c-3))
  have step := (div_lt_iff₀ slope).mp hm
  let M : ℝ := K + (3*(m:ℝ)+3)
  let L : ℝ := 10*(m:ℝ)+9
  let A : ℝ := Fintype.card (Base m)
  have pos : 0 < c*L-M := by dsimp [M,L]; nlinarith only [step]
  obtain ⟨N,hN⟩ := exists_nat_gt (max 2 (M*A/(c*L-M)))
  have hN₂ : (2:ℝ) < N := lt_of_le_of_lt (le_max_left ..) hN
  have hn : 2 < N := by exact_mod_cast hN₂
  have amplify := (div_lt_iff₀ pos).mp (lt_of_le_of_lt (le_max_right ..) hN)
  obtain ⟨hl,hu,hs⟩ := bouquet_mass m N
  have hpos : 0 < peripheralSamples (tree m N) := by omega
  refine ⟨m,N,?_,hpos,?_⟩
  · simp only [Vertex,Fintype.card_sum,Fintype.card_fin]; omega
  have cmp : M * (A + N) < c * ((N:ℝ)*L) := by nlinarith only [amplify]
  have hsum : (N:ℝ)*L ≤ peripheralDistanceSum (tree m N) := by dsimp [L]; exact_mod_cast hs
  have hupper : (peripheralSamples (tree m N) : ℝ) ≤ A + N := by dsimp [A]; exact_mod_cast hu
  have mnon : 0 ≤ M := by dsimp [M]; positivity
  have capped := lt_of_le_of_lt (mul_le_mul_of_nonneg_left hupper mnon) cmp
  have mean : M < c * peripheralMean (tree m N) := by
    rw [peripheralMean,← mul_div_assoc,lt_div_iff₀ (show (0:ℝ) < peripheralSamples (tree m N) by exact_mod_cast hpos)]
    exact capped.trans_le (mul_le_mul_of_nonneg_left hsum posc)
  have d : (totalDominationNumber (tree m N) : ℝ) ≤ (isolatedSupports (tree m N)).card + (3*(m:ℝ)+3) := by
    exact_mod_cast relay_cost m N
  dsimp [M] at mean
  unfold peripheralDeficit
  linarith

end PeripheralTripod

/-- No convention for an empty mean enters the optimality statement. -/
def validPeripheralCoefficients : Set ℝ := {c | ∀ (W : Type) [Fintype W] [DecidableEq W]
    (T : SimpleGraph W) [DecidableRel T.Adj], T.IsTree → 2 < Fintype.card W →
    0 < peripheralSamples T → peripheralDeficit c T ≤ 0}

theorem sharp_peripheral_coefficient : IsGreatest validPeripheralCoefficients (3/10) := by
  classical
  constructor
  · intro W _ _ T _ ht hn _
    letI : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    exact peripheral_three_tenths ht.isConnected
  · intro c hc
    by_contra! h
    obtain ⟨m,N,hn,hs,bad⟩ := PeripheralTripod.deficit_unbounded c h 0
    exact (not_lt_of_ge (hc _ _ (PeripheralTripod.isTree m N) hn hs)) (by simpa using bad)

open scoped Classical in
/-- In particular the proposed one-third repair has unbounded additive deficit. -/
theorem third_deficit_unbounded (K : ℕ) : ∃ m N : ℕ, 2 < Fintype.card (PeripheralTripod.Vertex m N) ∧
    0 < peripheralSamples (PeripheralTripod.tree m N) ∧ (K : ℝ) < peripheralDeficit (1/3) (PeripheralTripod.tree m N) :=
  PeripheralTripod.deficit_unbounded (1/3) (by norm_num) K

end Graffiti

#print axioms Graffiti.sharp_peripheral_coefficient
#print axioms Graffiti.third_deficit_unbounded
