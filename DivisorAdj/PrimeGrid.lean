import DivisorAdj.Grid.Checker

/-! # Prime density for the finite range [512, 400000]

Each row is a band `[a,b]` and a distance `g`. The elaborators generate two
lists of *witnesses*, not primality proofs: a sparse grid with spacing ≤ `g+1`
and enough distinct primes in the common interval `(b+g,2a]`. The logical
checker independently validates every entry and both bounds in the kernel.
The greedy choice of grid point and the choice of bands are irrelevant to
soundness. No prime-counting estimates are used.
-/

namespace DivisorAdj
open Grid

-- Greedily cover as many new integers as possible at each grid point.
local elab "gridPts%" a:num b:num g:num : term => do
  let mut next := a.getNat
  let mut pts := #[]
  while next ≤ b.getNat do
    let mut q := next + g.getNat
    while !decide q.Prime do
      if q ≤ next then throwError "prime grid has an uncovered integer: {next}"
      q := q - 1
    pts := pts.push q
    next := q + 1
  return Lean.toExpr pts.toList

local elab "samplePts%" a:num b:num g:num : term => do
  let (a, b, g) := (a.getNat, b.getNat, g.getNat)
  let size := 4*(b+g)*(g-1)/(a+1)+1
  let mut q := b+g
  let mut pts := #[]
  for _ in [:size] do
    q := q+1
    while !decide q.Prime do q := q+1
    pts := pts.push q
  return Lean.toExpr pts.toList

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

local macro "row " nm:ident a:num b:num g:num : command =>
  `(private theorem $nm : Band $a $b :=
      certified (g := $g) (gridPts% $a $b $g) (samplePts% $a $b $g)
        (by decide +kernel) (by decide +kernel) (by decide +kernel))

row b00 512 544 17
row b01 545 681 11
row b02 682 852 13
row b03 853 959 19
row b04 960 1080 17
row b05 1081 1216 21
row b06 1217 1293 17
row b07 1294 1374 33
row b08 1375 1718 23
row b09 1719 2148 21
row b10 2149 2686 25
row b11 2687 3358 27
row b12 3359 5038 29
row b13 5039 7558 31
row b14 7559 11338 35
row b15 11339 17008 43
row b16 17009 25513 53
row b17 25514 38271 71
row b18 38272 57408 59
row b19 57409 86113 71
row b20 86114 129171 89
row b21 129172 193758 119
row b22 193759 290638 131
row b23 290639 400000 149

/-- On this finite range the least prime `p ≥ k` has enough primes in `(p,2p]`
to pay for its distance beyond `k+1`. -/
theorem medium_prime_density {k : ℕ} (hk : 512 ≤ k) (hK : k ≤ 400000) :
    ∃ p : ℕ, p.Prime ∧ k ≤ p ∧ (∀ r : ℕ, r.Prime → k ≤ r → p ≤ r) ∧
      4*p*(p-(k+1)) < ((Finset.Ioc p (2*p)).filter Nat.Prime).card*(k+1) := by
  apply (show Band 512 400000 from ?_) k hk hK
  refine join b00 ?_
  refine join b01 ?_
  refine join b02 ?_
  refine join b03 ?_
  refine join b04 ?_
  refine join b05 ?_
  refine join b06 ?_
  refine join b07 ?_
  refine join b08 ?_
  refine join b09 ?_
  refine join b10 ?_
  refine join b11 ?_
  refine join b12 ?_
  refine join b13 ?_
  refine join b14 ?_
  refine join b15 ?_
  refine join b16 ?_
  refine join b17 ?_
  refine join b18 ?_
  refine join b19 ?_
  refine join b20 ?_
  refine join b21 ?_
  refine join b22 ?_
  exact b23

end DivisorAdj
