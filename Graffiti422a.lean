import Graffiti.CliqueFiber

/-! # Four independent maximum-degree vertices suffice to break 422a

Theorem 2.5 of DeLaViña–Pepper–Waller proves the bound when there are at
most three independent maximum-degree vertices. The unrestricted conjecture
already has a counterexample family (Graffiti verification catalogue, §7bd);
the point here is sharpness of the cutoff, not minimality of the order.

* https://www.uhd.edu/documents/academics/sciences/dpw-cn2011.pdf
* https://graffiti-verification-ae088f.gitlab.io/README.md
-/

namespace Graffiti.FourMaximum

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
open CliqueFiber

abbrev Color := Fin 14

/-- `2*a+b` denotes the high vertex `m_ab`, `4+j` the neutral `z_j`,
    and `6+4*j+2*e+t` a clique of size `2+t` on side `e` of module `j`. -/
def weight (x : Color) : ℕ := if x.val < 6 then 1 else 2 + (x.val - 6) % 2

def highs : Finset Color := {0, 1, 2, 3}

/-- Test adjacency of two colors in increasing order. Distinct sides of one
module are joined, not distinct kinds on the same side. -/
private def upper (x y : ℕ) : Bool :=
  if y < 6 then false else
  let u := y - 6
  let j := u / 4
  let e := u / 2 % 2
  if x < 4 then e != (if j == 0 then x / 2 else x % 2)
  else if x < 6 then (x - 4 == j) && (u % 2 == 0)
  else ((x - 6) / 4 == j) && ((x - 6) / 2 % 2 != e)

private def edge (x y : Color) : Bool :=
  if x ≤ y then upper x.val y.val else upper y.val x.val

def quotient : SimpleGraph Color where
  Adj x y := edge x y = true
  symm := by
    have h : ∀ x y : Color, edge x y = edge y x := by decide
    intro x y hxy
    exact (h y x).trans hxy
  loopless := by
    have h : ∀ x : Color, edge x x ≠ true := by decide
    exact h

instance : DecidableRel quotient.Adj := fun x y => inferInstanceAs (Decidable (edge x y = true))

/-- The finite certificate checks the independent sets on the fourteen colors.
Combinatorially, an independent set uses at most two low vertices per module.
For an independent dominating set, let `r` count modules with a selected
side vertex. Those modules fix one bit each, leaving exactly `2^(2-r)` highs
without a selected neighbor; all must be selected. Each such module needs
at least two low vertices: the selected highs cannot dominate its selected
side, so either both kinds are represented, or the neutral covers the small
kind. Every other module needs its neutral. Thus the total is at least
`2^(2-r) + 2*r + (2-r)`, at least five for `r = 0, 1, 2`. -/
private theorem certificate : Certificate quotient weight highs 4 5 4 26 where
  positive := by decide
  order_eq := by decide
  hubs_eq := by decide
  singleton_hubs := by decide
  indep_hubs := by decide
  seen := ⟨0, 3, by decide⟩
  checked := ⟨List.finRange 14, by decide, by decide⟩

/-- A connected graph of order 26 with four independent maximum-degree
vertices, independence number at most four off those vertices, and independent
domination number at least five. -/
theorem counterexample422a :
    Witness (liftGraph quotient weight) (maxVertices (liftGraph quotient weight)) 4 5 4 26 := by
  have hmax := fibers_eq_max quotient weight highs certificate.positive
    (show highs.Nonempty from ⟨0, by decide⟩) 11 (by decide)
  rw [← hmax]
  exact realize quotient weight highs 4 5 4 26 certificate

end Graffiti.FourMaximum
