# Open Problems in Lean 4

[![Lean CI](https://github.com/levzzz5154/open-problems-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/levzzz5154/open-problems-lean/actions/workflows/ci.yml)

Machine-checked Lean 4 / Mathlib (`v4.19.0`) proofs and counterexamples for open conjectures from Ermelinda DeLaViña's [*Written on the Wall II*](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html) (Graffiti.pc) catalog and the [OEIS](https://oeis.org/).

All proofs were generated with **GPT 6.2 Astra** in OMP and audited for formal soundness and prior literature/repository overlap as of **November 27, 2026**.

- **113 Lean modules, 1,977 theorems**, zero `sorry`, zero `admit`, zero custom `axiom`, zero `native_decide`.
- Every theorem depends solely on Lean's standard axioms: `[propext, Classical.choice, Quot.sound]`.
- Already-solved problems from the same run (including overlap with 2026 preprints/PRs by Jonas J. Gebendorfer, Evan Dash Rust, `pablodrake`, Howe et al., Kenta Kitamura, `siddhantdubey`, and `graffiti-verification`) have been pruned out, except for 9 modules kept strictly as shared-definition dependencies (listed below).

---

## Summary of Open Problems Resolved

### 1. *Written on the Wall II* (Graffiti.pc) — 17 open catalog conjectures (16 proved, 1 disproved)

| WoW II | Result | Main Theorem(s) | File | Notes |
|---|---|---|---|---|
| **76** | **Disproved** | `Graffiti.Wall76.counterexample76`, `unbounded76` | [Graffiti76.lean](Graffiti76.lean) | 343-vertex connected counterexample + unbounded deficit family |
| **232** | **Proved** | `Graffiti.graffiti232` | [Graffiti232.lean](Graffiti232.lean) | All connected graphs $n \ge 2$ (`radius_periphery_budget` strengthens odd $\gamma_t$) |
| **235** | **Proved** | `Graffiti.graffiti235` | [Graffiti235.lean](Graffiti235.lean) | All connected graphs $n \ge 2$ |
| **241** | **Proved** | `Graffiti.graffiti241` | [Graffiti241.lean](Graffiti241.lean) | Trees $n \ge 2$ (`closed_components_lt_total_set` holds unconditionally) |
| **258** | **Proved** | `Graffiti.graffiti258` | [Graffiti258.lean](Graffiti258.lean) | Connected $n \ge 2$ (`evenMax_add_two` gives stronger additive bound) |
| **259–261** | **Proved** | `Graffiti.graffiti259`, `graffiti260`, `graffiti261` | [Graffiti259to261.lean](Graffiti259to261.lean) | Connected $n \ge 2$; unified via `external_product_of_three_leaves` |
| **342** | **Proved** | `Graffiti.graffiti342` | [Graffiti342.lean](Graffiti342.lean) | Trees $n > 2$, complement annihilation number $A(\overline{T})$ (also reproves closed row `332` as a lemma) |
| **343** | **Proved** | `Graffiti.graffiti343` | [Graffiti343.lean](Graffiti343.lean) | Trees $n > 2$; drops the catalog's nonempty-$D_2$ assumption |
| **344** | **Proved** | `Graffiti.graffiti344` | [Graffiti344.lean](Graffiti344.lean) | Trees $n > 2$, additive form avoiding `Nat` subtraction |
| **356** | **Proved** | `Graffiti.graffiti356` | [Graffiti356.lean](Graffiti356.lean) | Trees $n > 2$, via stronger radius bound `center_leafDistance_sum_le_radius` |
| **377** | **Proved** | `Graffiti.graffiti377` | [Graffiti377.lean](Graffiti377.lean) | Trees $n > 2$, exact Def. 68 upper degree median |
| **434a** | **Proved** | `Graffiti.conjecture434a` | [Graffiti434.lean](Graffiti434.lean) | Connected $n > 3$, exact Def. 119 degeneracy $SW(\overline{G})$ |
| **434b** | **Proved** | `Graffiti.conjecture434b` | [Graffiti434.lean](Graffiti434.lean) | Connected $n > 3$; proves both clauses without $\operatorname{diam} > 2$ or $+1$ |
| **434d** | **Proved** | `Graffiti.conjecture434d` | [Graffiti434d.lean](Graffiti434d.lean) | Connected $n > 3$; generalized to arbitrary distance-4 packings |
| **434e** | **Proved** | `Graffiti.conjecture434e` | [Graffiti434e.lean](Graffiti434e.lean) | DeLaViña–Pepper–Waller (2011) Conjecture 3.2; drops $n > 3$ |

---

### 2. Open Follow-Up & Sharpness Questions on *Written on the Wall II* — 5 theorems

These resolve open follow-up questions on catalog conjectures whose unrestricted statements were previously disproved:

| Target | Theorem(s) | File | What It Resolves |
|---|---|---|---|
| **363 (sharp constant)** | `Graffiti.sharp_peripheral_coefficient`, `third_deficit_unbounded` | [Graffiti363Sharp.lean](Graffiti363Sharp.lean) | Proves the largest valid coefficient in $\gamma_t \ge i(S) + c \cdot \overline{d}(\cdot, B)$ is **$c = 3/10$** (holding for all connected $n \ge 2$) and the deficit is unbounded for every $c > 3/10$ (including $1/3$), settling the open questions from Gebendorfer's `formal-conjectures#7360`. |
| **368 (minimum order)** | `Graffiti.FirstZero.least_counterexample_368`, `least_counterexample_369` | [Graffiti368.lean](Graffiti368.lean) | Proves minimum counterexample order is **29** for `368` (answering DeLaViña–Larson–Pepper–Waller 2009, p. 13) and formally certifies 29 for `369` (matching `adamben04`'s witness in `formal-conjectures#8319`). |
| **369 (tie domain)** | `Graffiti.FirstZero.graffiti369_on_ties` | [Graffiti369Ties.lean](Graffiti369Ties.lean) | Proves `369` is **true** for all trees $n > 2$ with tied modal degrees (`|modes| ≥ 2`), the literal domain specified in UHD Definition 45. |
| **422a (cutoff sharpness)** | `Graffiti.FourMaximum.counterexample422a` | [Graffiti422a.lean](Graffiti422a.lean) | Proves DPW (2011) Theorem 2.5 ($\le 3$ independent max-degree vertices) is sharp: fails at **4** independent max-degree vertices (order 26). |
| **422c (cutoff sharpness)** | `Graffiti.FiveHeavy.five_heavy_counterexample` | [Graffiti422c.lean](Graffiti422c.lean) | Proves DPW (2011) Theorem 2.10 ($\le 4$ heavy vertices) is sharp: fails at **5** heavy vertices (order 275; earlier disproof used 8). |

---

### 3. OEIS Open Conjectures — 4 sequence families

| OEIS | Result | Main Theorem(s) | Files | Notes & Prior Work |
|---|---|---|---|---|
| **[A397185](https://oeis.org/A397185)** | **Proved** | `EvenCover.sequence_succ`, `even_recurrence`, `scaled_exact`, `four_corrections`, `normalized_limit`, `arbitrarily_large_noncovering_prime` | [EvenCover/](EvenCover/) | Proves exact bit pattern for all $n \ge 1$, OEIS even-index recurrence $a(2k) = 2a(2k-1)+1$, 4-step recurrence & $\frac{19}{30} 2^n$ limit asked in OSF `10.17605/osf.io/tq45x`, and disproves modular-class prime coverage. |
| **[A398589](https://oeis.org/A398589) / [A399709](https://oeis.org/A399709)** | **Proved** | `SelfBanning.not_purely_periodic`, `pure_iff`, `square_dvd_period`, `row_le_four_mul` | [SelfBanning.lean](SelfBanning.lean), [SelfBanning/](SelfBanning/) | Proves the open positive-preperiod conjecture (`pure_iff`: purely periodic iff $k \le 2$; cf. `trureturing#16079`), plus linear bound $a(t) \le 4k$ and $(k+1)^2 \mid T$ for every eventual period $T$. *(Note: eventual periodicity itself was previously proved in `trureturing#11864`; A398589 was later withdrawn/recycled on OEIS while A399709 continues the same family.)* |
| **[A353890](https://oeis.org/A353890)** | **Disproved & characterized** | `PowerDifferences.greatest_prime_factor_counterexample`, `PowerPeriods.leastPeriod_eq_radical`, `leastPeriod_twenty`, `leastPeriod_twenty_nine`, `greatest_prime_factor_twenty_nine`, `odd_jacobsthal_factors` | [PrimeFactor.lean](PrimeFactor.lean), [PeriodPrimes.lean](PeriodPrimes.lean), [Period20.lean](Period20.lean), [Period29.lean](Period29.lean), [JacobsthalPrimes.lean](JacobsthalPrimes.lean) | Refutes both OEIS greatest-prime-factor predictions at prime $n = 29$, proves exact squarefree active-prime characterization of the least period, and certifies $a(20)$, $a(29)$, and true gpf $108050869$. *(Periodicity in [PowerPeriods.lean](PowerPeriods.lean) follows Bodin–Dèbes–Najib 2020, Prop. 3.2.)* |
| **[A251758](https://oeis.org/A251758)** | **Proved** *(see Dusart note)* | `DivisorAdj.wilson_primorial_through_400000`, `wilson_primorial_of_dusart`, `wilson_blocks`, `first_through_150`, `first_114`, `wilson_first_eight` | [DivisorAdj/](DivisorAdj/) | Resolves Robert G. Wilson v's general consecutive-primorial assertion: **unconditional** for all $1 \le k \le 400{,}000$ and arbitrarily long prime-neighborhood blocks, and unrestricted for all $k \ge 1$ given the explicit hypothesis `Dusart66` (Pierre Dusart's published unconditional 2010 theorem, [`arXiv:1002.0442`](https://arxiv.org/abs/1002.0442), Thm. 6.9 eq. (6.6)). Also certifies unconditional exact first occurrences for $1 \le k \le 150$ and records up to 69 digits (`first_114`). *(Note: [FirstEight.lean](DivisorAdj/FirstEight.lean) independently certifies $k = 8$, which was also formalized in Lean in `pablodrake/oeis-a251758` / `formal-conjectures#8297` on Nov 25, 2026.)* |

---

## Shared Definitions & Transitive Dependencies (Not Counted Above)

The following 9 top-level `Graffiti*.lean` modules are **already solved in prior work** and are **not** counted among the open problems resolved by this repository; they are kept solely because the open-problem proofs above import shared definitions (`TotallyDominates`, `independentDominationNumber`, `isolatedSupports`, `supportVertices`, `degreeClass`, `distanceToVertices`, `firstZeroStep`, etc.) from them:

- [Graffiti169.lean](Graffiti169.lean), [Graffiti315.lean](Graffiti315.lean), [Graffiti362.lean](Graffiti362.lean), [Graffiti363.lean](Graffiti363.lean), [Graffiti365.lean](Graffiti365.lean) — prior proofs/disproofs by Jonas J. Gebendorfer (2026).
- [Graffiti369.lean](Graffiti369.lean) — prior 29-vertex witness by `adamben04` (`formal-conjectures#8319`); provides `degrees`, `modes`, `firstZeroStep`, and the witness tree used by `Graffiti368.lean` / `Graffiti369Ties.lean`.
- [Graffiti416.lean](Graffiti416.lean) — prior Lean proof by Evan Dash Rust (`Conjecture-Killers`).
- [Graffiti426.lean](Graffiti426.lean), [Graffiti450.lean](Graffiti450.lean) — prior proofs in the WoW / West dossier (`siddhantdubey`).

---

## Verification

Requires [elan](https://github.com/leanprover/elan) (`leanprover/lean4:v4.19.0`, pinned in [lean-toolchain](lean-toolchain)).

```bash
lake exe cache get
lake build
./scripts/check_axioms.sh
```

`scripts/check_axioms.sh` scans all `.lean` files for forbidden tokens (`sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`) and runs a Lean metaprogramming check over every theorem in all 113 local modules verifying that only `[propext, Classical.choice, Quot.sound]` appear.
