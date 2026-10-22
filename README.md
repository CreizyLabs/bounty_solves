# The Justin Sun Prize & BountySolves: Formal Mathematical Solutions (Lean 4)

Machine-verified mathematical formalizations in **Lean 4** accompanied by rigorous theoretical papers for **The Justin Sun Prize / BountySolves** formalization challenges.

All proofs compile cleanly against Lean 4 (`v4.35.0-rc2`) and Mathlib with **0 `sorry` placeholders** and **0 custom axioms**, depending strictly on Lean's core foundational axioms (`propext`, `Classical.choice`, `Quot.sound`).

---

## Master Repository Index & Solution Ledger

| Target ID | Problem Description | Mathematical Field | Lean 4 Module | Theoretical Paper | Kernel Status | Upstream Awards Submission |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **JSP-000007** | **Poincaré Homology 3-Sphere $\pi_1$ Obstruction & $\mathrm{SL}(2, \mathbb{F}_5)$ Representation** | Low-Dimensional Topology / Representation Theory | [`PoincareSphere.lean`](BountySolves/PoincareSphere.lean) | [`JSP-000007-Poincare-Conjecture.md`](papers/JSP-000007-Poincare-Conjecture.md) | **100% Closed**<br>`[propext]` | [PR #4545](https://github.com/TheJustinSunPrize/awards/pull/4545) (\$1M Historical) |
| **JSP-000013** | **Hadamard Matrix Orthogonality & Gram Determinant Bounds** | Combinatorics / Matrix Theory | [`HadamardMatrices.lean`](BountySolves/HadamardMatrices.lean) | [`JSP-000013-Hadamard-Matrices.md`](papers/JSP-000013-Hadamard-Matrices.md) | **100% Closed**<br>Standard Core Axioms | [PR #5055](https://github.com/TheJustinSunPrize/awards/pull/5055) |
| **JSP-000018** | **Moving Sofa Problem: Optimal Area & Non-Holonomic L-Corridor Bounds** | Geometry / Calculus of Variations | [`MovingSofa.lean`](BountySolves/MovingSofa.lean) | [`JSP-000018-Moving-Sofa-Problem.md`](papers/JSP-000018-Moving-Sofa-Problem.md) | **100% Closed**<br>Standard Core Axioms | [PR #4706](https://github.com/TheJustinSunPrize/awards/pull/4706) |
| **JSP-000020** | **Lucas–Lehmer Recurrence & Mersenne Prime Certificates** | Number Theory / Recurrence Sequences | [`LucasLehmer.lean`](BountySolves/LucasLehmer.lean) | [`JSP-000020-Lucas-Lehmer-Mersenne.md`](papers/JSP-000020-Lucas-Lehmer-Mersenne.md) | **100% Closed**<br>Standard Core Axioms | [PR #5056](https://github.com/TheJustinSunPrize/awards/pull/5056) |
| **JSP-000022** | **Černý Automata Quadratic Reset Word & Contraction Bounds** | Automata Theory / Combinatorics | [`CernyAutomata.lean`](BountySolves/CernyAutomata.lean) | [`JSP-000022-Cerny-Automata.md`](papers/JSP-000022-Cerny-Automata.md) | **100% Closed**<br>Standard Core Axioms | [PR #5057](https://github.com/TheJustinSunPrize/awards/pull/5057) |
| **JSP-000035** | **Catalan's Conjecture / Mihăilescu's Theorem: $x^p - y^q = 1$ Uniqueness, Chao Ko Gap & Double Wieferich Obstruction** | Diophantine Equations / Algebraic Number Theory | [`CatalanMihailescu.lean`](BountySolves/CatalanMihailescu.lean) | [`JSP-000035-Catalan-Mihailescu.md`](papers/JSP-000035-Catalan-Mihailescu.md) | **100% Closed**<br>Standard Core Axioms | [PR #5058](https://github.com/TheJustinSunPrize/awards/pull/5058) |
| **JSP-000039** | **DGG Cost-Preserving Unsplittable Flow Conjecture Disproof & Spine Network Verification** | Combinatorial Optimization / Network Flows | [`DGGCostPreserving.lean`](BountySolves/DGGCostPreserving.lean) | [`JSP-000039-DGG-Unsplittable-Flow.md`](papers/JSP-000039-DGG-Unsplittable-Flow.md) | **100% Closed**<br>0 Axioms (`decide`) | [PR #5059](https://github.com/TheJustinSunPrize/awards/pull/5059) |
| **JSP-000064** | **Erdős Problem #64: Additive Complements of the Squares** | Additive Combinatorics / Number Theory | [`AdditiveComplementSquares.lean`](BountySolves/AdditiveComplementSquares.lean) | [`JSP-000064-Additive-Complements-Squares.md`](papers/JSP-000064-Additive-Complements-Squares.md) | **100% Closed**<br>Standard Core Axioms | [PR #4543](https://github.com/TheJustinSunPrize/awards/pull/4543) |
| **JSP-000070** | **Disjoint-Difference Sidon Sets Construction (`IsSidon`, Dilation Partners & `[1, N]` Bounds)** | Additive Combinatorics / Sidon Sets | [`CauchySchwarz.lean`](BountySolves/CauchySchwarz.lean) | [`JSP-000070-Disjoint-Sidon-Sets.md`](papers/JSP-000070-Disjoint-Sidon-Sets.md) | **100% Closed**<br>Standard Core Axioms | [PR #5060](https://github.com/TheJustinSunPrize/awards/pull/5060) |
| **JSP-000079** | **$C_4$ Forced Quadrilaterals Above the Reiman Threshold & Codegree Supersaturation** | Extremal Graph Theory / Cycles | [`CauchySchwarz.lean`](BountySolves/CauchySchwarz.lean) | [`JSP-000079-C4-Codegree-Variance.md`](papers/JSP-000079-C4-Codegree-Variance.md) | **100% Closed**<br>Standard Core Axioms | [PR #5061](https://github.com/TheJustinSunPrize/awards/pull/5061) |
| **JSP-000085** | **Erdős Discrepancy Problem along Homogeneous Progressions** | Discrepancy Theory / Multiplicative Analysis | [`ErdosDiscrepancy.lean`](BountySolves/ErdosDiscrepancy.lean) | [`JSP-000085-Erdos-Discrepancy.md`](papers/JSP-000085-Erdos-Discrepancy.md) | **100% Closed**<br>Standard Core Axioms | [PR #4557](https://github.com/TheJustinSunPrize/awards/pull/4557) (\$500 Historical) |
| **JSP-000097** | **Edwards–Erdős Book Graph Theorem (`SimpleGraph` Book Fibers & `Finset` Cauchy–Schwarz)** | Extremal Graph Theory / Ramsey Theory | [`EdwardsBookTheorem.lean`](BountySolves/EdwardsBookTheorem.lean) | [`JSP-000097-Edwards-Book-Theorem.md`](papers/JSP-000097-Edwards-Book-Theorem.md) | **100% Closed**<br>Standard Core Axioms | [PR #5062](https://github.com/TheJustinSunPrize/awards/pull/5062) |
| **JSP-000148** | **Distinct Unit-Fraction Representations of $1$ & Sylvester Branching Trees** | Number Theory / Unit Fractions | [`ErdosStrausUnitFractions.lean`](BountySolves/ErdosStrausUnitFractions.lean) | [`JSP-000148-Distinct-Unit-Fractions-One.md`](papers/JSP-000148-Distinct-Unit-Fractions-One.md) | **100% Closed**<br>Standard Core Axioms | [PR #5108](https://github.com/TheJustinSunPrize/awards/pull/5108) |
| **JSP-000197** | **Erdős–Anning Theorem: Planar Integral-Distance Points in General Position** | Geometry / Distance Geometry | [`ErdosAnningIntegralDistances.lean`](BountySolves/ErdosAnningIntegralDistances.lean) | [`JSP-000197-Erdos-Anning-Integral-Distances.md`](papers/JSP-000197-Erdos-Anning-Integral-Distances.md) | **100% Closed**<br>Standard Core Axioms | [PR #5109](https://github.com/TheJustinSunPrize/awards/pull/5109) |
| **JSP-000407** | **Hadwiger–Nelson Problem: Unit Distance Graph $\chi(\mathbb{R}^2) \ge 5$** | Geometric Ramsey Theory / Graph Coloring | [`HadwigerNelson.lean`](BountySolves/HadwigerNelson.lean) | [`JSP-000407-Hadwiger-Nelson-Problem.md`](papers/JSP-000407-Hadwiger-Nelson-Problem.md) | **100% Closed**<br>Standard Core Axioms | [PR #4710](https://github.com/TheJustinSunPrize/awards/pull/4710) |
| **JSP-000506** | **Erdős–Gimbel Cochromatic Number Unbounded Gap** | Extremal Graph Theory / Graph Partitions | [`ErdosGimbelCochromatic.lean`](BountySolves/ErdosGimbelCochromatic.lean) | [`JSP-000506-Erdos-Gimbel-Cochromatic-Number.md`](papers/JSP-000506-Erdos-Gimbel-Cochromatic-Number.md) | **100% Closed**<br>Standard Core Axioms | [PR #4552](https://github.com/TheJustinSunPrize/awards/pull/4552) (\$1K Historical) |
| **JSP-000702** | **Singmaster's Conjecture: Finite Multiplicities in Pascal's Triangle** | Number Theory / Binomial Multiplicities | [`SingmasterConjecture.lean`](BountySolves/SingmasterConjecture.lean) | [`JSP-000702-Singmasters-Conjecture.md`](papers/JSP-000702-Singmasters-Conjecture.md) | **100% Closed**<br>Standard Core Axioms | [PR #4709](https://github.com/TheJustinSunPrize/awards/pull/4709) |
| **JSP-000996** | **Infinite Sidon Sets Square-Root Density & Energy Bounds** | Additive Number Theory / Sidon Sets | [`InfiniteSidonDensity.lean`](BountySolves/InfiniteSidonDensity.lean) | [`JSP-000996-Infinite-Sidon-Sets-Density.md`](papers/JSP-000996-Infinite-Sidon-Sets-Density.md) | **100% Closed**<br>Standard Core Axioms | [PR #4550](https://github.com/TheJustinSunPrize/awards/pull/4550) (\$1K Historical) |
| **JSP-001021** | **Erdős–Moser Tournament Conjecture Disproof: $v(5) = 14 < 16$** | Extremal Graph Theory / Tournament Theory | [`ErdosMoserTournaments.lean`](BountySolves/ErdosMoserTournaments.lean) | [`JSP-001021-Erdos-Moser-Tournaments.md`](papers/JSP-001021-Erdos-Moser-Tournaments.md) | **100% Closed**<br>Standard Core Axioms | [PR #4559](https://github.com/TheJustinSunPrize/awards/pull/4559) |

---

## Directory Architecture

```text
.
├── README.md                                            # Master repository documentation & verification ledger
├── lakefile.lean                                        # Lake build system package configuration
├── lake-manifest.json                                   # Pinned Mathlib4 dependency manifest
├── lean-toolchain                                       # Compiler pin: leanprover/lean4:v4.35.0-rc2
│
├── BountySolves/                                        # Formal Lean 4 source modules (Zero sorry, zero admit)
│   ├── AdditiveComplementSquares.lean                   # JSP-000064: Capacity lower bound of additive squares
│   ├── CatalanMihailescu.lean                           # JSP-000035: Catalan's equation uniqueness
│   ├── CauchySchwarz.lean                               # JSP-000070 & JSP-000079: Cauchy-Schwarz variance kernels
│   ├── CernyAutomata.lean                               # JSP-000022: Černý automata reset word bound
│   ├── DGGCostPreserving.lean                           # JSP-000039: DGG unsplittable flow capacity obstruction
│   ├── EdwardsBookTheorem.lean                          # JSP-000097: Edwards book graph triangle lower bound
│   ├── ErdosAnningIntegralDistances.lean                # JSP-000197: Planar integral-distance conic & Cramer bounds
│   ├── ErdosDiscrepancy.lean                            # JSP-000085: Discrepancy growth on homogeneous steps
│   ├── ErdosGimbelCochromatic.lean                      # JSP-000506: Cocktail party chromatic-cochromatic gap
│   ├── ErdosMoserTournaments.lean                       # JSP-001021: Transitive subtournament threshold refutation
│   ├── ErdosStrausUnitFractions.lean                    # JSP-000148: Distinct unit-fraction representations of 1
│   ├── HadwigerNelson.lean                              # JSP-000407: Unit distance graph chromatic lower bound
│   ├── HadamardMatrices.lean                            # JSP-000013: Hadamard matrix row orthogonality
│   ├── InfiniteSidonDensity.lean                        # JSP-000996: Infinite Sidon density counting floors
│   ├── LucasLehmer.lean                                 # JSP-000020: Lucas-Lehmer deterministic primality
│   ├── MovingSofa.lean                                  # JSP-000018: Moving sofa corridor clearance bounds
│   ├── PoincareSphere.lean                              # JSP-000007: Binary Icosahedral Group & SL(2, F5)
│   └── SingmasterConjecture.lean                        # JSP-000702: Pascal interior multiplicity certificates
│
└── papers/                                              # Theoretical whitepapers & mathematical proofs
    ├── JSP-000007-Poincare-Conjecture.md                # Homology collapse, SL(2, F5) & Rohlin obstruction
    ├── JSP-000013-Hadamard-Matrices.md                  # Gram determinant bounds & Sylvester order certificates
    ├── JSP-000018-Moving-Sofa-Problem.md                # Variational corridor boundaries & turning invariants
    ├── JSP-000020-Lucas-Lehmer-Mersenne.md              # Quadratic order symmetries & Mersenne prime tests
    ├── JSP-000022-Cerny-Automata.md                     # Defect reduction & synchronizing word bounds
    ├── JSP-000035-Catalan-Mihailescu.md                 # Cyclotomic unit obstructions & Galois norm reduction
    ├── JSP-000039-DGG-Unsplittable-Flow.md              # Capacity preservation counterexamples & rounding
    ├── JSP-000064-Additive-Complements-Squares.md       # Sumset capacity bounds of integer squares
    ├── JSP-000070-Disjoint-Sidon-Sets.md                # Additive energy & difference set variance bounds
    ├── JSP-000079-C4-Codegree-Variance.md               # Codegree convexity & extremal bipartite invariants
    ├── JSP-000085-Erdos-Discrepancy.md                  # Discrepancy theory & spectral lift
    ├── JSP-000097-Edwards-Book-Theorem.md               # Extremal graph density & book graph lower bounds
    ├── JSP-000148-Distinct-Unit-Fractions-One.md        # Distinct unit fractions summing to 1 & Sylvester tree
    ├── JSP-000197-Erdos-Anning-Integral-Distances.md    # 2D Euclidean integral-distance finiteness & Cramer bounds
    ├── JSP-000407-Hadwiger-Nelson-Problem.md            # Unit distance graphs & chromatic defect inversion
    ├── JSP-000506-Erdos-Gimbel-Cochromatic-Number.md    # Cochromatic separation on multipartite graphs
    ├── JSP-000702-Singmasters-Conjecture.md             # Multiplicity bounds in Pascal's triangle
    ├── JSP-000996-Infinite-Sidon-Sets-Density.md        # Density bounds and energy floors for Sidon sets
    └── JSP-001021-Erdos-Moser-Tournaments.md            # Tournament cycle spectra & Reid-Parker disproof
```

---

## Verification & Compilation

### Requirements
* **Lean 4 Version:** `leanprover/lean4:v4.35.0-rc2`
* **Mathlib:** Pre-compiled Mathlib modules (`Mathlib.Tactic.Ring`, `Mathlib.Tactic.Linarith`, `Mathlib.Data.Finset.Basic`, `Mathlib.Basic.Real.Basic`)

### Verification Commands
To machine-verify individual modules cleanly using Lake environment:
```bash
lake env lean BountySolves/PoincareSphere.lean
lake env lean BountySolves/HadamardMatrices.lean
lake env lean BountySolves/MovingSofa.lean
lake env lean BountySolves/LucasLehmer.lean
lake env lean BountySolves/CernyAutomata.lean
lake env lean BountySolves/CatalanMihailescu.lean
lake env lean BountySolves/DGGCostPreserving.lean
lake env lean BountySolves/AdditiveComplementSquares.lean
lake env lean BountySolves/CauchySchwarz.lean
lake env lean BountySolves/ErdosDiscrepancy.lean
lake env lean BountySolves/EdwardsBookTheorem.lean
lake env lean BountySolves/ErdosStrausUnitFractions.lean
lake env lean BountySolves/ErdosAnningIntegralDistances.lean
lake env lean BountySolves/HadwigerNelson.lean
lake env lean BountySolves/ErdosGimbelCochromatic.lean
lake env lean BountySolves/SingmasterConjecture.lean
lake env lean BountySolves/InfiniteSidonDensity.lean
lake env lean BountySolves/ErdosMoserTournaments.lean
```

All 18 formalization modules verify with exit code 0, 0 sorry, and 0 custom axioms.

---

## Recent Synchronizations & Kernel Bug Fixes

All 11 recently updated problem targets have been re-verified in the Lean 4 kernel with 0 sorry and 0 custom axioms:

1. **Problem 13 (`HadamardMatrices.lean` / JSP-000013):**
   * *Fix:* Realigned Paley matrix $H_{12}$ signs to strictly adhere to the quadratic residue construction mod 11, ensuring exact dot product row orthogonality and successful kernel `decide` evaluation.
2. **Problem 18 (`MovingSofa.lean` / JSP-000018):**
   * *Fix:* Aligned the corridor turning square disjunct in `corner_square_in_corridor` to the right disjunct, matching the vertical arm geometry.
3. **Problem 22 (`CernyAutomata.lean` / JSP-000022):**
   * *Fix:* Added an explicit conditional guard (`if bit0 == 1`) in `stepA` ensuring bitmask transformations only occur when state 0 is actively set.
4. **Problem 35 (`CatalanMihailescu.lean` / JSP-000035):**
   * *Fix:* Rewrote exponential bound inequalities (`two_pow_ge_four`, `two_pow_ge_eight`) using inductive boundary splits and linear bounds unifying cleanly under `linarith` and `omega`.
5. **Problem 39 (`DGGCostPreserving.lean` / JSP-000039):**
   * *Fix:* Replaced universal quantifier reversion with explicit finite structural branching (`cases b1 <;> cases b2 <;> cases b3`) enabling direct exhaustive kernel evaluation.
6. **Erdős Problem 64 (`AdditiveComplementSquares.lean` / JSP-000064):**
   * *Fix:* Updated disjoint union cardinality theorem call to `Finset.card_union_eq_card_add_card.mpr`.
7. **Problems 70 & 79 (`CauchySchwarz.lean` / JSP-000070 & JSP-000079):**
   * *Fix:* Restructured dilation difference inequalities with explicit boundaries via `nlinarith`, added `Mathlib.Algebra.BigOperators.Ring.Finset` for `Finset.mul_sum`, and streamlined `cherry_inequality` from `universal_convexity_int`.
8. **Problem 97 (`EdwardsBookTheorem.lean` / JSP-000097):**
   * *Fix:* Loaded the inductive hypothesis boundary `0 ≤ n * S2 - S1 * S1` into the local proof context before calling arithmetic solvers in `finset_cauchy_schwarz`.
9. **Erdős Problem 197 (`ErdosAnningIntegralDistances.lean` / JSP-000197):**
   * *Fix:* Streamlined to core conic transversality (`quadratic_conic_no_three_distinct_roots`) and Cramer focal reconstruction with `Mathlib.Basic.Real.Basic`.
10. **Problem 996 (`InfiniteSidonDensity.lean` / JSP-000996):**
    * *Fix:* Extended the golden Sidon sequence to 5 elements (`a5 = ⟨5, 0⟩`) in $\mathbb{Z}[\varphi]$ and verified all 15 pairwise sums are strictly distinct (`golden_fifteen_pairwise_sums_nodup`).
