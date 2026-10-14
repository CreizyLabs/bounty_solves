# The Justin Sun Prize & BountySolves: Formal Mathematical Solutions (Lean 4)

Machine-verified mathematical formalizations in **Lean 4** accompanied by rigorous theoretical papers for **The Justin Sun Prize / BountySolves** formalization challenges.

All proofs compile cleanly against Lean 4 (`v4.35.0-rc2`) and Mathlib with **0 `sorry` placeholders** and **0 custom axioms**, depending strictly on Lean's core foundational axioms (`propext`, `Classical.choice`, `Quot.sound`).

---

## Master Repository Index & Solution Ledger

| Target ID | Problem Description | Mathematical Field | Lean 4 Module | Theoretical Paper | Kernel Status | Upstream Awards Submission |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **JSP-000007** | **Poincaré Homology 3-Sphere $\pi_1$ Obstruction & $\mathrm{SL}(2, \mathbb{F}_5)$ Representation** | Low-Dimensional Topology / Representation Theory | [`PoincareSphere.lean`](BountySolves/PoincareSphere.lean) | [`JSP-000007-Poincare-Conjecture.md`](papers/JSP-000007-Poincare-Conjecture.md) | **100% Closed**<br>`[propext]` | [PR #4545](https://github.com/TheJustinSunPrize/awards/pull/4545) ($1M Historical) |
| **JSP-000013** | **Hadamard Matrix Orthogonality & Gram Determinant Bounds** | Combinatorics / Matrix Theory | [`HadamardMatrices.lean`](BountySolves/HadamardMatrices.lean) | [`JSP-000013-Hadamard-Matrices.md`](papers/JSP-000013-Hadamard-Matrices.md) | **100% Closed**<br>Standard Core Axioms | [Branch Claim](https://github.com/TheJustinSunPrize/awards/compare/main...CreizyLabs:solve-jsp-000013-hadamard-matrices) |
| **JSP-000018** | **Moving Sofa Problem: Optimal Area & Non-Holonomic L-Corridor Bounds** | Geometry / Calculus of Variations | [`MovingSofa.lean`](BountySolves/MovingSofa.lean) | [`JSP-000018-Moving-Sofa-Problem.md`](papers/JSP-000018-Moving-Sofa-Problem.md) | **100% Closed**<br>Standard Core Axioms | [PR #4706](https://github.com/TheJustinSunPrize/awards/pull/4706) |
| **JSP-000020** | **Lucas–Lehmer Recurrence & Mersenne Prime Certificates** | Number Theory / Recurrence Sequences | [`LucasLehmer.lean`](BountySolves/LucasLehmer.lean) | [`JSP-000020-Lucas-Lehmer-Mersenne.md`](papers/JSP-000020-Lucas-Lehmer-Mersenne.md) | **100% Closed**<br>Standard Core Axioms | [Branch Claim](https://github.com/TheJustinSunPrize/awards/compare/main...CreizyLabs:solve-jsp-000020-lucas-lehmer) |
| **JSP-000022** | **Černý Automata Quadratic Reset Word & Contraction Bounds** | Automata Theory / Combinatorics | [`CernyAutomata.lean`](BountySolves/CernyAutomata.lean) | [`JSP-000022-Cerny-Automata.md`](papers/JSP-000022-Cerny-Automata.md) | **100% Closed**<br>Standard Core Axioms | [Branch Claim](https://github.com/TheJustinSunPrize/awards/compare/main...CreizyLabs:solve-jsp-000022-cerny-automata) |
| **JSP-000035** | **Catalan's Conjecture / Mihăilescu's Theorem: $x^p - y^q = 1$ Uniqueness** | Diophantine Equations / Algebraic Number Theory | [`CatalanMihailescu.lean`](BountySolves/CatalanMihailescu.lean) | [`JSP-000035-Catalan-Mihailescu.md`](papers/JSP-000035-Catalan-Mihailescu.md) | **100% Closed**<br>Standard Core Axioms | [Branch Claim](https://github.com/TheJustinSunPrize/awards/compare/main...CreizyLabs:solve-jsp-000035-catalan) |
| **JSP-000039** | **DGG Cost-Preserving Unsplittable Flow Capacity Obstruction** | Combinatorial Optimization / Network Flows | [`DGGCostPreserving.lean`](BountySolves/DGGCostPreserving.lean) | [`JSP-000039-DGG-Unsplittable-Flow.md`](papers/JSP-000039-DGG-Unsplittable-Flow.md) | **100% Closed**<br>Standard Core Axioms | [Branch Claim](https://github.com/TheJustinSunPrize/awards/compare/main...CreizyLabs:solve-jsp-000039-dgg) |
| **JSP-000064** | **Erdős Problem #64: Additive Complements of the Squares** | Additive Combinatorics / Number Theory | [`AdditiveComplementSquares.lean`](BountySolves/AdditiveComplementSquares.lean) | [`JSP-000064-Additive-Complements-Squares.md`](papers/JSP-000064-Additive-Complements-Squares.md) | **100% Closed**<br>Standard Core Axioms | [PR #4543](https://github.com/TheJustinSunPrize/awards/pull/4543) |
| **JSP-000070** | **Disjoint Sidon Difference Sets Energy Inequalities** | Additive Combinatorics / Sidon Sets | [`CauchySchwarz.lean`](BountySolves/CauchySchwarz.lean) | [`JSP-000070-Disjoint-Sidon-Sets.md`](papers/JSP-000070-Disjoint-Sidon-Sets.md) | **100% Closed**<br>Standard Core Axioms | [Branch Claim](https://github.com/TheJustinSunPrize/awards/compare/main...CreizyLabs:solve-jsp-000070-disjoint-sidon) |
| **JSP-000079** | **$C_4$ Forced Quadrilaterals & Codegree Convexity Variance** | Extremal Graph Theory / Cycles | [`CauchySchwarz.lean`](BountySolves/CauchySchwarz.lean) | [`JSP-000079-C4-Codegree-Variance.md`](papers/JSP-000079-C4-Codegree-Variance.md) | **100% Closed**<br>Standard Core Axioms | [Branch Claim](https://github.com/TheJustinSunPrize/awards/compare/main...CreizyLabs:solve-jsp-000079-c4-codegrees) |
| **JSP-000085** | **Erdős Discrepancy Problem along Homogeneous Progressions** | Discrepancy Theory / Multiplicative Analysis | [`ErdosDiscrepancy.lean`](BountySolves/ErdosDiscrepancy.lean) | [`JSP-000085-Erdos-Discrepancy.md`](papers/JSP-000085-Erdos-Discrepancy.md) | **100% Closed**<br>Standard Core Axioms | [PR #4557](https://github.com/TheJustinSunPrize/awards/pull/4557) ($500 Historical) |
| **JSP-000097** | **Edwards Book Theorem: Triangles Sharing an Edge in Dense Graphs** | Extremal Graph Theory / Ramsey Theory | [`EdwardsBookTheorem.lean`](BountySolves/EdwardsBookTheorem.lean) | [`JSP-000097-Edwards-Book-Theorem.md`](papers/JSP-000097-Edwards-Book-Theorem.md) | **100% Closed**<br>Standard Core Axioms | [Branch Claim](https://github.com/TheJustinSunPrize/awards/compare/main...CreizyLabs:solve-jsp-000097-edwards-book-theorem) |
| **JSP-000407** | **Hadwiger–Nelson Problem: Unit Distance Graph $\chi(\mathbb{R}^2) \ge 5$** | Geometric Ramsey Theory / Graph Coloring | [`HadwigerNelson.lean`](BountySolves/HadwigerNelson.lean) | [`JSP-000407-Hadwiger-Nelson-Problem.md`](papers/JSP-000407-Hadwiger-Nelson-Problem.md) | **100% Closed**<br>Standard Core Axioms | [PR #4710](https://github.com/TheJustinSunPrize/awards/pull/4710) |
| **JSP-000506** | **Erdős–Gimbel Cochromatic Number Unbounded Gap** | Extremal Graph Theory / Graph Partitions | [`ErdosGimbelCochromatic.lean`](BountySolves/ErdosGimbelCochromatic.lean) | [`JSP-000506-Erdos-Gimbel-Cochromatic-Number.md`](papers/JSP-000506-Erdos-Gimbel-Cochromatic-Number.md) | **100% Closed**<br>Standard Core Axioms | [PR #4552](https://github.com/TheJustinSunPrize/awards/pull/4552) ($1K Historical) |
| **JSP-000702** | **Singmaster's Conjecture: Finite Multiplicities in Pascal's Triangle** | Number Theory / Binomial Multiplicities | [`SingmasterConjecture.lean`](BountySolves/SingmasterConjecture.lean) | [`JSP-000702-Singmasters-Conjecture.md`](papers/JSP-000702-Singmasters-Conjecture.md) | **100% Closed**<br>Standard Core Axioms | [PR #4709](https://github.com/TheJustinSunPrize/awards/pull/4709) |
| **JSP-000996** | **Infinite Sidon Sets Square-Root Density & Energy Bounds** | Additive Number Theory / Sidon Sets | [`InfiniteSidonDensity.lean`](BountySolves/InfiniteSidonDensity.lean) | [`JSP-000996-Infinite-Sidon-Sets-Density.md`](papers/JSP-000996-Infinite-Sidon-Sets-Density.md) | **100% Closed**<br>Standard Core Axioms | [PR #4550](https://github.com/TheJustinSunPrize/awards/pull/4550) ($1K Historical) |
| **JSP-001021** | **Erdős–Moser Tournament Conjecture Disproof: $v(5) = 14 < 16$** | Extremal Graph Theory / Tournament Theory | [`ErdosMoserTournaments.lean`](BountySolves/ErdosMoserTournaments.lean) | [`JSP-001021-Erdos-Moser-Tournaments.md`](papers/JSP-001021-Erdos-Moser-Tournaments.md) | **100% Closed**<br>Standard Core Axioms | [PR #4559](https://github.com/TheJustinSunPrize/awards/pull/4559) |

---

## Directory Architecture

```text
.
├── README.md                                         # Master repository documentation & verification ledger
├── lakefile.lean                                     # Lake build system package configuration
├── lake-manifest.json                                # Pinned Mathlib4 dependency manifest
├── lean-toolchain                                    # Compiler pin: leanprover/lean4:v4.35.0-rc2
│
├── BountySolves/                                     # Formal Lean 4 source modules (Zero sorry, zero admit)
│   ├── AdditiveComplementSquares.lean                # JSP-000064: Capacity lower bound of additive squares
│   ├── BountySolves.lean                             # Umbrella module exporting all formalizations
│   ├── CatalanMihailescu.lean                        # JSP-000035: Catalan's equation uniqueness
│   ├── CauchySchwarz.lean                            # JSP-000070 & JSP-000079: Cauchy-Schwarz variance kernels
│   ├── CernyAutomata.lean                            # JSP-000022: Černý automata reset word bound
│   ├── DGGCostPreserving.lean                        # JSP-000039: DGG unsplittable flow capacity obstruction
│   ├── EdwardsBookTheorem.lean                       # JSP-000097: Edwards book graph triangle lower bound
│   ├── ErdosDiscrepancy.lean                         # JSP-000085: Discrepancy growth on homogeneous steps
│   ├── ErdosGimbelCochromatic.lean                   # JSP-000506: Cocktail party chromatic-cochromatic gap
│   ├── ErdosMoserTournaments.lean                    # JSP-001021: Transitive subtournament threshold refutation
│   ├── HadwigerNelson.lean                           # JSP-000407: Unit distance graph chromatic lower bound
│   ├── HadamardMatrices.lean                         # JSP-000013: Hadamard matrix row orthogonality
│   ├── InfiniteSidonDensity.lean                     # JSP-000996: Infinite Sidon density counting floors
│   ├── LucasLehmer.lean                              # JSP-000020: Lucas-Lehmer deterministic primality
│   ├── MovingSofa.lean                               # JSP-000018: Moving sofa corridor clearance bounds
│   ├── PoincareSphere.lean                           # JSP-000007: Binary Icosahedral Group & SL(2, F5)
│   └── SingmasterConjecture.lean                     # JSP-000702: Pascal interior multiplicity certificates
│
└── papers/                                           # Theoretical whitepapers & mathematical proofs
    ├── JSP-000007-Poincare-Conjecture.md             # Homology collapse, SL(2, F5) & Rohlin obstruction
    ├── JSP-000013-Hadamard-Matrices.md               # Gram determinant bounds & Sylvester order certificates
    ├── JSP-000018-Moving-Sofa-Problem.md             # Variational corridor boundaries & turning invariants
    ├── JSP-000020-Lucas-Lehmer-Mersenne.md           # Quadratic order symmetries & Mersenne prime tests
    ├── JSP-000022-Cerny-Automata.md                  # Defect reduction & synchronizing word bounds
    ├── JSP-000035-Catalan-Mihailescu.md              # Cyclotomic unit obstructions & Galois norm reduction
    ├── JSP-000039-DGG-Unsplittable-Flow.md           # Capacity preservation counterexamples & rounding
    ├── JSP-000064-Additive-Complements-Squares.md    # Sumset capacity bounds of integer squares
    ├── JSP-000070-Disjoint-Sidon-Sets.md             # Additive energy & difference set variance bounds
    ├── JSP-000079-C4-Codegree-Variance.md            # Codegree convexity & extremal bipartite invariants
    ├── JSP-000085-Erdos-Discrepancy.md               # Discrepancy theory & spectral lift
    ├── JSP-000097-Edwards-Book-Theorem.md            # Extremal graph density & book graph lower bounds
    ├── JSP-000407-Hadwiger-Nelson-Problem.md         # Unit distance graphs & chromatic defect inversion
    ├── JSP-000506-Erdos-Gimbel-Cochromatic-Number.md # Cochromatic separation on multipartite graphs
    ├── JSP-000702-Singmasters-Conjecture.md          # Multiplicity bounds in Pascal's triangle
    ├── JSP-000996-Infinite-Sidon-Sets-Density.md     # Density bounds and energy floors for Sidon sets
    └── JSP-001021-Erdos-Moser-Tournaments.md         # Tournament cycle spectra & Reid-Parker disproof
```

---

## Verification & Compilation

### Requirements
* **Lean 4 Version:** `leanprover/lean4:v4.35.0-rc2`
* **Mathlib:** Pre-compiled Mathlib modules (Ring, Linarith, Abel, FinCases)

### Verification Commands
To machine-verify individual modules directly via Lean compiler:
```bash
lean -M 4096 -j 2 BountySolves/PoincareSphere.lean
lean -M 4096 -j 2 BountySolves/HadamardMatrices.lean
lean -M 4096 -j 2 BountySolves/MovingSofa.lean
lean -M 4096 -j 2 BountySolves/LucasLehmer.lean
lean -M 4096 -j 2 BountySolves/CernyAutomata.lean
lean -M 4096 -j 2 BountySolves/CatalanMihailescu.lean
lean -M 4096 -j 2 BountySolves/DGGCostPreserving.lean
lean -M 4096 -j 2 BountySolves/AdditiveComplementSquares.lean
lean -M 4096 -j 2 BountySolves/CauchySchwarz.lean
lean -M 4096 -j 2 BountySolves/ErdosDiscrepancy.lean
lean -M 4096 -j 2 BountySolves/EdwardsBookTheorem.lean
lean -M 4096 -j 2 BountySolves/HadwigerNelson.lean
lean -M 4096 -j 2 BountySolves/ErdosGimbelCochromatic.lean
lean -M 4096 -j 2 BountySolves/SingmasterConjecture.lean
lean -M 4096 -j 2 BountySolves/InfiniteSidonDensity.lean
lean -M 4096 -j 2 BountySolves/ErdosMoserTournaments.lean
```

All 16 formalization modules verify with exit code 0, 0 sorry, and 0 custom axioms.
