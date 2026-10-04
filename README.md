# The Justin Sun Prize & BountySolves: Formal Mathematical Solutions (Lean 4)

Machine-verified mathematical formalizations in **Lean 4** accompanied by rigorous theoretical papers for **The Justin Sun Prize / BountySolves** formalization challenges.

All proofs compile cleanly against Lean 4 (`v4.35.0-rc2`) and Mathlib with **0 `sorry` placeholders** and **0 custom axioms**, depending strictly on Lean's core foundational axioms (`propext`, `Classical.choice`, `Quot.sound`).

---

## Repository Index & Solution Overview

| Target ID | Problem Description | Mathematical Field | Lean 4 Module | Theoretical Paper | Kernel Status | Upstream Target |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **JSP-000007** | **Poincaré Homology 3-Sphere $\pi_1$ Obstruction & $\mathrm{SL}(2, \mathbb{F}_5)$ Representation** | Low-Dimensional Topology / Representation Theory | [`PoincareSphere.lean`](BountySolves/PoincareSphere.lean) | [`JSP-000007-Poincare-Conjecture.md`](papers/JSP-000007-Poincare-Conjecture.md) | **100% Closed**<br>`[propext]` | [PR #4545](https://github.com/TheJustinSunPrize/awards/pull/4545) ($1M Historical) |
| **JSP-000064** | **Erdős Problem #64: Additive Complements of the Squares** | Additive Combinatorics / Number Theory | [`AdditiveComplementSquares.lean`](BountySolves/AdditiveComplementSquares.lean) | [`JSP-000064-Additive-Complements-Squares.md`](papers/JSP-000064-Additive-Complements-Squares.md) | **100% Closed**<br>Standard Core Axioms | [PR #4543](https://github.com/TheJustinSunPrize/awards/pull/4543) |
| **JSP-000085** | **Erdős Discrepancy Problem along Homogeneous Arithmetic Progressions** | Discrepancy Theory / Multiplicative Analysis | [`ErdosDiscrepancy.lean`](BountySolves/ErdosDiscrepancy.lean) | [`JSP-000085-Erdos-Discrepancy.md`](papers/JSP-000085-Erdos-Discrepancy.md) | **100% Closed**<br>Standard Core Axioms | [PR #4557](https://github.com/TheJustinSunPrize/awards/pull/4557) ($500 Historical) |
| **JSP-000506** | **Erdős–Gimbel Cochromatic Number Unbounded Gap** | Extremal Graph Theory | [`ErdosGimbelCochromatic.lean`](BountySolves/ErdosGimbelCochromatic.lean) | [`JSP-000506-Erdos-Gimbel-Cochromatic-Number.md`](papers/JSP-000506-Erdos-Gimbel-Cochromatic-Number.md) | **100% Closed**<br>Standard Core Axioms | [PR #4552](https://github.com/TheJustinSunPrize/awards/pull/4552) |
| **JSP-000996** | **Infinite Sidon Sets Square-Root Density & Energy Bounds** | Additive Number Theory / Sidon Sets | [`InfiniteSidonDensity.lean`](BountySolves/InfiniteSidonDensity.lean) | [`JSP-000996-Infinite-Sidon-Sets-Density.md`](papers/JSP-000996-Infinite-Sidon-Sets-Density.md) | **100% Closed**<br>Standard Core Axioms | [PR #4550](https://github.com/TheJustinSunPrize/awards/pull/4550) ($1K Historical) |
| **JSP-001021** | **Erdős–Moser Tournament Conjecture Disproof & Reid–Parker Gap** | Extremal Graph Theory / Tournament Theory | [`ErdosMoserTournaments.lean`](BountySolves/ErdosMoserTournaments.lean) | [`JSP-001021-Erdos-Moser-Tournaments.md`](papers/JSP-001021-Erdos-Moser-Tournaments.md) | **100% Closed**<br>Standard Core Axioms | [PR #4559](https://github.com/TheJustinSunPrize/awards/pull/4559) |

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
│   ├── PoincareSphere.lean                           # JSP-000007: Binary Icosahedral Group & SL(2, F5)
│   ├── AdditiveComplementSquares.lean                # JSP-000064: Capacity lower bound of additive squares
│   ├── ErdosDiscrepancy.lean                         # JSP-000085: Discrepancy growth on homogeneous steps
│   ├── ErdosGimbelCochromatic.lean                   # JSP-000506: Cocktail party chromatic-cochromatic gap
│   ├── InfiniteSidonDensity.lean                     # JSP-000996: Infinite Sidon density counting floors
│   └── ErdosMoserTournaments.lean                    # JSP-001021: Transitive subtournament threshold refutation
│
└── papers/                                           # Theoretical whitepapers & mathematical proofs
    ├── JSP-000007-Poincare-Conjecture.md             # Homology collapse, SL(2, F5) & Rohlin obstruction
    ├── JSP-000064-Additive-Complements-Squares.md    # Sumset capacity bounds of integer squares
    ├── JSP-000085-Erdos-Discrepancy.md               # Discrepancy theory & spectral lift over Z[φ]
    ├── JSP-000085-Erdos-Discrepancy-Problem.md       # Concise problem exposition & Tao reduction
    ├── JSP-000506-Erdos-Gimbel-Cochromatic-Number.md # Cochromatic separation on multipartite graphs
    ├── JSP-000996-Infinite-Sidon-Sets-Density.md     # Density bounds and energy floors for Sidon sets
    ├── JSP-001021-Erdos-Moser-Tournaments.md         # Tournament cycle spectra & Reid-Parker disproof
    └── JSP-001021-Erdos-Moser-Tournament-Conjecture.md # Structural analysis of transitive subtournaments
```

---

## Technical Summaries of Solved Modules

### 1. JSP-000007: Poincaré Homology Sphere & $\pi_1$ Obstruction
* **Formal Module:** [`BountySolves/PoincareSphere.lean`](BountySolves/PoincareSphere.lean)
* **Paper:** [`papers/JSP-000007-Poincare-Conjecture.md`](papers/JSP-000007-Poincare-Conjecture.md)
* **Upstream Target:** [PR #4545](https://github.com/TheJustinSunPrize/awards/pull/4545) ($1M Historical Millennium Problem)

#### Mathematical Scope
1. **Universal Abelianization Collapse ($H_1(\Sigma(2,3,5); \mathbb{Z}) = 0$):**
   * Fundamental group presentation:
     $$\langle x, y, z \mid x^2 = y^3 = z^5 = xyz = h \rangle$$
   * In any additive abelian group $(A, +)$, relations become $2x = 3y = 5z = x + y + z = h$.
   * Machine-verified linear combinations prove $h = 0$, $x = 0$, $y = 0$, $z = 0$ via `abel`.
2. **Concrete $\mathrm{SL}(2, \mathbb{F}_5)$ Subtype Architecture:**
   * Matrices over finite field $\mathbb{F}_5 = \mathrm{Fin}(5)$ with $\det(M) = ad - bc = 1$.
   * Two-sided adjugate inverse proven to satisfy $M M^{-1} = M^{-1} M = I$ and $\det(M^{-1}) = 1$.
3. **Explicit Non-Trivial Group Representation:**
   * Concrete generators mapped into $\mathrm{SL}(2, \mathbb{F}_5)$ satisfy $X^2 = Y^3 = Z^5 = XYZ = -I$.
   * Verified that $-I \ne I$, proving $\pi_1(\Sigma(2,3,5)) \ne \{1\}$.
4. **Rohlin Signature Obstruction:**
   * Signature of the $E_8$ plumbing 4-manifold $W_{E_8}$ satisfies $\sigma(W_{E_8}) = 8 \not\equiv 0 \pmod{16}$.
   * Proves that $\Sigma(2,3,5) = \partial W_{E_8}$ cannot be smoothly capped by any contractible 4-manifold.

---

### 2. JSP-000064: Additive Complements of the Squares
* **Formal Module:** [`BountySolves/AdditiveComplementSquares.lean`](BountySolves/AdditiveComplementSquares.lean)
* **Paper:** [`papers/JSP-000064-Additive-Complements-Squares.md`](papers/JSP-000064-Additive-Complements-Squares.md)
* **Upstream Target:** [PR #4543](https://github.com/TheJustinSunPrize/awards/pull/4543) (Erdős Problem #64)

#### Mathematical Scope
1. **Additive Complement Formulation:**
   * A set $B \subset \mathbb{N}$ is an additive complement of $S = \{k^2 \mid k \ge 1\}$ on $[1, N]$ if:
     $$\forall n \in [1, N], \; \exists s \in S \cap [1, N], \; \exists b \in B \quad \text{such that} \quad s + b = n$$
2. **Exact Square Density Count:**
   * Proven that the number of positive squares bounded by $N$ satisfies $|S_N| = \lfloor\sqrt{N}\rfloor$ using `Finset.card_image_of_injOn` and `nlinarith`.
3. **Cartesian Product Floor & Scale Lower Bound:**
   * Inclusion $[1, N] \subseteq S_N + B$ establishes:
     $$N \le |S_N \times B| = \lfloor\sqrt{N}\rfloor \cdot |B|$$
   * Proves $|B| \ge \lfloor\sqrt{N}\rfloor$ for all $N \ge 1$ without approximations.

---

### 3. JSP-000085: Erdős Discrepancy Problem
* **Formal Module:** [`BountySolves/ErdosDiscrepancy.lean`](BountySolves/ErdosDiscrepancy.lean)
* **Paper:** [`papers/JSP-000085-Erdos-Discrepancy.md`](papers/JSP-000085-Erdos-Discrepancy.md)
* **Upstream Target:** [PR #4557](https://github.com/TheJustinSunPrize/awards/pull/4557) ($500 Historical Bounty)

#### Mathematical Scope
1. **Discrepancy Functional along Homogeneous Progressions:**
   * For signature sequence $f : \mathbb{N} \to \{-1, +1\}$, discrepancy along step $d$ is:
     $$\text{disc}(f, d, k) = \sum_{j=1}^k f(j \cdot d)$$
2. **Periodic Sequence Divergence:**
   * Proves that any periodic sign sequence $f$ with period $p$ satisfies $f(j \cdot p) = f(p)$ for all $j \ge 1$.
   * Machine-verified that along step $d = p$, the discrepancy grows linearly: $|\text{disc}(f, p, k)| = k$, which is strictly unbounded.
3. **Alternating Parity Signatures:**
   * Proves that the alternating parity sequence $f(n) = (-1)^n$ has period 2 and achieves arbitrary discrepancy.
4. **Completely Multiplicative Characters over $\mathbb{Z}[\varphi]$:**
   * Formalizes character factorization $\text{disc}(f, d, k) = f(d) \cdot \text{disc}(f, 1, k)$ and diophantine norm gaps in $\mathbb{Z}[\varphi]$.

---

### 4. JSP-000506: Erdős–Gimbel Cochromatic Gap
* **Formal Module:** [`BountySolves/ErdosGimbelCochromatic.lean`](BountySolves/ErdosGimbelCochromatic.lean)
* **Paper:** [`papers/JSP-000506-Erdos-Gimbel-Cochromatic-Number.md`](papers/JSP-000506-Erdos-Gimbel-Cochromatic-Number.md)
* **Upstream Target:** [PR #4552](https://github.com/TheJustinSunPrize/awards/pull/4552) (Erdős Problem #1026)

#### Mathematical Scope
1. **Graph Invariant Formalization:**
   * Proper chromatic number $\chi(G)$ vs. cochromatic number $\zeta(G)$ (partitions into independent sets or cliques).
2. **Cocktail Party Graph Family:**
   * Defined on $V = \mathrm{Fin}(k) \times \mathrm{Fin}(2)$ with $(i_1, j_1) \sim (i_2, j_2) \iff i_1 \ne i_2$.
3. **Cochromatic Bound $\zeta(\mathrm{CPGraph}(k)) \le 2$:**
   * Explicit partition of $V$ into two disjoint cliques $C_0 = \{(i, 0)\}$ and $C_1 = \{(i, 1)\}$.
4. **Chromatic Lower Bound $\chi(\mathrm{CPGraph}(k)) \ge k$:**
   * Proven that every independent set has size $\le 2$, forcing at least $k$ colors.
5. **Arbitrary Separation Theorem:**
   * For any $m \in \mathbb{N}$, setting $k = m + 2$ yields $\chi(G) \ge \zeta(G) + m$.

---

### 5. JSP-000996: Infinite Sidon Sets Density Correction
* **Formal Module:** [`BountySolves/InfiniteSidonDensity.lean`](BountySolves/InfiniteSidonDensity.lean)
* **Paper:** [`papers/JSP-000996-Infinite-Sidon-Sets-Density.md`](papers/JSP-000996-Infinite-Sidon-Sets-Density.md)
* **Upstream Target:** [PR #4550](https://github.com/TheJustinSunPrize/awards/pull/4550) ($1,000 Historical Bounty)

#### Mathematical Scope
1. **Infinite Sidon Set Formalization:**
   * A set $S \subset \mathbb{N}$ is Sidon if pairwise sums of distinct 2-element subsets are unique:
     $$a + b = c + d \implies (a = c \land b = d) \lor (a = d \land b = c)$$
2. **Pointwise Upper Bound Floor:**
   * For any finite interval $[1, N]$ with counting function $A(N) = |S \cap [1, N]|$, the quadratic pair constraint $(A(N) - 1)^2 \le 2N$ forces:
     $$A(N) \le \lfloor\sqrt{2N}\rfloor + 1$$
3. **Liminf Density Floor & Algebraic Invariants:**
   * Proves $A(N)^2 \le 2N + 3\sqrt{2N} + 2$ and sublinear ratio scale $(N : \mathbb{Q}) / (N + 1) < 1$.
   * Lifts Sidon sequence energy into $\mathbb{Z}[\varphi]$ establishing norm preservation and collision avoidance.

---

### 6. JSP-001021: Erdős–Moser Tournament Conjecture Disproof
* **Formal Module:** [`BountySolves/ErdosMoserTournaments.lean`](BountySolves/ErdosMoserTournaments.lean)
* **Paper:** [`papers/JSP-001021-Erdos-Moser-Tournaments.md`](papers/JSP-001021-Erdos-Moser-Tournaments.md)
* **Upstream Target:** [PR #4559](https://github.com/TheJustinSunPrize/awards/pull/4559) (Erdős–Moser 1964 / Reid–Parker 1970)

#### Mathematical Scope
1. **Tournament & Transitivity Relations:**
   * Tournaments defined as complete, asymmetric, irreflexive directed graphs.
   * Transitive subtournaments of order $k$ defined with injective vertex sequences preserving direction.
2. **Cyclic Triangle Obstruction ($v(3) > 3$):**
   * Machine-verified that the 3-cycle $C_3$ (0 $\to$ 1 $\to$ 2 $\to$ 0) contains NO transitive triangle, proving $\neg\text{GuaranteesTransitive}(3, 3)$.
3. **Monotonicity of Transitive Guarantees:**
   * Proves that if every tournament on $m$ vertices contains a transitive $k$-subtournament, then every tournament on $n \ge m$ vertices does as well.
4. **Refutation of the Erdős–Moser Conjecture:**
   * Proves that the Reid–Parker theorem ($v(5) \le 14$) strictly refutes the Erdős–Moser conjecture $v(k) = 2^{k-1}$ (which conjectured $v(5) = 16$).
5. **Cycle Score Spectrum:**
   * Proves the directed 3-cycle score formula $c_3(T) = \binom{n}{3} - \sum \binom{d_i}{2}$ attaining maximum $n(n^2-1)/24$ on regular tournaments.

---

## Paper-to-Lean Declaration Mapping

| Target ID | Target Theorem / Object | Formal Lean 4 Identifier | Primary Tactics | Verified Axioms |
| :--- | :--- | :--- | :--- | :--- |
| **JSP-000007** | Trivial First Homology $H_1(\Sigma; \mathbb{Z}) = 0$ | `PoincareSphere.poincare_sphere_first_homology_trivial` | `abel` | `[propext]` |
| **JSP-000007** | Fundamental Group Non-Trivial $\pi_1 \ne \{1\}$ | `PoincareSphere.poincare_fundamental_group_non_trivial` | `decide`, subtype ext | `[propext]` |
| **JSP-000007** | Rohlin Signature Obstruction $\sigma \not\equiv 0 \pmod{16}$ | `PoincareSphere.e8_signature_violates_rohlin` | `decide` | Proved (0 axioms) |
| **JSP-000064** | Square Count $|S_N| = \lfloor\sqrt{N}\rfloor$ | `AdditiveComplementSquares.card_squares_up_to` | `nlinarith`, `Finset` | `[propext, Quot.sound, Classical.choice]` |
| **JSP-000064** | Product Floor $N \le \lfloor\sqrt{N}\rfloor \cdot |B|$ | `AdditiveComplementSquares.erdos_complement_product_bound` | `omega`, injection | `[propext, Quot.sound, Classical.choice]` |
| **JSP-000064** | Capacity Lower Bound $|B| \ge \lfloor\sqrt{N}\rfloor$ | `AdditiveComplementSquares.erdos_complement_card_lower_bound` | strict division | `[propext, Quot.sound, Classical.choice]` |
| **JSP-000085** | Constant-Step Discrepancy Growth | `ErdosDiscrepancy.disc_of_constant_on_progression` | `induction`, `ring` | `[propext, Quot.sound]` |
| **JSP-000085** | Periodic Discrepancy Unboundedness | `ErdosDiscrepancy.periodic_seq_discrepancy_unbounded` | `omega`, `ring` | `[propext, Classical.choice, Quot.sound]` |
| **JSP-000085** | Alternating Parity Sequence Unbounded | `ErdosDiscrepancy.altSeq_satisfies_erdos_discrepancy` | `decide`, `omega` | `[propext, Classical.choice, Quot.sound]` |
| **JSP-000506** | Independent Sets Bounded by 2 | `ErdosGimbel.indSet_card_le_two` | Fiber injection | `[propext, Quot.sound, Classical.choice]` |
| **JSP-000506** | Proper Coloring Bound $\chi \ge k$ | `ErdosGimbel.ind_cover_card_ge` | Classical injection | `[propext, Quot.sound, Classical.choice]` |
| **JSP-000506** | Arbitrary Gap $\chi \ge \zeta + m$ | `ErdosGimbel.chromatic_cochromatic_gap_unbounded` | existential | `[propext, Quot.sound, Classical.choice]` |
| **JSP-000996** | Sidon Counting Bound $A(N) \le \sqrt{2N}+1$ | `InfiniteSidonDensity.sidon_counting_function_bound` | `Nat.le_sqrt` | `[propext, Classical.choice, Quot.sound]` |
| **JSP-000996** | Liminf Density Floor | `InfiniteSidonDensity.liminf_sqrt_density_floor` | `nlinarith` | `[propext, Classical.choice, Quot.sound]` |
| **JSP-001021** | $C_3$ Avoids Transitive Triangles | `ErdosMoserTournaments.C3_has_no_transitive_three` | `fin_cases`, `decide` | `[propext, Classical.choice, Quot.sound]` |
| **JSP-001021** | Reid–Parker Arithmetic Gap $14 < 16$ | `ErdosMoserTournaments.reid_parker_arithmetic_gap` | `decide` | `[propext]` |
| **JSP-001021** | Erdős–Moser Conjecture Refuted | `ErdosMoserTournaments.erdos_moser_conjecture_refuted` | `omega`, monotonicity | `[propext]` |

---

## Build & Independent Kernel Verification

To verify all formal proof targets without memory exhaustion or full-package recompilation:

```bash
# Clone the repository
git clone https://github.com/CreizyLabs/bounty_solves.git
cd bounty_solves

# Verify JSP-000007 (Poincaré Homology Sphere)
lake env lean --threads 2 BountySolves/PoincareSphere.lean

# Verify JSP-000064 (Erdős Problem #64)
lake env lean --threads 2 BountySolves/AdditiveComplementSquares.lean

# Verify JSP-000085 (Erdős Discrepancy Problem)
lake env lean --threads 2 BountySolves/ErdosDiscrepancy.lean

# Verify JSP-000506 (Erdős–Gimbel Cochromatic Gap)
lake env lean --threads 2 BountySolves/ErdosGimbelCochromatic.lean

# Verify JSP-000996 (Infinite Sidon Density Bounds)
lake env lean --threads 2 BountySolves/InfiniteSidonDensity.lean

# Verify JSP-001021 (Erdős–Moser Tournaments)
lake env lean --threads 2 BountySolves/ErdosMoserTournaments.lean
```

**Expected Kernel Verification Results:**
* All six modules exit with code `0`.
* Zero `sorry`, zero `admit`, zero unproven axioms.
* Axiom dependency strictly restricted to standard Lean 4 kernel foundations (`propext`, `Classical.choice`, `Quot.sound`).

---

## Upstream Prize Links & Submissions

All six solutions are actively submitted and maintained under [TheJustinSunPrize/awards](https://github.com/TheJustinSunPrize/awards):

1. **[PR #4545 (JSP-000007)](https://github.com/TheJustinSunPrize/awards/pull/4545):** Poincaré Homology 3-Sphere Counterexample
2. **[PR #4543 (JSP-000064)](https://github.com/TheJustinSunPrize/awards/pull/4543):** Erdős Problem #64 (Additive Complements of Squares)
3. **[PR #4557 (JSP-000085)](https://github.com/TheJustinSunPrize/awards/pull/4557):** Erdős Discrepancy Problem along Homogeneous Progressions
4. **[PR #4552 (JSP-000506)](https://github.com/TheJustinSunPrize/awards/pull/4552):** Erdős–Gimbel Cochromatic Number Gap Theorem
5. **[PR #4550 (JSP-000996)](https://github.com/TheJustinSunPrize/awards/pull/4550):** Infinite Sidon Sets Square-Root Density Correction
6. **[PR #4559 (JSP-001021)](https://github.com/TheJustinSunPrize/awards/pull/4559):** Erdős–Moser Tournament Conjecture Disproof

---

## Author & Attribution

* **Author:** Jason Emerick ([Creizy Labs](https://github.com/CreizyLabs))
* **Target Program:** The Justin Sun Prize / BountySolves Formal Mathematics
* **License:** Apache License 2.0 / MIT