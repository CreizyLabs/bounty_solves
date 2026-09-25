# Bounty Solves — Lean 4 Proof Verification

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22884961.svg)](https://doi.org/10.5281/zenodo.22884961)
[![Lean 4](https://img.shields.io/badge/Lean_4-v4.35.0--rc2-blue.svg)](https://leanprover.github.io/)
[![License](https://img.shields.io/badge/License-Apache_2.0-green.svg)](LICENSE)

This repository contains verified mathematical solutions and formal proof packages developed for academic bounties, including **The Justin Sun Prize** ([`TheJustinSunPrize/awards`](https://github.com/TheJustinSunPrize/awards)).

Every official submission package in this repository satisfies three strict criteria:
1. **A Complete Informal Paper**: A full mathematical proof from first principles without omitted cases or hand-waving.
2. **A Complete End-to-End Lean 4 Formalization**: Exactly matching the catalog statement, kernel-verified with 0 `sorry` and 0 custom axioms.
3. **Reproducible Repository Packaging**: Verified build commands, axiom audits, and explicit mapping between paper sections and Lean declarations.

---

## 📁 Repository Structure

```
bounty_solves/
├── lakefile.lean             # Lake build configuration specifying mathlib & targets
├── lake-manifest.json        # Pinned dependency manifest
├── lean-toolchain            # Pinned Lean 4 toolchain (v4.35.0-rc2)
├── papers/                   # Complete informal mathematical papers
│   ├── JSP-000301-Golomb-Consecutive-Powerful-Numbers.md
│   └── JSP-000288-Minimal-Stably-Complete-Sequences.md
├── BountySolves/             # Lean 4 formalization modules
│   ├── GolombPowerful.lean
│   └── StablyCompleteGoldenRatio.lean
└── README.md                 # Documentation & mapping guide
```

---

## 🏆 Submission 1: JSP-000301 (Golomb Powerful Numbers)

* **Problem**: *If two consecutive positive integers are powerful, must at least one be a perfect square?*
* **Catalog ID**: [JSP-000301](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#JSP-000301)
* **Mathematical Solver**: Solomon W. Golomb (1970), *Powerful Numbers*, American Mathematical Monthly 77(8): 848–852; Erdős Problem #365.
* **Formalization Author**: Jason Emerick (`@CreizyLabs`)
* **Informal Paper**: [`papers/JSP-000301-Golomb-Consecutive-Powerful-Numbers.md`](papers/JSP-000301-Golomb-Consecutive-Powerful-Numbers.md)
* **Lean 4 Module**: [`BountySolves/GolombPowerful.lean`](BountySolves/GolombPowerful.lean)
* **PR on Awards Repo**: [TheJustinSunPrize/awards#4516](https://github.com/TheJustinSunPrize/awards/pull/4516)

### One-to-One Paper to Lean Declaration Mapping

| Paper Section | Mathematical Statement | Lean 4 Identifier | Method |
| :--- | :--- | :--- | :--- |
| **Section 2.1** | Canonical powerful number form $x^2 y^3$ | `GolombPowerful.IsPowerful` | Definition |
| **Section 2.2** | Perfect square definition $k^2 = n$ | `GolombPowerful.IsSquare` | Definition |
| **Lemma 3.1** | $12168 - 12167 = 1$ | `GolombPowerful.consecutive_12167_12168` | `by decide` |
| **Lemma 3.2** | $12167 = 1^2 \cdot 23^3$ is powerful | `GolombPowerful.powerful_12167` | `by use 1, 23; decide` |
| **Lemma 3.3** | $12168 = 39^2 \cdot 2^3$ is powerful | `GolombPowerful.powerful_12168` | `by use 39, 2; decide` |
| **Lemma 3.4** | $110^2 < 12167 < 111^2 \implies \neg \text{IsSquare}(12167)$ | `GolombPowerful.not_square_12167` | `by omega; decide` |
| **Lemma 3.5** | $110^2 < 12168 < 111^2 \implies \neg \text{IsSquare}(12168)$ | `GolombPowerful.not_square_12168` | `by omega; decide` |
| **Theorem 4.1** | Exact prize conjecture is False | `GolombPowerful.consecutive_powerful_squares_conjecture_false` | Machine-Closed |

### Verification & Reproduction
```bash
lake build GolombPowerful
```
Kernel verification: depends only on standard `[propext, Quot.sound]` (0 `sorry`, 0 custom axioms).

---

## 🏆 Submission 2: JSP-000288 (Minimal Stably Complete Sequences)

* **Problem**: *Must ratios of consecutive terms in the specified minimal stably complete sequences converge to the golden ratio?*
* **Catalog ID**: [JSP-000288](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0201-0300.md#JSP-000288)
* **Mathematical Solver**: Ronald L. Graham (1964) / Paul Erdős & Ronald L. Graham (1980); Erdős Problem #346.
* **Formalization Author**: Jason Emerick (`@CreizyLabs`)
* **Informal Paper**: [`papers/JSP-000288-Minimal-Stably-Complete-Sequences.md`](papers/JSP-000288-Minimal-Stably-Complete-Sequences.md)
* **Lean 4 Module**: [`BountySolves/StablyCompleteGoldenRatio.lean`](BountySolves/StablyCompleteGoldenRatio.lean)

### One-to-One Paper to Lean Declaration Mapping

| Paper Section | Mathematical Statement | Lean 4 Identifier | Method |
| :--- | :--- | :--- | :--- |
| **Section 2.1** | Subset Sums Definition | `Erdos346.subsetSums` | Definition |
| **Section 2.2** | Completeness on Index Set | `Erdos346.IsCompleteOn` | Definition |
| **Section 2.3** | Finite Deletion Completeness | `Erdos346.ValueFiniteDeletionComplete` | Definition |
| **Section 2.4** | Infinite Deletion Incompleteness | `Erdos346.ValueInfiniteDeletionIncomplete` | Definition |
| **Section 2.5** | Uniform Ratio Gap | `Erdos346.HasUniformRatioGap` | Definition |
| **Lemma 3.1** | Threshold Monotonicity | `Erdos346.subsetSums_mono` | Proved |
| **Lemma 3.2** | Exponential Growth Lower Bound | `Erdos346.ratio_lower_bound` | Proved |
| **Lemma 3.3** | Golden Ratio Rigidity | `Erdos346.main` | Proved |
| **Theorem 4.1** | Main Characterization Theorem | `Erdos346.main_valueDeletion` | Proved (0 `sorry`) |
| **Theorem 4.1 (Expanded)**| Explicit Public Statement | `Erdos346.main_valueDeletion_expanded` | Proved (0 `sorry`) |

### Verification & Reproduction
```bash
lake build StablyCompleteGoldenRatio
```
Kernel verification: depends only on standard `[propext, Quot.sound, Classical.choice]` (0 `sorry`, 0 custom axioms).

---

## 3. JSP-000465: Erdős–Simonovits Compactness Conjecture Refutation

* **Problem ID**: [JSP-000465](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000465)
* **Mathematical Solvers**: Internal OpenAI model (Astra); Erdős Problem #180
* **Formalization Author**: Jason Emerick (`@CreizyLabs`)
* **Informal Paper**: [`papers/JSP-000465-Erdos-Simonovits-Compactness-Conjecture.md`](papers/JSP-000465-Erdos-Simonovits-Compactness-Conjecture.md)
* **Lean 4 Module**: [`BountySolves/ErdosSimonovitsCompactness.lean`](BountySolves/ErdosSimonovitsCompactness.lean)

### One-to-One Paper to Lean Declaration Mapping

| Paper Section | Mathematical Statement | Lean 4 Identifier | Method |
| :--- | :--- | :--- | :--- |
| **Section 2.1** | Family-Free Subgraph Definition | `CompactnessConjecture.FamilyFree` | Definition |
| **Section 2.2** | Extremal Number for Family | `CompactnessConjecture.familyExtremal` | Definition |
| **Section 2.3** | Cyclic Family Definition | `CompactnessConjecture.IsCyclicFamily` | Definition |
| **Section 2.4** | Compact Family Definition | `CompactnessConjecture.IsCompactFamily` | Definition |
| **Section 2.5** | Compactness Conjecture Statement | `CompactnessConjecture.CompactnessConjectureStatement` | Definition |
| **Construction 3.1** | Proposed Bipartite Family | `CompactnessConjecture.proposedFamily` | Construction |
| **Lemma 3.2** | Uniform Member Lower Bound | `CompactnessConjecture.proposedFamily_uniformMemberLower` | Proved |
| **Lemma 3.3** | Sixteenth-Power Host Bound | `CompactnessConjecture.proposedFamily_familyExtremal_sixteenth_power_le` | Proved |
| **Theorem 3.4** | Non-Compactness of Family | `CompactnessConjecture.proposedFamily_not_compact` | Proved |
| **Corollary 3.5** | Main Refutation Theorem | `CompactnessConjecture.not_erdos_180` | Proved (0 `sorry`) |
| **Theorem 4.1** | Quantitative Counterexample | `CompactnessConjecture.quantitativeCompactnessCounterexample` | Proved (0 `sorry`) |
| **Theorem 4.2** | Asymptotic Big-O Form | `CompactnessConjecture.compactnessCounterexample_bigO` | Proved (0 `sorry`) |

### Verification & Reproduction
```bash
lake build ErdosSimonovitsCompactness
```
Kernel verification: depends only on standard `[propext, Quot.sound, Classical.choice]` (0 `sorry`, 0 custom axioms).

---

## 4. JSP-000788: Erdős–Galvin Subset Sums Conjecture Refutation

* **Problem ID**: [JSP-000788](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0701-0800.md#JSP-000788)
* **Mathematical Solvers**: Paul Erdős and Fred Galvin (1991); negative answer by Lisa Price & GPT Pro; Erdős Problem #948
* **Formalization Author**: Jason Emerick (`@CreizyLabs`)
* **Informal Paper**: [`papers/JSP-000788-Erdos-Galvin-Subset-Sums.md`](papers/JSP-000788-Erdos-Galvin-Subset-Sums.md)
* **Lean 4 Module**: [`BountySolves/ErdosGalvinSubsetSums.lean`](BountySolves/ErdosGalvinSubsetSums.lean)

### One-to-One Paper to Lean Declaration Mapping

| Paper Section | Mathematical Statement | Lean 4 Identifier | Method |
| :--- | :--- | :--- | :--- |
| **Section 3.1** | Non-Decreasing Envelope | `Erdos948.Fenv` | Definition |
| **Section 3.2** | Threshold Growth Operator | `Erdos948.Gfun` | Definition |
| **Section 3.3** | Greedy Support Clustering | `Erdos948.clusterAux2`, `Erdos948.rho` | Definition |
| **Section 3.4** | Universal Integer Coloring | `Erdos948.chi` | Definition |
| **Lemma 4.1** | Block Decoupling Under Gap Growth | `Erdos948.clusterAux2_ge_bound` | Proved |
| **Lemma 4.2** | Countable Surjectivity on Finite Sums | `Erdos948.countable` | Proved |
| **Theorem 4.3** | All Colors Hit on Finite Integer Palette | `Erdos948.finite` | Proved |
| **Theorem 4.3 (Nat)** | All Colors Hit on Natural Palette | `Erdos948.finite_nat` | Proved |
| **Corollary 4.4 (Int)** | Main Refutation of Conjecture | `Erdos948.not_erdos_948` | Proved (0 `sorry`) |
| **Corollary 4.4 (Nat)** | Natural-Number Statement Refutation | `Erdos948.erdos_948_nat` | Proved (0 `sorry`) |

### Verification & Reproduction
```bash
lake build ErdosGalvinSubsetSums
```
Kernel verification: depends only on standard `[propext, Quot.sound, Classical.choice]` (0 `sorry`, 0 custom axioms).
