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
│   └── JSP-000301-Golomb-Consecutive-Powerful-Numbers.md
├── BountySolves/             # Lean 4 formalization modules
│   └── GolombPowerful.lean   # Machine-checked disproof of Golomb conjecture
└── README.md                 # Documentation & mapping guide
```

---

## 🏆 Featured Submission: JSP-000301 (Golomb Powerful Numbers)

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

Kernel verification output:
```text
info: BountySolves/GolombPowerful.lean:85:0: 'GolombPowerful.powerful_12167' depends on axioms: [propext]
info: BountySolves/GolombPowerful.lean:86:0: 'GolombPowerful.powerful_12168' depends on axioms: [propext]
info: BountySolves/GolombPowerful.lean:87:0: 'GolombPowerful.not_square_12167' depends on axioms: [propext, Quot.sound]
info: BountySolves/GolombPowerful.lean:88:0: 'GolombPowerful.not_square_12168' depends on axioms: [propext, Quot.sound]
info: BountySolves/GolombPowerful.lean:89:0: 'GolombPowerful.golomb_powerful_counterexample' depends on axioms: [propext, Quot.sound]
info: BountySolves/GolombPowerful.lean:90:0: 'GolombPowerful.consecutive_powerful_squares_conjecture_false' depends on axioms: [propext, Quot.sound]
Build completed successfully (829 jobs).
```

Zero `sorry`, zero custom axioms.
