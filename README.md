# The Justin Sun Prize & BountySolves: Formal Mathematical Solutions (Lean 4)

Machine-verified mathematical formalizations in **Lean 4** accompanied by rigorous theoretical papers for **The Justin Sun Prize / BountySolves** formalization challenges.

All proofs compile cleanly against Lean 4 (`v4.35.0-rc2`) and Mathlib4 with **0 `sorry` placeholders**, **0 `admit`**, and **0 custom axioms**, depending strictly on Lean's core foundational axioms (`propext`, `Classical.choice`, `Quot.sound`).

---

## Master Repository Index & Solution Ledger

| Target ID | Problem Description | Mathematical Field | Lean 4 Module | Theoretical Paper | Kernel Status | Upstream Awards Submission |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **JSP-000043** | **Unconditional Formalization of Distinct Subset Sum Extremal Bounds & Arbitrary-$n$ Conway–Guy Families** | Number Theory / Additive Combinatorics | [`LowerBoundMaxElement.lean`](BountySolves/LowerBoundMaxElement.lean) | [`JSP-000043-Lower-Bound-Max-Element.md`](papers/JSP-000043-Lower-Bound-Max-Element.md)<br>[`Formal Paper (PDF)`](papers/Formal%20Paper%20-%20Lower%20Bound%20on%20Maximum%20Element%20of%20Sets%20with%20Distinct%20Subset%20Sums.pdf) | **100% Closed**<br>Standard Core Axioms | [PR #5541](https://github.com/TheJustinSunPrize/awards/pull/5541) (\$500 Historical) |

---

## Directory Architecture

```text
.
├── README.md                                            # Master repository documentation & verification ledger
├── lakefile.lean                                        # Lake build system package configuration
├── lake-manifest.json                                   # Pinned Mathlib4 dependency manifest
├── lean-toolchain                                       # Compiler pin: leanprover/lean4:v4.35.0-rc2
├── verify.bat                                           # Automated verification batch script
│
├── BountySolves/                                        # Formal Lean 4 source modules (Zero sorry, zero admit)
│   └── LowerBoundMaxElement.lean                        # JSP-000043: General capacity floor & arbitrary-n inductive families
│
└── papers/                                              # Theoretical whitepapers & mathematical proofs
    ├── Formal Paper - Lower Bound on Maximum Element of Sets with Distinct Subset Sums.pdf
    └── JSP-000043-Lower-Bound-Max-Element.md
```

---

## Verification & Compilation

### Requirements
* **Lean 4 Version:** `leanprover/lean4:v4.35.0-rc2`
* **Mathlib4:** Pinned in `lake-manifest.json`

### Verification Commands
```bash
lake env lean BountySolves/LowerBoundMaxElement.lean
```

### Axiom Audit Output
```text
'LowerBoundMaxElement.sum_le_sum_of_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'LowerBoundMaxElement.combinatorial_capacity_floor' depends on axioms: [propext, Classical.choice, Quot.sound]
'LowerBoundMaxElement.sum_le_card_mul_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'LowerBoundMaxElement.distinct_subset_sums_max_element_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'LowerBoundMaxElement.max_element_product_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'LowerBoundMaxElement.geom_sum_powers_of_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'LowerBoundMaxElement.capacity_floor_sharpness' depends on axioms: [propext, Classical.choice, Quot.sound]
'LowerBoundMaxElement.asymptotic_capacity_ratio_decay' depends on axioms: [propext, Quot.sound]
'LowerBoundMaxElement.dyadicLift_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'LowerBoundMaxElement.dyadicLift_distinct_subset_sums' depends on axioms: [propext, Classical.choice, Quot.sound]
'LowerBoundMaxElement.conwayGuyFamily_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'LowerBoundMaxElement.conwayGuyFamily_distinct_subset_sums' depends on axioms: [propext, Classical.choice, Quot.sound]
'LowerBoundMaxElement.conwayGuyFamily_max_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'LowerBoundMaxElement.conwayGuyFamily_beats_power_of_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'LowerBoundMaxElement.conwayGuyOrder5Family_distinct_subset_sums' depends on axioms: [propext, Classical.choice, Quot.sound]
'LowerBoundMaxElement.conwayGuyOrder5Family_beats_power_of_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'LowerBoundMaxElement.universal_arbitrary_n_sub_power_of_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'LowerBoundMaxElement.naive_power_of_two_bound_disproved_for_all_n_ge_4' depends on axioms: [propext, Classical.choice, Quot.sound]
'LowerBoundMaxElement.conway_guy_erdos_conjecture_disproved' depends on axioms: [propext, Classical.choice, Quot.sound]
'LowerBoundMaxElement.naive_power_of_two_bound_disproved' depends on axioms: [propext]
```
