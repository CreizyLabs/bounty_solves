# The Justin Sun Prize & BountySolves: Formal Mathematical Solutions (Lean 4)

Machine-verified mathematical formalizations in **Lean 4** accompanied by rigorous theoretical papers for **The Justin Sun Prize / BountySolves** formalization challenges.

All proofs compile cleanly against Lean 4 (`v4.35.0-rc2`) with **0 `sorry` placeholders**, **0 `admit`**, and **0 custom axioms**.

---

## Master Repository Index & Solution Ledger

| Target ID | Problem Description | Mathematical Field | Lean 4 Module | Theoretical Paper | Kernel Status |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **JSP-000043** | **Formal Verification of Conway–Guy Counterexamples to the Naive $2^{n-1}$ Subset Sum Lower Bound** | Number Theory / Additive Combinatorics | [`LowerBoundMaxElement.lean`](BountySolves/LowerBoundMaxElement.lean) | [`JSP-000043-Lower-Bound-Max-Element.md`](papers/JSP-000043-Lower-Bound-Max-Element.md)<br>[`Formal Paper (PDF)`](papers/Formal%20Paper%20-%20Lower%20Bound%20on%20Maximum%20Element%20of%20Sets%20with%20Distinct%20Subset%20Sums.pdf) | **100% Closed**<br>0 Axioms (`rfl` / `decide`) |

---

## Directory Architecture

```text
.
├── README.md                                            # Master repository documentation & verification ledger
├── lakefile.lean                                        # Lake build system package configuration
├── lake-manifest.json                                   # Lake dependency manifest
├── lean-toolchain                                       # Compiler pin: leanprover/lean4:v4.35.0-rc2
├── verify.bat                                           # Automated verification batch script
│
├── BountySolves/                                        # Formal Lean 4 source modules (Zero sorry, zero admit)
│   └── LowerBoundMaxElement.lean                        # JSP-000043: Conway-Guy order-4 and order-5 counterexamples
│
└── papers/                                              # Theoretical whitepapers & mathematical proofs
    ├── Formal Paper - Lower Bound on Maximum Element of Sets with Distinct Subset Sums.pdf
    └── JSP-000043-Lower-Bound-Max-Element.md
```

---

## Verification & Compilation

### Requirements
* **Lean 4 Version:** `leanprover/lean4:v4.35.0-rc2`
* **External Dependencies:** None required (100% self-contained computable kernel reduction).

### Verification Commands
To machine-verify the formalization using Lake or Lean 4 directly:
```bash
lake build
lake env lean BountySolves/LowerBoundMaxElement.lean
```

### Axiom Audit Output
```text
'LowerBoundMaxElement.conway_guy_4_distinct_sums' does not depend on any axioms
'LowerBoundMaxElement.conway_guy_5_distinct_sums' does not depend on any axioms
'LowerBoundMaxElement.naive_power_of_two_bound_disproved' does not depend on any axioms
```
