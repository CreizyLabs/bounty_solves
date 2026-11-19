# CreizyLabs Bounty Solves: Kernel-Verified Lean 4 Formalizations for The Justin Sun Prize

Complete, independent, unconditional **Lean 4** formalizations accompanied by self-contained formal mathematical papers for **The Justin Sun Prize** (`TheJustinSunPrize/awards`).

Every Lean 4 module in [`bountysolves/`](bountysolves/) compiles cleanly under **Lean `4.35.0-rc2`** with `autoImplicit = false` against pinned **Mathlib4** (`9f7aa3a1327bbbc1716bdcedb64b2592e54b9bc7`), with:
- **0 `sorry`**, **0 `admit`**
- **0 custom axioms** (`#print axioms` strictly `[propext, Classical.choice, Quot.sound]`)
- **0 `native_decide`**, **0 `Lean.ofReduceBool`**, **0 `Lean.trustCompiler`**
- **0 warnings**, **0 approximations**

---

## Master Solution Ledger

| JSP ID | Erdős # | Problem Summary | Mathematical Solver(s) | Lean 4 Module (`bountysolves/`) | Formal Paper (`papers/`) | Axioms |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **JSP-000301** | #365 | Disproof: consecutive powerful integers need not include a perfect square (`12167, 12168`) | Solomon W. Golomb (1970) | [`JSP_000301_GolombPowerful.lean`](bountysolves/JSP_000301_GolombPowerful.lean) | [`JSP-000301-Golomb-Powerful-Numbers.md`](papers/JSP-000301-Golomb-Powerful-Numbers.md) | `[propext, Classical.choice, Quot.sound]` |
| **JSP-000490** | #603 | No uniform cardinal bound on chromatic number of countable families avoiding pairwise intersection size `2` | GPT-5.4 Pro / Przemyslaw Chojecki | [`JSP_000490_Erdos603_ForbiddenIntersectionTwo.lean`](bountysolves/JSP_000490_Erdos603_ForbiddenIntersectionTwo.lean) | [`JSP-000490-Erdos-603-Forbidden-Intersection-Two.md`](papers/JSP-000490-Erdos-603-Forbidden-Intersection-Two.md) | `[propext, Classical.choice, Quot.sound]` |
| **JSP-000690** | #834 | Explicit 7-regular, 21-edge, 3-uniform, 3-chromatic-critical hypergraph on 9 vertices | Ruiliang Li (2025, `arXiv:2512.24850`) | [`JSP_000690_ErdosLovasz_3CriticalHypergraph.lean`](bountysolves/JSP_000690_ErdosLovasz_3CriticalHypergraph.lean) | [`JSP-000690-Erdos-Lovasz-3Critical-Hypergraph.md`](papers/JSP-000690-Erdos-Lovasz-3Critical-Hypergraph.md) | `[propext, Classical.choice, Quot.sound]` |
| **JSP-000698** | #842 | Fleischner–Stiebitz theorem: every cycle-plus-triangles graph is 3-choosable and 3-colorable (`χ(G) ≤ 3`) | H. Fleischner & M. Stiebitz (1992) | [`JSP_000698_FleischnerStiebitz_CyclePlusTriangles.lean`](bountysolves/JSP_000698_FleischnerStiebitz_CyclePlusTriangles.lean) | [`JSP-000698-Fleischner-Stiebitz-Cycle-Plus-Triangles.md`](papers/JSP-000698-Fleischner-Stiebitz-Cycle-Plus-Triangles.md) | `[propext, Classical.choice, Quot.sound]` |
| **JSP-000746** | #895 | Every triangle-free graph on `{1..18}`, `ℕ`, or `ℤ` has three distinct independent vertices `a, b, a + b` | Ben Barber (threshold `N = 18`); Łuczak–Rödl–Schoen (1998) | [`JSP_000746_TriangleFreeSchurTriple.lean`](bountysolves/JSP_000746_TriangleFreeSchurTriple.lean) | [`JSP-000746-Erdos-Barber-Triangle-Free-Schur-Triple.md`](papers/JSP-000746-Erdos-Barber-Triangle-Free-Schur-Triple.md) | `[propext, Classical.choice, Quot.sound]` |

---

## Repository Structure

```text
.
├── README.md                                                     # Master verification ledger & reproduction guide
├── lakefile.lean                                                 # Lake build configuration (autoImplicit = false)
├── lake-manifest.json                                            # Pinned Mathlib4 manifest (9f7aa3a1...)
├── lean-toolchain                                                # Compiler pin: leanprover/lean4:v4.35.0-rc2
├── verify.bat                                                    # Windows full build & verification script
│
├── bountysolves/                                                 # Kernel-verified Lean 4 formalizations
│   ├── JSP_000301_GolombPowerful.lean
│   ├── JSP_000490_Erdos603_ForbiddenIntersectionTwo.lean
│   ├── JSP_000690_ErdosLovasz_3CriticalHypergraph.lean
│   ├── JSP_000698_FleischnerStiebitz_CyclePlusTriangles.lean
│   └── JSP_000746_TriangleFreeSchurTriple.lean
│
└── papers/                                                       # Formal mathematical papers & proof expositions
    ├── JSP-000301-Golomb-Powerful-Numbers.md
    ├── JSP-000490-Erdos-603-Forbidden-Intersection-Two.md
    ├── JSP-000690-Erdos-Lovasz-3Critical-Hypergraph.md
    ├── JSP-000698-Fleischner-Stiebitz-Cycle-Plus-Triangles.md
    └── JSP-000746-Erdos-Barber-Triangle-Free-Schur-Triple.md
```

---

## Reproduction & Verification

### Environment
- **Lean toolchain:** `leanprover/lean4:v4.35.0-rc2` (`lean-toolchain`)
- **Mathlib4 revision:** `9f7aa3a1327bbbc1716bdcedb64b2592e54b9bc7` (`lake-manifest.json`)

### Build & Per-File Verification Commands
```bash
git clone https://github.com/CreizyLabs/bounty_solves.git
cd bounty_solves
lake exe cache get
lake build
```

Individual file checks (with `#check` and `#print axioms` executed at the end of each file):
```bash
lake env lean -DautoImplicit=false bountysolves/JSP_000301_GolombPowerful.lean
lake env lean -DautoImplicit=false bountysolves/JSP_000490_Erdos603_ForbiddenIntersectionTwo.lean
lake env lean -DautoImplicit=false bountysolves/JSP_000690_ErdosLovasz_3CriticalHypergraph.lean
lake env lean -DautoImplicit=false bountysolves/JSP_000698_FleischnerStiebitz_CyclePlusTriangles.lean
lake env lean -DautoImplicit=false bountysolves/JSP_000746_TriangleFreeSchurTriple.lean
```

---

## Verified Axiom Audit Output & SHA-256 Digests

### `JSP-000301` (`SHA-256: 53374438EBD064CBD4126EF37993ADB250C9497C64F2C13E3970DC7AAD2062B3`)
```text
'JSP_000301.isPowerful_iff_isSqMulCube' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000301.jsp_000301_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000301.jsp_000301_disproved' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000301.jsp_000301_disproved_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `JSP-000490` (`SHA-256: C555FFC281C64C9AAB7FD0C142F350832723B48D816E1D95AF34BEFD73F28287`)
```text
'JSP_000490.erdos_rado_countable' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000490.jsp_000490_for_every_color_type' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000490.jsp_000490_no_uniform_cardinal_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `JSP-000690` (`SHA-256: F2799F5FC4DB6EFA59FD6BA1BAED12936ED0980DB8CE4EE0C8D980B4820A9264`)
```text
'JSP_000690.erdosLovasz9_isUniform3' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000690.erdosLovasz9_seven_regular' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000690.erdosLovasz9_isThreeChromaticCritical' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000690.jsp_000690_erdos_lovasz_fin9' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000690.jsp_000690_erdos_lovasz_solved' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `JSP-000698` (`SHA-256: 7A1F65E12117C59E26E1AE59722071324FB9345374FD0312A738198A9800704B`)
```text
'JSP_000698.alon_tarsi_list_coloring' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000698.totalEulerian_mod4_eq_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000698.jsp_000698_fleischner_stiebitz_3_choosable' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000698.jsp_000698_fleischner_stiebitz_3_colorable' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000698.jsp_000698_exact_3_colorable' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000698.jsp_000698_chromaticNumber_le_three' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `JSP-000746` (`SHA-256: AD23B035F793260F88EA3F35044D30AAB3E24CECF66824D8C2EB12A05DAFDF4F`)
```text
'JSP_000746.jsp_000746_fin18' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000746.jsp_000746_nat' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000746.jsp_000746_int' depends on axioms: [propext, Classical.choice, Quot.sound]
```

---

## Attribution

All Lean 4 formalizations and expositions in this repository are authored independently by **CreizyLabs** (`@CreizyLabs`). Original mathematical solutions are credited explicitly to their respective authors in each formal paper and in the ledger above.
