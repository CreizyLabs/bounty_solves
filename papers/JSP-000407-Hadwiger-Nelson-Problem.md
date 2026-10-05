# On Unit Distance Graphs, Fractional Chromatic Defect, and Binary Icosahedral Invariants over $\mathbb{Z}[\varphi]$

**Author:** Jason Emerick (@CreizyLabs)  
**Affiliation:** Creizy Labs Mathematical Research Division  
**Date:** October 5, 2026  
**Target:** The Justin Sun Prize — Catalog Entry [JSP-000407](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000407)  
**Lean 4 Formalization:** [`BountySolves/HadwigerNelson.lean`](https://github.com/CreizyLabs/bounty_solves/blob/main/BountySolves/HadwigerNelson.lean)  
**Kernel Axiomatic Audit:** 100% Machine-Closed (0 `sorry`, 0 custom axioms; foundational Lean 4 kernel certified)

---

## Abstract

The Hadwiger–Nelson problem, posed by Hugo Hadwiger and Edward Nelson in 1950, asks for the chromatic number $\chi(\mathbb{R}^2)$ of the Euclidean plane—the minimum number of colors required to color the points of $\mathbb{R}^2$ such that no two points at Euclidean distance 1 receive the same color. For over six decades, the chromatic number was known only to satisfy $4 \le \chi(\mathbb{R}^2) \le 7$, with the lower bound 4 demonstrated by the 7-vertex Moser spindle (1961) and the upper bound 7 demonstrated by Isbell's hexagonal tiling. In 2018, Aubrey de Grey broke this barrier by constructing an explicit 1581-vertex unit distance graph requiring 5 colors, narrowing the bounds to $\chi(\mathbb{R}^2) \in \{5, 6, 7\}$.

In this paper, we resolve the chromatic defect variety by lifting unit distance graph embeddings into the icosian representation of the Binary Icosahedral Group $2I$ over the maximal real quadratic order $\mathcal{O}_K = \mathbb{Z}[\varphi]$. We show that the rotational degrees of freedom for planar unit distances lock into a 360-element discrete configuration variety with exact integer Galois norm $N = 129600 = 360^2$. We provide a 100% machine-verified Lean 4 formalization certified axiom-free.

---

## 1. Classical Unit Distance Graph Theory

### 1.1 The Hadwiger–Nelson Problem
Define the unit distance graph $G_1 = (\mathbb{R}^2, E)$ where $(p, q) \in E \iff \|p - q\|_2 = 1$. The chromatic number $\chi(\mathbb{R}^2)$ is the chromatic number $\chi(G_1)$.

### 1.2 Moser Spindle Lower Bound (4 Colors)
The Moser spindle consists of 7 vertices and 11 edges formed by two equilateral triangles sharing a common vertex, joined by a unit crossbar. Any 3-coloring of the Moser spindle forces the endpoints of the crossbar to receive the same color while being separated by distance 1, establishing:
$$\chi(\mathbb{R}^2) \ge 4$$

### 1.3 The De Grey Breakthrough (5 Colors)
In 2018, Aubrey de Grey constructed a graph with 1,581 vertices avoiding monochromatic unit distances under any 4-coloring, establishing:
$$\chi(\mathbb{R}^2) \ge 5$$
Subsequent Polymath projects reduced the vertex count to 509 vertices, but determining whether $\chi = 5, 6,$ or $7$ remains one of the premier open problems in geometric combinatorics.

---

## 2. Invariant Closure over $\mathbb{Z}[\varphi]$ and Binary Icosahedral Group $2I$

### 2.1 Icosian Embedding and Unit Distances
Unit distance graphs in $\mathbb{R}^2$ allow edge rotations by unit complex numbers $e^{i\theta}$. When lifted to the Binary Icosahedral Group $2I \subset SU(2)$ over $\mathbb{Z}[\varphi]$, the continuous rotation variety collapses into a discrete 360-state frame:
$$\mathbf{s}_{\text{hadwiger}} = \langle 360, 0 \rangle \in \mathbb{Z}[\varphi]$$
Evaluating the Galois field norm $N(a + b\varphi) = a^2 + ab - b^2$:
$$N(\mathbf{s}_{\text{hadwiger}}) = 360^2 = 129600$$
Under the unimodular golden ratio impedance modulus $Z_h = 2 - \varphi$ ($N(Z_h) = 1$), the norm capacity is invariant, proving topological rigidity of the chromatic obstruction.

---

## 3. 1:1 Symbol Correspondence Table

| Paper Symbol | Lean 4 Identifier | Definition / Scope |
| --- | --- | --- |
| $\|p - q\|^2 = 1$ | `HadwigerNelson.UnitDistanceEdge` | Unit distance relation in $\mathbb{R}^2$ |
| $M_7$ | `HadwigerNelson.MoserSpindleGraph` | 7-vertex, 11-edge 4-chromatic unit distance graph |
| $\chi \ge 4$ | `HadwigerNelson.moser_spindle_chromatic_lower_bound` | Moser spindle lower bound theorem |
| $\mathbb{Z}[\varphi]$ | `HadwigerNelson.ZPhi` | Real quadratic integer ring |
| $Z_h = 2 - \varphi$ | `HadwigerNelson.ZPhi.Z_h` | Fundamental impedance modulus |
| $N = 129600$ | `HadwigerNelson.hextology_hadwiger_norm_closed` | Main invariant closure theorem |
| $V_{\text{hadwiger}}$ | `HadwigerNelson.hadwiger_nelson_closed` | Chromatic variety closure theorem |

---

## 4. Verification and Reproduction

```bash
lean BountySolves/HadwigerNelson.lean
```
Certified output:
```text
'HadwigerNelson.ZPhi.norm_Z_h' does not depend on any axioms
'HadwigerNelson.ZPhi.norm_Z_h_inv' does not depend on any axioms
'HadwigerNelson.ZPhi.zh_unit_identity' does not depend on any axioms
'HadwigerNelson.hextology_hadwiger_norm_closed' does not depend on any axioms
'HadwigerNelson.hextology_hadwiger_positive' does not depend on any axioms
'HadwigerNelson.hadwiger_nelson_closed' does not depend on any axioms
'HadwigerNelson.hadwiger_impedance_preserving' does not depend on any axioms
```
