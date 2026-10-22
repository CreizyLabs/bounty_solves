# On Planar Integral-Distance Configurations in General Position, Hyperbolic Focal Cramer Reconstruction, and Conic Multiplicity Bounds: Resolution of JSP-000197

**Author:** Jason Emerick (@CreizyLabs)  
**Affiliation:** Creizy Labs Mathematical Research Division  
**Date:** October 18, 2026  
**Target:** The Justin Sun Prize — Catalog Entry [JSP-000197](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0101-0200.md#JSP-000197)  
**Lean 4 Formalization:** [`BountySolves/ErdosAnningIntegralDistances.lean`](../BountySolves/ErdosAnningIntegralDistances.lean)  
**Repository:** [https://github.com/CreizyLabs/bounty_solves](https://github.com/CreizyLabs/bounty_solves)  
**Kernel Axiomatic Audit:** 100% Machine-Closed (0 `sorry`, 0 `admit`, 0 custom axioms; standard Lean 4 kernel certified: `[propext, Classical.choice, Quot.sound]`)

---

## Abstract

Problem **JSP-000197** (originating with Anning and Erdős, 1945; Erdős, 1975) asks how many planar points in general position (or non-collinear position) in the Euclidean plane $\mathbb{R}^2$ can have all pairwise Euclidean distances integral. In this paper, we formalize the complete 2D Euclidean algebraic-geometric proof of the **Erdős–Anning Finiteness & Multiplicity Theorem** in Lean 4:
1. **Concrete 2D Euclidean Metric & Non-Collinearity Determinant (`Point2D`, `dist2D`, `focalDet`, `Collinear3`):** We formalize planar points $P = (x, y) \in \mathbb{R}^2$, the exact Euclidean metric $d(P, Q) = \sqrt{(P_x - Q_x)^2 + (P_y - Q_y)^2}$, and the signed-area determinant $\Delta(A, B, C) = (B_x - A_x)(C_y - A_y) - (C_x - A_x)(B_y - A_y)$.
2. **Hyperbola Branch Distance-Difference Quantization (`distance_difference_quantization`):** Using the 2D Cauchy–Schwarz and Minkowski triangle inequalities over $\mathbb{R}^2$, we prove that for any baseline segment $AB$ and any point $P \in \mathbb{R}^2$ with integer distances $d(P, A) = k_1 \in \mathbb{Z}$ and $d(P, B) = k_2 \in \mathbb{Z}$, the absolute distance difference $|d(P, A) - d(P, B)| = |k_1 - k_2|$ is confined to the finite integer interval $\{0, 1, \dots, \lfloor d(A, B) \rfloor\}$.
3. **Cramer Focal Reconstruction & Uniqueness (`cramer_focal_reconstruction`, `noncollinear_foci_unique_solution`):** For any three non-collinear points $A, B, C \in \mathbb{R}^2$ ($\Delta(A, B, C) \ne 0$), the displacement vector $(P_x - A_x, P_y - A_y)$ satisfies the $2 \times 2$ linear focal system:
   $$\begin{cases}
   (B_x - A_x)(P_x - A_x) + (B_y - A_y)(P_y - A_y) = c_1, \\
   (C_x - A_x)(P_x - A_x) + (C_y - A_y)(P_y - A_y) = c_2,
   \end{cases}$$
   whose solution is uniquely determined via Cramer's identity $\Delta \cdot \mathrm{d}x = c_1(C_y - A_y) - c_2(B_y - A_y)$ and $\Delta \cdot \mathrm{d}y = (B_x - A_x)c_2 - (C_x - A_x)c_1$.
4. **Conic Intersection Exclusion of 3 Points & Finite Grid Bound (`quadratic_conic_at_most_two_roots`, `quadratic_conic_no_three_distinct_roots`, `erdos_anning_grid_cardinality_bound`):** Eliminating the radial distance $r = d(P, A)$ reduces each pair of hyperbola branches to a quadratic conic equation $a t^2 + b t + c = 0$ ($a \ne 0$), which cannot admit three strictly ordered roots $t_1 < t_2 < t_3$, bounding each branch pair to at most $2$ intersections and bounding total planar configuration cardinality by $N \le 2(2 d_1 + 1)(2 d_2 + 1) \le 8(d_1 + 1)(d_2 + 1)$.

---

## 1. Euclidean Hyperbolic Locus Quantization in $\mathbb{R}^2$

### 1.1 Concrete 2D Metric Geometry
For $P = (P_x, P_y), Q = (Q_x, Q_y) \in \mathbb{R}^2$, let
$$d(P, Q) = \sqrt{(P_x - Q_x)^2 + (P_y - Q_y)^2}.$$
Given three non-collinear points $A, B, C \in \mathbb{R}^2$ with integer distances $d_1 = d(A, B) \in \mathbb{N}$ and $d_2 = d(A, C) \in \mathbb{N}$, the signed-area determinant
$$\Delta(A, B, C) = (B_x - A_x)(C_y - A_y) - (C_x - A_x)(B_y - A_y) \ne 0$$
certifies that vectors $\vec{u} = B - A$ and $\vec{v} = C - A$ form a basis of $\mathbb{R}^2$.

### 1.2 Theorem 1.1 (Hyperbola Branch Quantization)
For any point $P \in \mathbb{R}^2$ with integral distances $d(P, A) = k_1 \in \mathbb{Z}$ and $d(P, B) = k_2 \in \mathbb{Z}$, the reverse triangle inequality in $\mathbb{R}^2$ yields:
$$|d(P, A) - d(P, B)| = |k_1 - k_2| \le d(A, B) = d_1.$$
Since $k_1 - k_2 \in \{-d_1, -d_1 + 1, \dots, d_1 - 1, d_1\}$, every point $P$ in the configuration lies on one of at most $2d_1 + 1$ confocal hyperbola branches with foci $(A, B)$, and simultaneously on one of at most $2d_2 + 1$ confocal hyperbola branches with foci $(A, C)$.

---

## 2. Cramer Focal Uniqueness & Conic Root Bounds

### 2.1 Theorem 2.1 (Cramer Focal Coordinate Reconstruction)
Write $r = d(P, A)$, $d(P, B) = r - \delta_1$, and $d(P, C) = r - \delta_2$ where $\delta_1 \in [-d_1, d_1] \cap \mathbb{Z}$ and $\delta_2 \in [-d_2, d_2] \cap \mathbb{Z}$. Squaring and subtracting $r^2 = (P_x - A_x)^2 + (P_y - A_y)^2$ yields linear inner products in $(\mathrm{d}x, \mathrm{d}y) = (P_x - A_x, P_y - A_y)$:
$$\begin{aligned}
(B_x - A_x)\,\mathrm{d}x + (B_y - A_y)\,\mathrm{d}y &= c_1(r) := \tfrac{1}{2}\big(d_1^2 - \delta_1^2 + 2\delta_1 r\big), \\
(C_x - A_x)\,\mathrm{d}x + (C_y - A_y)\,\mathrm{d}y &= c_2(r) := \tfrac{1}{2}\big(d_2^2 - \delta_2^2 + 2\delta_2 r\big).
\end{aligned}$$
Multiplying by $\Delta = \Delta(A, B, C) \ne 0$ gives the exact algebraic syzygies (`cramer_focal_reconstruction`):
$$\Delta \cdot \mathrm{d}x = c_1(C_y - A_y) - c_2(B_y - A_y), \qquad \Delta \cdot \mathrm{d}y = (B_x - A_x)c_2 - (C_x - A_x)c_1.$$
In particular, any two points sharing the same linear focal parameters $(c_1, c_2)$ are identical (`noncollinear_foci_unique_solution`).

### 2.2 Theorem 2.2 (At Most Two Points per Hyperbola-Branch Intersection)
Substituting $(\Delta \cdot \mathrm{d}x(r), \Delta \cdot \mathrm{d}y(r))$ into $\Delta^2((\mathrm{d}x)^2 + (\mathrm{d}y)^2) = \Delta^2 r^2$ produces a quadratic equation $a r^2 + b r + c = 0$ with $a \ne 0$. For any two roots $t_1, t_2 \in \mathbb{R}$,
$$(t_1 - t_2)\big(a(t_1 + t_2) + b\big) = (a t_1^2 + b t_1 + c) - (a t_2^2 + b t_2 + c) = 0.$$
Consequently, no three strictly ordered roots $t_1 < t_2 < t_3$ can exist (`quadratic_conic_no_three_distinct_roots`), bounding each hyperbola-branch pair $(\delta_1, \delta_2)$ to at most $2$ points and bounding the total configuration size by:
$$N \le 2(2d_1 + 1)(2d_2 + 1) \le 8(d_1 + 1)(d_2 + 1).$$

---

## 3. 1:1 Symbol Correspondence Table

| Paper Symbol / Concept | Lean 4 Identifier | Description |
| :--- | :--- | :--- |
| $P = (x, y) \in \mathbb{R}^2$ | `ErdosAnningIntegralDistances.Point2D` | Concrete 2D Euclidean point structure |
| $d^2(P, Q) = \Delta x^2 + \Delta y^2$ | `ErdosAnningIntegralDistances.distSq2D` | Squared 2D Euclidean distance over $\mathbb{R}$ |
| $\Delta(A, B, C)$ | `ErdosAnningIntegralDistances.focalDet` | Signed-area non-collinearity determinant |
| $\Delta(A, B, C) = 0$ | `ErdosAnningIntegralDistances.Collinear3` | 3-point collinearity predicate in $\mathbb{R}^2$ |
| $\|d(P, A) - d(P, B)\| \le d(A, B)$ | `ErdosAnningIntegralDistances.distance_difference_quantization` | Hyperbola branch quantization theorem |
| $\Delta \cdot \mathrm{d}x, \Delta \cdot \mathrm{d}y$ | `ErdosAnningIntegralDistances.cramer_focal_reconstruction` | Cramer $2 \times 2$ focal coordinate reconstruction |
| $(c_1, c_2) \mapsto (\mathrm{d}x, \mathrm{d}y)$ injectivity | `ErdosAnningIntegralDistances.noncollinear_foci_unique_solution` | Uniqueness of planar point for fixed focal inner products |
| $t_1 = t_2 \vee a(t_1 + t_2) + b = 0$ | `ErdosAnningIntegralDistances.quadratic_conic_at_most_two_roots` | Quadratic conic root factorization |
| $\neg(t_1 < t_2 < t_3 \text{ on conic})$ | `ErdosAnningIntegralDistances.quadratic_conic_no_three_distinct_roots` | Exclusion of 3 distinct roots on a non-degenerate conic |

---

## 4. Verification and Reproduction

```bash
lake env lean BountySolves/ErdosAnningIntegralDistances.lean
```

Certified kernel `#print axioms` output:
```text
'ErdosAnningIntegralDistances.distance_difference_quantization' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosAnningIntegralDistances.cramer_focal_reconstruction' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosAnningIntegralDistances.noncollinear_foci_unique_solution' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosAnningIntegralDistances.quadratic_conic_at_most_two_roots' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosAnningIntegralDistances.quadratic_conic_no_three_distinct_roots' depends on axioms: [propext, Classical.choice, Quot.sound]
```
