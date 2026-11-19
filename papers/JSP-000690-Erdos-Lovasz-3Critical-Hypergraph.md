# An Explicit 7-Regular, 3-Uniform, 3-Chromatic-Critical Hypergraph on Nine Vertices (JSP-000690 / Erdős–Lovász 1974)

**Catalog Identifier:** `JSP-000690` ([The Justin Sun Prize Problem Bank](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0601-0700.md#JSP-000690))  
**Original Problem Reference:** Erdős Problem #834; P. Erdős and L. Lovász (1974), p. 282  
**Mathematical Area:** Graph Theory / Hypergraphs  
**Original Mathematical Solution:** Ruiliang Li, *On an Erdős–Lovász problem: 3-critical 3-graphs of minimum degree 7*, `arXiv:2512.24850` (2025)  
**Lean 4 Formalization & Exposition:** CreizyLabs (`bountysolves/JSP_000690_ErdosLovasz_3CriticalHypergraph.lean`)  
**Verification Environment:** Lean `4.35.0-rc2`, Mathlib4 (`9f7aa3a1327bbbc1716bdcedb64b2592e54b9bc7`)

---

## Abstract

In 1974, Paul Erdős and László Lovász asked whether there exists a $3$-uniform, $3$-chromatic-critical hypergraph with minimum vertex degree at least $7$. Following the affirmative resolution on $9$ vertices (`arXiv:2512.24850`), we exhibit an explicit **$7$-regular, $21$-edge, $3$-uniform hypergraph** $H$ on $V = \{0, 1, \dots, 8\}$ that is $3$-colorable, not $2$-colorable, and simultaneously **edge-critical** (deleting any edge yields a $2$-colorable hypergraph) and **vertex-critical** (deleting any vertex yields a $2$-colorable hypergraph). Every condition—uniformity, $7$-regularity, $3$-colorability, exhaustive non-$2$-colorability across all $2^9 = 512$ binary colorings via a depth-$9$ balanced binary tree, and all $21$ explicit edge-deletion $2$-coloring certificates—is verified unconditionally in the Lean 4 kernel without `sorry`, `admit`, `native_decide`, or custom axioms.

---

## 1. Problem Statement and Formal Definitions

### 1.1 Original Problem (`JSP-000690` / Erdős #834)
> *Is there a three-uniform, three-chromatic-critical hypergraph with minimum degree at least seven?*

### 1.2 Formal Definitions
Let $H \subseteq \mathcal{P}(V)$ be a finite hypergraph on a finite vertex set $V$.
1. **$k$-Uniformity (`JSP_000690.IsUniform`):** $|e| = k$ for every $e \in H$.
2. **Vertex Degree & Minimum Degree (`JSP_000690.vertexDegree`, `JSP_000690.HasMinDegreeAtLeast`):**
   $$d_H(v) = |\{e \in H \mid v \in e\}|, \qquad \delta(H) \ge d \iff \forall v \in V,\; d_H(v) \ge d.$$
3. **Proper Hypergraph Coloring (`JSP_000690.IsProperHypergraphColoring`, `JSP_000690.IsKColorable`):**
   A coloring $c : V \to \mathrm{Fin}\,k$ is *proper* (weak coloring) if no hyperedge $e \in H$ is monochromatic:
   $$\forall e \in H,\; \exists u, v \in e,\; c(u) \ne c(v).$$
4. **$3$-Chromatic-Criticality (`JSP_000690.IsThreeChromaticCritical`):**
   $H$ is $3$-colorable, not $2$-colorable, **edge-critical** ($\forall e \in H$, $H \setminus \{e\}$ is $2$-colorable), and **vertex-critical** ($\forall v \in V$, $\{e \in H \mid v \notin e\}$ is $2$-colorable).

### 1.3 Statement Correspondence Table

| Mathematical Property | Lean 4 Declaration in `bountysolves/JSP_000690_ErdosLovasz_3CriticalHypergraph.lean` |
| --- | --- |
| Explicit $21$-edge hypergraph on `Fin 9` | `JSP_000690.erdosLovasz9` |
| $3$-uniformity ($\forall e \in H,\; |e| = 3$) | `JSP_000690.erdosLovasz9_isUniform3` |
| $7$-regularity ($\forall v \in \mathrm{Fin}\,9,\; d_H(v) = 7$) | `JSP_000690.erdosLovasz9_seven_regular` |
| $3$-chromatic-criticality (edge- and vertex-critical) | `JSP_000690.erdosLovasz9_isThreeChromaticCritical` |
| Main existential theorem on `Fin 9` | `JSP_000690.jsp_000690_erdos_lovasz_fin9` |
| Main existential theorem over arbitrary finite types | `JSP_000690.jsp_000690_erdos_lovasz_solved` |

---

## 2. Explicit Construction and Proof

### 2.1 The $7$-Regular, $21$-Edge Hypergraph $H$ on $\{0, 1, \dots, 8\}$
Define $H$ as the set of $21$ distinct $3$-element subsets of $V = \{0, 1, 2, 3, 4, 5, 6, 7, 8\}$:
$$
\begin{aligned}
H = \bigl\{
&\{0,1,6\},\; \{0,2,4\},\; \{0,4,5\},\; \{0,4,6\},\; \{0,4,7\},\; \{0,5,6\},\; \{0,5,7\},\\
&\{1,2,8\},\; \{1,3,5\},\; \{1,3,6\},\; \{1,3,8\},\; \{1,5,6\},\; \{1,6,8\},\\
&\{2,3,7\},\; \{2,3,8\},\; \{2,4,7\},\; \{2,4,8\},\; \{2,7,8\},\\
&\{3,5,6\},\; \{3,7,8\},\; \{4,5,7\}
\bigr\}.
\end{aligned}
$$

### 2.2 Uniformity and $7$-Regularity
Each listed triple consists of three strictly increasing (hence distinct) vertices in $\{0, \dots, 8\}$, so $|e| = 3$ for all $e \in H$, and all $21$ triples are distinct. Direct incidence counting gives
$$d_H(v) = 7 \quad \text{for every } v \in \{0, 1, 2, 3, 4, 5, 6, 7, 8\},$$
consistent with $\sum_{v=0}^{8} d_H(v) = 9 \cdot 7 = 63 = 3 \cdot 21 = 3|H|$. Hence $\delta(H) = 7 \ge 7$.

### 2.3 $3$-Colorability ($\chi(H) \le 3$)
Define $c_3 : \{0, \dots, 8\} \to \{0, 1, 2\}$ by $c_3(v) = \lfloor v / 3 \rfloor$, partitioning $V$ into $\{0,1,2\}$, $\{3,4,5\}$, and $\{6,7,8\}$. None of $\{0,1,2\}$, $\{3,4,5\}$, $\{6,7,8\}$ belongs to $H$; therefore no hyperedge of $H$ is monochromatic under $c_3$.

### 2.4 Non-$2$-Colorability ($\chi(H) \ge 3$)
Every $2$-coloring $c : \{0, \dots, 8\} \to \{0, 1\}$ is encoded bijectively as a $9$-bit integer
$$m(c) = \sum_{v=0}^{8} c(v) \cdot 2^v \in \{0, 1, \dots, 511\},$$
with exact inverse $c(v) = \lfloor m(c) / 2^v \rfloor \bmod 2$. Exhaustive verification over all $512$ bitmasks (structured in Lean as a balanced binary tree `checkPow2 0 9` of depth $9$ with proven soundness Lemma `checkPow2_sound`) shows that for every $m \in \{0, \dots, 511\}$, at least one triple $e \in H$ satisfies $c(a) = c(b) = c(d)$. Thus $H$ is not $2$-colorable, and combined with Section 2.3 we have $\chi(H) = 3$.

### 2.5 Edge-Criticality and Vertex-Criticality
For each edge $e \in H$, the following explicit $9$-bit mask $m_e \in \{0, \dots, 511\}$ defines a $2$-coloring $c_e(v) = \lfloor m_e / 2^v \rfloor \bmod 2$ whose **only** monochromatic edge in $H$ is $e$, hence is a proper $2$-coloring of $H \setminus \{e\}$:

| Deleted Edge $e$ | Witness Mask $m_e$ | Color-1 Set $\{v : c_e(v)=1\}$ | Deleted Edge $e$ | Witness Mask $m_e$ | Color-1 Set $\{v : c_e(v)=1\}$ |
| --- | ---: | --- | --- | ---: | --- |
| $\{0,1,6\}$ | `199` | $\{0,1,2,6,7\}$ | $\{1,5,6\}$ | `230` | $\{1,2,5,6,7\}$ |
| $\{0,2,4\}$ | `31` | $\{0,1,2,3,4\}$ | $\{1,6,8\}$ | `45` | $\{0,2,3,5\}$ |
| $\{0,4,5\}$ | `198` | $\{1,2,6,7\}$ | $\{2,3,7\}$ | `143` | $\{0,1,2,3,7\}$ |
| $\{0,4,6\}$ | `166` | $\{1,2,5,7\}$ | $\{2,3,8\}$ | `210` | $\{1,4,6,7\}$ |
| $\{0,4,7\}$ | `155` | $\{0,1,3,4,7\}$ | $\{2,4,7\}$ | `214` | $\{1,2,4,6,7\}$ |
| $\{0,5,6\}$ | `154` | $\{1,3,4,7\}$ | $\{2,4,8\}$ | `139` | $\{0,1,3,7\}$ |
| $\{0,5,7\}$ | `92` | $\{2,3,4,6\}$ | $\{2,7,8\}$ | `27` | $\{0,1,3,4\}$ |
| $\{1,2,8\}$ | `216` | $\{3,4,6,7\}$ | $\{3,5,6\}$ | `124` | $\{2,3,4,5,6\}$ |
| $\{1,3,5\}$ | `47` | $\{0,1,2,3,5\}$ | $\{3,7,8\}$ | `39` | $\{0,1,2,5\}$ |
| $\{1,3,6\}$ | `218` | $\{1,3,4,6,7\}$ | $\{4,5,7\}$ | `15` | $\{0,1,2,3\}$ |
| $\{1,3,8\}$ | `228` | $\{2,5,6,7\}$ | | | |

Hence $H$ is $3$-chromatic edge-critical. Since every vertex $v \in V$ has degree $7 \ge 1$, there exists an edge $e_v \in H$ with $v \in e_v$; therefore $\{f \in H \mid v \notin f\} \subseteq H \setminus \{e_v\}$ is also $2$-colorable, proving that $H$ is vertex-critical as well. $\square$

---

## 3. Lean 4 Formalization and Verification Evidence

The complete formalization resides in [`bountysolves/JSP_000690_ErdosLovasz_3CriticalHypergraph.lean`](../bountysolves/JSP_000690_ErdosLovasz_3CriticalHypergraph.lean) (351 lines). All finite checks are executed inside Lean's kernel (`decide`, zero `native_decide`), with zero `sorry`, zero `admit`, and zero custom axioms.

### Exported Theorems
```lean
theorem JSP_000690.erdosLovasz9_isUniform3 : IsUniform 3 erdosLovasz9
theorem JSP_000690.erdosLovasz9_seven_regular : ∀ v : Fin 9, vertexDegree erdosLovasz9 v = 7
theorem JSP_000690.erdosLovasz9_isThreeChromaticCritical : IsThreeChromaticCritical erdosLovasz9

theorem JSP_000690.jsp_000690_erdos_lovasz_fin9 :
    ∃ H : Finset (Finset (Fin 9)),
      IsUniform 3 H ∧ HasMinDegreeAtLeast 7 H ∧ IsThreeChromaticCritical H

theorem JSP_000690.jsp_000690_erdos_lovasz_solved :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (H : Finset (Finset V)),
      Nonempty V ∧ IsUniform 3 H ∧ HasMinDegreeAtLeast 7 H ∧ IsThreeChromaticCritical H
```

### Reproduction and Axiom Audit
```bash
lake env lean bountysolves/JSP_000690_ErdosLovasz_3CriticalHypergraph.lean
```
Observed `#print axioms` output (exit code `0`, 0 warnings):
```text
'JSP_000690.erdosLovasz9_isUniform3' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000690.erdosLovasz9_seven_regular' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000690.erdosLovasz9_isThreeChromaticCritical' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000690.jsp_000690_erdos_lovasz_fin9' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000690.jsp_000690_erdos_lovasz_solved' depends on axioms: [propext, Classical.choice, Quot.sound]
```

---

## 4. References

1. P. Erdős and L. Lovász, *Problems and results on 3-chromatic hypergraphs and some related questions*, Infinite and Finite Sets, Colloq. Math. Soc. János Bolyai **10** (1974), 609–627.
2. R. Li, *On an Erdős–Lovász problem: 3-critical 3-graphs of minimum degree 7*, `arXiv:2512.24850` (2025).
3. Erdős Problems Database, [Problem #834](https://www.erdosproblems.com/834).
4. The Justin Sun Prize Problem Bank, entry `JSP-000690`, `problems/catalog-0601-0700.md`.
