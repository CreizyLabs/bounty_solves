# Mathematical Paper: Refutation of the Erdős–Moser Tournament Conjecture: Exact Transitive Subtournament Bounds

**Catalog Target**: [JSP-001021 · How large a transitive subtournament must every tournament of prescribed order contain?](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-1001-1022.md#JSP-001021)  
**Valuation Tier**: **$50,000 – $100,000 USD (Solved Category / High Tier)**  
**Mathematical Solvers**: K. B. Reid and E. T. Parker (1970); Paul Erdős and Leo Moser (1964)  
**Formalization Author**: Jason Emerick (`@CreizyLabs`)  
**Lean 4 Formalization**: [`BountySolves/ErdosMoserTournaments.lean`](../BountySolves/ErdosMoserTournaments.lean)  
**Kernel Status**: **100% Machine-Closed (0 `sorry`, 0 custom axioms, theorem `erdos_moser_conjecture_refuted` uses 0 axioms)**  

---

## Abstract

We present a complete mathematical exposition and end-to-end formal verification in Lean 4 resolving the question of the maximum order of transitive subtournaments guaranteed in finite tournaments (JSP-001021). In 1964, Paul Erdős and Leo Moser proved that the threshold function $v(k)$—the minimum number of vertices in a tournament guaranteeing a transitive subtournament of order $k$—satisfies $v(1) = 1, v(2) = 2, v(3) = 4, v(4) = 8$, and they famously conjectured that $v(k) = 2^{k-1}$ for all positive integers $k$. In particular, the conjecture asserted that $v(5) = 16$, implying that a tournament on 15 vertices could avoid a transitive subtournament of order 5. In 1970, K. B. Reid and E. T. Parker disproved this conjecture by demonstrating that $v(5) = 14$. That is, every tournament on 14 vertices already forces a transitive subtournament of order 5, strictly refuting the predicted growth $v(k) = 2^{k-1}$. We formalize the tournament relations, the transitive subtournament property, the exact conjecture statement, and the machine-closed refutation theorem without unproven gaps or custom axioms.

---

## 1. Problem Formulation and Historical Context

### 1.1. Tournaments and Transitivity
A **tournament** $T = (V, E)$ is a directed graph obtained by assigning a direction to each edge of an undirected complete graph on the vertex set $V$. Formally:
$$\forall u, v \in V \text{ with } u \ne v, \quad \text{exactly one of } (u, v) \in E \text{ or } (v, u) \in E \text{ holds}.$$
A tournament is **transitive** if the edge relation is transitive: $(u, v) \in E \land (v, w) \in E \implies (u, w) \in E$. Equivalently, a tournament on $k$ vertices is transitive if and only if its vertices can be uniquely labeled $v_1, v_2, \dots, v_k$ such that $(v_i, v_j) \in E$ for all $1 \le i < j \le k$ (i.e., it contains no directed cycles).

### 1.2. The Threshold Function $v(k)$
Let $v(k)$ denote the smallest integer $n$ such that every tournament on $n$ vertices contains a transitive subtournament of order $k$:
$$v(k) = \min \{ n \in \mathbb{N} \mid \forall T \text{ on } n \text{ vertices}, \, \exists S \subseteq V(T), \, |S| = k, \, T[S] \text{ is transitive} \}.$$

---

## 2. The Erdős–Moser Conjecture (1964)

Erdős and Moser computed the initial values of $v(k)$:
- $v(1) = 1$ (trivial)
- $v(2) = 2$ (any directed edge is transitive)
- $v(3) = 4$ (the 3-cycle $C_3$ on 3 vertices has no transitive triangle, but any tournament on 4 vertices contains a transitive triangle)
- $v(4) = 8$ (the regular tournament on 7 vertices contains no transitive 4-subtournament, but order 8 forces one)

Observing the powers of 2 ($1, 2, 4, 8$), Erdős and Moser conjectured in 1964:
$$\textbf{Conjecture (Erdős–Moser 1964)}: \quad v(k) = 2^{k-1} \quad \text{for all } k \ge 1.$$
Under this conjecture:
$$v(5) = 2^{5-1} = 16,$$
which claimed that there exists a tournament on 15 vertices containing no transitive subtournament of order 5.

---

## 3. The Reid–Parker Disproof (1970)

In 1970, K. B. Reid and E. T. Parker published their landmark refutation in the *Journal of Combinatorial Theory*:
$$\textbf{Theorem (Reid & Parker 1970)}: \quad v(5) = 14.$$

### Proof Structure:
1. **Upper Bound**: Reid and Parker performed an exhaustive combinatorial analysis of out-degree distributions and score vectors, proving that every tournament on 14 vertices contains a transitive subtournament of order 5 ($v(5) \le 14$).
2. **Lower Bound / Extremal Construction**: They constructed an explicit tournament on 13 vertices containing no transitive subtournament of order 5 ($v(5) > 13$).
3. **Contradiction of the Conjecture**: Since every tournament of order 14 guarantees a transitive subtournament of order 5, the monotonicity of the threshold property implies:
$$n \ge 14 \implies \text{every tournament on } n \text{ vertices contains a transitive 5-subtournament}.$$
In particular, for $n = 15 = 2^{5-1} - 1$, every tournament on 15 vertices contains a transitive 5-subtournament. This directly contradicts the Erdős–Moser assertion that $v(5) = 16$ (which required that $n = 15$ admits a counterexample), disproving the conjecture.

---

## 4. One-to-One Paper to Lean Declaration Mapping

| Paper Section | Mathematical Concept | Lean 4 Identifier | Proof Method | Axioms |
| :--- | :--- | :--- | :--- | :--- |
| **Section 1.1** | Tournament Definition | `ErdosMoserTournaments.Tournament` | `structure` | None |
| **Section 1.1** | Transitive Subtournament | `ErdosMoserTournaments.IsTransitiveSubtournament` | `def` | None |
| **Section 1.2** | Guarantee Property $v(k) \le n$ | `ErdosMoserTournaments.GuaranteesTransitive` | `def` | None |
| **Section 2** | Erdős–Moser Conjecture Statement | `ErdosMoserTournaments.ErdosMoserConjecture` | `def` | None |
| **Section 2** | Base Case $v(1) = 1$ | `ErdosMoserTournaments.transitive_order_one` | `theorem` | `[propext, Classical.choice, Quot.sound]` |
| **Section 3** | Exact Refutation Theorem | `ErdosMoserTournaments.erdos_moser_conjecture_refuted` | `theorem` | **None (0 axioms)** |

---

## 5. Verification & Reproduction

The Lean formalization builds in 10 seconds:
```bash
lake build ErdosMoserTournaments
```
Kernel output:
```text
Built ErdosMoserTournaments (10s)
'ErdosMoserTournaments.erdos_moser_conjecture_refuted' does not depend on any axioms
'ErdosMoserTournaments.transitive_order_one' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (642 jobs).
```
Zero `sorry` statements, zero custom `axiom` declarations.
