# An Unconditional Formal Proof of the Fleischner–Stiebitz Theorem: 3-Choosability and 3-Colorability of Cycle-Plus-Triangles Graphs (JSP-000698 / Erdős Problem #842)

**Catalog Identifier:** `JSP-000698` ([The Justin Sun Prize Problem Bank](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0601-0700.md#JSP-000698))  
**Original Problem Reference:** Erdős Problem #842 (Cycle-Plus-Triangles Conjecture; posed by D. Z. Du, D. F. Hsu, F. K. Hwang and strengthened by P. Erdős)  
**Mathematical Area:** Graph Theory / Chromatic Number / Algebraic Combinatorics  
**Original Mathematical Solution:** H. Fleischner and M. Stiebitz, *A solution to a colouring problem of P. Erdős*, Discrete Math. **101** (1992), 39–48  
**Lean 4 Formalization & Exposition:** CreizyLabs (`bountysolves/JSP_000698_FleischnerStiebitz_CyclePlusTriangles.lean`)  
**Verification Environment:** Lean `4.35.0-rc2`, Mathlib4 (`9f7aa3a1327bbbc1716bdcedb64b2592e54b9bc7`)

---

## Abstract

Catalog entry `JSP-000698` (Erdős Problem #842) asks whether every graph formed by taking the union of $n$ pairwise vertex-disjoint triangles and a spanning Hamilton cycle on their $3n$ vertices is $3$-colorable. Following the algebraic framework of Alon–Tarsi (1992) and Fleischner–Stiebitz (1992), we present a complete, self-contained proof of the strictly stronger **3-choosability** theorem: every cycle-plus-triangles graph (whether or not any triangle edge overlaps a cycle edge, and every subgraph thereof) admits a proper list coloring from arbitrary lists $L(v)$ of size $|L(v)| \ge 3$, and in particular satisfies $\chi(G) \le 3$. Our proof derives the general Alon–Tarsi list-coloring theorem from Mathlib's Combinatorial Nullstellensatz, factors the total Eulerian subdigraph count of the canonical $2$-regular orientation over triangle subsets $S \subseteq \{0, \dots, n-1\}$, evaluates the empty-subset contribution as $2$, and establishes $4 \mid N(S)$ for every nonempty $S$ via a direct reduction to the Chevalley–Warning theorem over $\mathbb{F}_2 = \mathrm{ZMod}\,2$. The entire proof is verified in Lean 4 with zero `sorry`, zero `admit`, and strictly `[propext, Classical.choice, Quot.sound]`.

---

## 1. Problem Statement and Formal Definitions

### 1.1 Original Problem (`JSP-000698` / Erdős #842)
> *Is every graph formed by vertex-disjoint triangles and a spanning Hamilton cycle three-colorable?*

### 1.2 Formal Definitions in Lean 4

In `bountysolves/JSP_000698_FleischnerStiebitz_CyclePlusTriangles.lean`:

1. **Cycle-plus-triangles graph (`JSP_000698.IsExactCyclePlusTriangles` and `JSP_000698.IsCyclePlusTriangles`):**
   A simple graph $G$ on a vertex type $V$ satisfies `IsExactCyclePlusTriangles n G` if there exist bijections $\mathrm{cyc} : \mathrm{Fin}(3n) \simeq V$ (the spanning Hamilton cycle) and $\mathrm{tri} : \mathrm{Fin}\,n \times \mathrm{Fin}\,3 \simeq V$ (partitioning $V$ into $n$ vertex-disjoint triangles) such that for all $u, v \in V$,
   $$G.\mathrm{Adj}\;u\;v \iff u \ne v \land \Bigl((\mathrm{cyc}^{-1}(u) + 1) \equiv \mathrm{cyc}^{-1}(v) \pmod{3n} \;\lor\; (\mathrm{cyc}^{-1}(v) + 1) \equiv \mathrm{cyc}^{-1}(u) \pmod{3n} \;\lor\; \pi_1(\mathrm{tri}^{-1}(u)) = \pi_1(\mathrm{tri}^{-1}(v))\Bigr).$$
   The weaker subgraph predicate `IsCyclePlusTriangles n G` replaces $\iff$ by $\implies$; hence `IsExactCyclePlusTriangles n G → IsCyclePlusTriangles n G`.
2. **3-Colorability & Chromatic Number:** Standard Mathlib `Nonempty (G.Coloring (Fin 3))` and `G.chromaticNumber ≤ 3`.

### 1.3 Statement Correspondence Table

| Mathematical Result | Lean 4 Declaration in `bountysolves/JSP_000698_FleischnerStiebitz_CyclePlusTriangles.lean` |
| --- | --- |
| General Alon–Tarsi list-coloring theorem (arbitrary color type $\alpha$) | `JSP_000698.alon_tarsi_list_coloring` |
| Parity theorem $\mathrm{totalEulerian}(D(\pi)) \equiv 2 \pmod 4$ | `JSP_000698.totalEulerian_mod4_eq_two` |
| 3-choosability of cycle-plus-triangles graphs | `JSP_000698.jsp_000698_fleischner_stiebitz_3_choosable` |
| 3-colorability (`Nonempty (G.Coloring (Fin 3))`) | `JSP_000698.jsp_000698_fleischner_stiebitz_3_colorable` |
| Exact-union 3-colorability (`IsExactCyclePlusTriangles`) | `JSP_000698.jsp_000698_exact_3_colorable` |
| Chromatic number bound `G.chromaticNumber ≤ 3` | `JSP_000698.jsp_000698_chromaticNumber_le_three` |

---

## 2. Complete Mathematical Proof

### Theorem 2.1 (Alon–Tarsi Theorem via Combinatorial Nullstellensatz)
Let $D = (V, A, \mathrm{src}, \mathrm{dst})$ be a finite directed multigraph, and define its signed Eulerian subdigraph count
$$\sigma(D) = \sum_{\substack{S \subseteq A \\ S\text{ Eulerian}}} (-1)^{|S|} = EE(D) - EO(D),$$
where $S \subseteq A$ is *Eulerian* if $d^+_S(v) = d^-_S(v)$ for every $v \in V$. If $\sigma(D) \ne 0$, then for every color type $\alpha$ and every list assignment $L : V \to \mathrm{Finset}\,\alpha$ with $|L(v)| > d^+_D(v)$ for all $v \in V$, there exists $c : V \to \alpha$ such that $c(v) \in L(v)$ for all $v \in V$ and $c(\mathrm{src}(a)) \ne c(\mathrm{dst}(a))$ for all $a \in A$.

**Proof.**
First encode the finite union $U = \bigcup_{v \in V} L(v)$ injectively into $\mathbb{Z}$, reducing to $\alpha = \mathbb{Z}$. Consider the graph polynomial in $\mathbb{Z}[X_v : v \in V]$:
$$P(X) = \prod_{a \in A} \bigl(X_{\mathrm{src}(a)} - X_{\mathrm{dst}(a)}\bigr) = \sum_{S \subseteq A} (-1)^{|S|} \prod_{a \in S} X_{\mathrm{dst}(a)} \prod_{a \in A \setminus S} X_{\mathrm{src}(a)}.$$
Every summand has total degree $|A|$, so $\deg(P) \le |A|$. The exponent of $X_v$ in the term for $S$ is $d^-_S(v) + (d^+_D(v) - d^+_S(v))$, which equals $d^+_D(v)$ for all $v \in V$ if and only if $S$ is Eulerian. Hence the coefficient of $\prod_{v \in V} X_v^{d^+_D(v)}$ in $P$ is precisely $\sigma(D) \ne 0$, forcing $\deg(P) = |A| = \sum_{v} d^+_D(v)$. By the Combinatorial Nullstellensatz (`MvPolynomial.combinatorial_nullstellensatz_exists_eval_nonzero`), there exists $c \in \prod_{v} L(v)$ with $P(c) \ne 0$, hence $c(\mathrm{src}(a)) \ne c(\mathrm{dst}(a))$ for every arc $a \in A$. $\square$

### Lemma 2.2 (Canonical $2$-Regular Orientation and Modulo-$4$ Criterion)
For $n \ge 1$ and any bijection $\pi : \mathrm{Fin}\,n \times \mathrm{Fin}\,3 \simeq \mathrm{Fin}(3n)$, define the directed multigraph $D(\pi)$ on $V = \mathrm{Fin}(3n)$ with $6n$ arcs:
- $3n$ cycle arcs $i \to (i+1) \bmod 3n$, and
- $3n$ triangle arcs $\pi(t, j) \to \pi(t, (j+1) \bmod 3)$ for $(t, j) \in \mathrm{Fin}\,n \times \mathrm{Fin}\,3$.

Every vertex has $d^+_{D(\pi)}(v) = d^-_{D(\pi)}(v) = 2$. Since $|A| = 6n$ is even, complementation $S \mapsto A \setminus S$ is a fixed-point-free, parity-preserving involution on both the even Eulerian subdigraphs $EE$ and the odd Eulerian subdigraphs $EO$. Therefore $2 \mid |EE|$ and $2 \mid |EO|$. Consequently, if $|EE| + |EO| \equiv 2 \pmod 4$, then $|EE| \ne |EO|$ and hence $\sigma(D(\pi)) = |EE| - |EO| \ne 0$. $\square$

### Lemma 2.3 (Triangle Factorization and Subset Expansion)
For a subset $A \subseteq \mathrm{Fin}(3n)$ of cycle arcs and vertex $v \in \mathrm{Fin}(3n)$, define the cycle balance
$$\mathrm{bal}_A(v) = \mathbf{1}_{(v-1) \in A} - \mathbf{1}_{v \in A} \in \{-1, 0, 1\}.$$
A subdigraph $(A, (B_t)_{t < n})$ of $D(\pi)$ is Eulerian if and only if for each triangle $t$ and each $j \in \mathrm{Fin}\,3$, the local triangle balance $\mathbf{1}_{j \in B_t} - \mathbf{1}_{(j-1) \in B_t}$ equals $\mathrm{bal}_A(\pi(t, j))$. For any prescribed triple $d \in \{-1, 0, 1\}^3$, let $M(d)$ be the number of subsets $B \subseteq \mathrm{Fin}\,3$ realizing $d$. Direct inspection of all $27$ triples in $\{-1, 0, 1\}^3$ yields the exact pointwise identity:
$$M(d) = \mathbf{1}_{\forall j,\, d_j = 0} + \mathbf{1}_{d_0 + d_1 + d_2 = 0}.$$
Expanding $\prod_{t=0}^{n-1} M(\mathrm{bal}_A(\pi(t, \cdot)))$ over subsets $S \subseteq \mathrm{Fin}\,n$ yields
$$|EE| + |EO| = \sum_{S \subseteq \mathrm{Fin}\,n} N(S),$$
where $N(S)$ counts cycle subsets $A \subseteq \mathrm{Fin}(3n)$ satisfying:
1. $\sum_{j=0}^{2} \mathrm{bal}_A(\pi(t, j)) = 0$ for all $t \in S$, and
2. $\mathrm{bal}_A(\pi(t, j)) = 0$ for all $t \notin S$ and $j \in \mathrm{Fin}\,3$.

For $S = \emptyset$, $\mathrm{bal}_A(v) = 0$ for all $v$ forces $\mathbf{1}_{(v-1) \in A} = \mathbf{1}_{v \in A}$ around the $3n$-cycle, so only $A = \emptyset$ and $A = \mathrm{Fin}(3n)$ qualify; hence $N(\emptyset) = 2$. $\square$

### Theorem 2.4 (Divisibility by $4$ via Chevalley–Warning over $\mathbb{F}_2$)
For every nonempty $S \subseteq \mathrm{Fin}\,n$, we have $4 \mid N(S)$.

**Proof.**
Since $\mathrm{bal}_{A^c}(v) = -\mathrm{bal}_A(v)$, complementation $A \mapsto A^c$ is an involution on the set counted by $N(S)$ swapping $0 \in A$ with $0 \notin A$. Thus $N(S) = 2 N_0(S)$, where $N_0(S)$ counts valid subsets $A$ with $0 \notin A$. It remains to prove $2 \mid N_0(S)$.

Identify subsets $A \subseteq \mathrm{Fin}(3n) \setminus \{0\}$ with vectors $x \in \mathbb{F}_2^{\sigma}$ where $\sigma = \{v \in \mathrm{Fin}(3n) \mid v \ne 0\}$ has $|\sigma| = 3n - 1$, extended by $x_0 = 0$. Over $\mathbb{F}_2$, two $3$-bit vectors $(a_0, a_1, a_2)$ and $(b_0, b_1, b_2)$ have equal integer Hamming weight $a_0 + a_1 + a_2 = b_0 + b_1 + b_2 \in \mathbb{Z}$ if and only if both their linear sums and their second elementary symmetric polynomials coincide in $\mathbb{F}_2$:
$$P(a, b) := \sum_{j=0}^{2}(a_j + b_j) = 0 \quad \text{and} \quad Q(a, b) := e_2(a_0, a_1, a_2) + e_2(b_0, b_1, b_2) = 0.$$
Choose one vertex $t_0 \in S$, and consider the system of polynomials in $\mathbb{F}_2[\sigma]$:
- For each $t \notin S$ and $j \in \mathrm{Fin}\,3$: $L_{t,j}(x) = x_{\pi(t,j)-1} + x_{\pi(t,j)}$ (degree $\le 1$; total $3(n - |S|)$ equations).
- For each $t \in S \setminus \{t_0\}$: $P_t(x)$ (degree $\le 1$) and $Q_t(x)$ (degree $\le 2$).

We verify two claims:
1. **Exact solution bijection:** Every $x$ in the zero locus of this reduced system automatically satisfies $P_{t_0}(x) = 0$ and $Q_{t_0}(x) = 0$. Indeed, summing $x_{v-1} + x_v$ over all $v \in \mathrm{Fin}(3n)$ vanishes identically in $\mathbb{F}_2$, and every $t \ne t_0$ satisfies $P_t(x) = 0$, forcing $P_{t_0}(x) = 0$. Likewise, summing $\mathrm{bal}_A(v)$ in $\mathbb{Z}$ over all $v \in \mathrm{Fin}(3n)$ vanishes identically, and every $t \ne t_0$ already has $\sum_j \mathrm{bal}_A(\pi(t, j)) = 0$ in $\mathbb{Z}$; hence $\sum_j \mathrm{bal}_A(\pi(t_0, j)) = 0$ in $\mathbb{Z}$, which implies $Q_{t_0}(x) = 0$. Thus the number of $\mathbb{F}_2$-solutions equals $N_0(S)$ exactly.
2. **Degree bound:** The sum of total degrees of all equations in the reduced system is at most
   $$3(n - |S|) + (|S| - 1) + 2(|S| - 1) = 3n - 3 < 3n - 1 = |\sigma|.$$
By the Chevalley–Warning theorem (`FiniteField.char_dvd_card_solutions_of_sum_lt` with $K = \mathbb{F}_2$, $p = 2$), $2 \mid N_0(S)$, and hence $4 \mid 2 N_0(S) = N(S)$. $\square$

### Corollary 2.5 (Fleischner–Stiebitz 3-Choosability & 3-Colorability)
Combining Lemma 2.3 and Theorem 2.4 gives $|EE| + |EO| = 2 + \sum_{S \ne \emptyset} N(S) \equiv 2 \pmod 4$. By Lemma 2.2, $\sigma(D(\pi)) \ne 0$. Since every vertex of $D(\pi)$ has outdegree $2 < 3$, Theorem 2.1 produces a proper list coloring of $G$ from any lists of size $\ge 3$ (handling $n = 0$ vacuously). Taking $L(v) = \mathrm{Fin}\,3$ yields `Nonempty (G.Coloring (Fin 3))` and `G.chromaticNumber ≤ 3`. $\square$

---

## 3. Lean 4 Formalization and Verification Evidence

The complete formalization resides in [`bountysolves/JSP_000698_FleischnerStiebitz_CyclePlusTriangles.lean`](../bountysolves/JSP_000698_FleischnerStiebitz_CyclePlusTriangles.lean) (1,462 lines), depending only on Mathlib (`Mathlib.Combinatorics.Nullstellensatz`, `Mathlib.FieldTheory.ChevalleyWarning`, and core combinatorics), with zero `sorry`, zero `admit`, zero `native_decide`, and zero custom axioms.

### Exported Theorems
```lean
theorem JSP_000698.alon_tarsi_list_coloring {V A α : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [DecidableEq α] (src dst : A → V)
    (hEul : signedEulerianCount src dst ≠ 0) (L : V → Finset α)
    (hL : ∀ v : V, (Finset.univ.filter fun a : A => src a = v).card < (L v).card) :
    ∃ c : V → α, (∀ v : V, c v ∈ L v) ∧ ∀ a : A, c (src a) ≠ c (dst a)

theorem JSP_000698.totalEulerian_mod4_eq_two {n : ℕ} (hn : 0 < n)
    (π : Fin n × Fin 3 ≃ Fin (3 * n)) :
    ((Finset.univ : Finset (Finset (CPTArc n))).filter
      (IsEulerian (cptSrc π) (cptDst hn π))).card % 4 = 2

theorem JSP_000698.jsp_000698_fleischner_stiebitz_3_choosable
    {V α : Type*} [DecidableEq α] {n : ℕ} {G : SimpleGraph V}
    (hG : IsCyclePlusTriangles n G) (L : V → Finset α) (hL : ∀ v : V, 3 ≤ (L v).card) :
    ∃ c : V → α, (∀ v : V, c v ∈ L v) ∧ ∀ u v : V, G.Adj u v → c u ≠ c v

theorem JSP_000698.jsp_000698_fleischner_stiebitz_3_colorable
    {V : Type*} {n : ℕ} {G : SimpleGraph V} (hG : IsCyclePlusTriangles n G) :
    Nonempty (G.Coloring (Fin 3))

theorem JSP_000698.jsp_000698_exact_3_colorable
    {V : Type*} {n : ℕ} {G : SimpleGraph V} (hG : IsExactCyclePlusTriangles n G) :
    Nonempty (G.Coloring (Fin 3))

theorem JSP_000698.jsp_000698_chromaticNumber_le_three
    {V : Type*} {n : ℕ} {G : SimpleGraph V} (hG : IsCyclePlusTriangles n G) :
    G.chromaticNumber ≤ 3
```

### Reproduction and Axiom Audit
```bash
lake env lean bountysolves/JSP_000698_FleischnerStiebitz_CyclePlusTriangles.lean
```
Observed `#print axioms` output (exit code `0`, 0 warnings):
```text
'JSP_000698.alon_tarsi_list_coloring' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000698.totalEulerian_mod4_eq_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000698.jsp_000698_fleischner_stiebitz_3_choosable' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000698.jsp_000698_fleischner_stiebitz_3_colorable' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000698.jsp_000698_exact_3_colorable' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000698.jsp_000698_chromaticNumber_le_three' depends on axioms: [propext, Classical.choice, Quot.sound]
```

---

## 4. References

1. H. Fleischner and M. Stiebitz, *A solution to a colouring problem of P. Erdős*, Discrete Math. **101** (1992), 39–48. DOI: `10.1016/0012-365X(92)90588-7`.
2. N. Alon and M. Tarsi, *Colorings and orientations of graphs*, Combinatorica **12** (1992), 125–134.
3. N. Alon, *Combinatorial Nullstellensatz*, Combin. Probab. Comput. **8** (1999), 7–29.
4. Erdős Problems Database, [Problem #842](https://www.erdosproblems.com/842).
5. The Justin Sun Prize Problem Bank, entry `JSP-000698`, `problems/catalog-0601-0700.md`.
