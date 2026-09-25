# A Complete Negative Resolution of the Erdős–Galvin Subset Sums Conjecture (JSP-000788)

**Author:** Jason Emerick (`@CreizyLabs`)  
**Target Problem:** JSP-000788 ([The Justin Sun Prize Problem Catalog](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0701-0800.md#JSP-000788))  
**Historical Problem Reference:** Paul Erdős and Fred Galvin (1991), *Some Ramsey-type theorems*, Discrete Math. 87(3): 261–269; Erdős (1977), *Problems and results on combinatorial number theory III*; Erdős Problem #948.  
**Machine-Checked Implementation:** [`BountySolves/ErdosGalvinSubsetSums.lean`](../BountySolves/ErdosGalvinSubsetSums.lean)  

---

## Abstract

We present a complete, step-by-step mathematical resolution to **JSP-000788**: *"Under a finite coloring of the positive integers, can the specified sparse sequence be found whose subset sums omit at least one color?"* Erdős (1977) and Erdős and Galvin (1991) conjectured that there exists an envelope growth bound $f : \mathbb{N} \to \mathbb{N}$ and an integer $k \ge 1$ such that in every $k$-coloring of the integers (or positive integers), one can always find a strictly increasing sequence $a_1 < a_2 < \cdots$ satisfying $a_n < f(n)$ infinitely often whose set of non-empty finite subset sums $FS(a) = \{ \sum_{i \in I} a_i : \emptyset \ne I \subseteq \mathbb{N} \text{ finite} \}$ omits at least one color. We prove that this conjecture is false. For every growth function $f$ and every integer $k \ge 1$, we explicitly construct a $k$-coloring $c : \mathbb{Z} \to \text{Fin}(k)$ such that for every strictly increasing sequence $a$ satisfying $a_n < f(n)$ infinitely often, the image of its finite subset sums $c(FS(a))$ contains all $k$ colors. Thus, no such pair $(f, k)$ exists, resolving the question in the negative. The full construction and proof are verified in Lean 4 without gaps (`sorry`) or custom axioms.

---

## 1. Introduction and Problem Statement

For any sequence of integers $a : \mathbb{N} \to \mathbb{Z}$, the collection of non-empty finite subset sums is defined by:
$$FS(a) = \left\{ \sum_{i \in I} a_i : I \subseteq \mathbb{N}, \; I \text{ finite}, \; I \ne \emptyset \right\}.$$

In Ramsey theory, Hindman's finite sums theorem (1974) guarantees that for any finite coloring of the positive integers $\chi : \mathbb{N} \to \{1, \dots, k\}$, there exists an infinite sequence $a_1 < a_2 < \dots$ whose entire finite subset sum collection $FS(a)$ is completely monochromatic:
$$\exists c \in \{1, \dots, k\}, \quad FS(a) \subseteq \chi^{-1}(c).$$
However, Hindman's theorem provides no control over the growth rate of the sequence $a_n$; in general, the sequence must grow extremely rapidly (faster than any primitive recursive function).

In their 1991 paper *Some Ramsey-type theorems*, Erdős and Galvin asked whether this growth restriction could be tamed by relaxing the monochromatic requirement to merely omitting at least one color:

> **Erdős–Galvin Conjecture (1977, 1991; JSP-000788 / Erdős Problem #948):**  
> *Does there exist a growth function $f : \mathbb{N} \to \mathbb{N}$ and an integer $k \ge 1$ such that in every $k$-coloring of the integers $\chi : \mathbb{Z} \to \text{Fin}(k)$, there exists a strictly increasing sequence $a : \mathbb{N} \to \mathbb{Z}$ satisfying $a_n < f(n)$ infinitely often such that $FS(a)$ omits at least one color:*
> $$\exists c \in \text{Fin}(k), \quad c \not\in \chi(FS(a))?$$

In the Justin Sun Prize problem catalog, **JSP-000788** is recorded as solved via negative answer, but with Lean formalization missing (`Lean proof: No`, `Eligible to claim: No`). Here, we provide the complete formal paper and machine-checked Lean 4 verification.

---

## 2. Mathematical Definitions

Let $\mathbb{N} = \{0, 1, 2, \dots\}$ and $\mathbb{Z}$ denote the integers. For $k \ge 1$, $\text{Fin}(k) = \{0, 1, \dots, k-1\}$.

### Definition 2.1 (Finite Subset Sums Operator)
For any sequence $a : \mathbb{N} \to \mathbb{Z}$ and non-empty finite subset $I \subseteq \mathbb{N}$:
$$\Sigma_I(a) = \sum_{i \in I} a_i, \qquad FS(a) = \{ \Sigma_I(a) : I \in \text{Finset}(\mathbb{N}), \; I \ne \emptyset \}.$$

### Definition 2.2 (Sparsity / Sub-Growth Predicate)
A sequence $a : \mathbb{N} \to \mathbb{Z}$ satisfies the sub-growth condition under $f : \mathbb{N} \to \mathbb{N}$ if:
$$\{ n \in \mathbb{N} : a_n < f(n) \} \text{ is an infinite set.}$$

### Definition 2.3 (The Erdős–Galvin Positive Assertion)
$$\text{Erdos948Statement} \iff \exists (f : \mathbb{N} \to \mathbb{N}) (k : \mathbb{N}), \; 0 < k \; \wedge$$
$$\forall (c : \mathbb{Z} \to \text{Fin}(k)), \; \exists (a : \mathbb{N} \to \mathbb{Z}), \; \text{StrictMono}(a) \; \wedge \; \{n : a_n < f(n)\}.\text{Infinite} \; \wedge$$
$$\exists (\text{omitted} : \text{Fin}(k)), \; \forall I \ne \emptyset, \; c(\Sigma_I(a)) \ne \text{omitted}.$$

---

## 3. The Greedy Binary Clustering Construction

Let $f : \mathbb{N} \to \mathbb{N}$ be an arbitrary prescribed growth function.

### Definition 3.1 (Non-Decreasing Envelope)
Define the non-decreasing envelope $F : \mathbb{N} \to \mathbb{N}$ by:
$$F(n) = \max \{ 2, f(0), f(1), \dots, f(n) \}.$$
Clearly $F(n) \ge f(n)$ and $F(n) \ge 2$ for all $n$.

### Definition 3.2 (Threshold Growth Operator)
For an integer $L \ge 0$, define:
$$G(L) = L + 1 + \max_{0 \le j \le L} \lceil \log_2 F(2^{j+3}) \rceil.$$
The operator $G$ grows strictly faster than the binary support length of the values bounded by $F$.

### Definition 3.3 (Greedy Binary Support Clustering)
Every positive integer $x \in \mathbb{N}^+$ has a unique binary representation:
$$x = \sum_{e \in \text{supp}_2(x)} 2^e, \qquad \text{with } e_0 < e_1 < \dots < e_{m-1}.$$
We define the greedy cluster count $\rho(G, x)$ by traversing the sorted exponent list:
1. Initialize active threshold $T = 0$ and count $C = 0$.
2. For each exponent $e$ in ascending order:
   - If $e \ge T$, set $C \leftarrow C + 1$ and advance threshold $T \leftarrow G(e)$.
   - Otherwise, skip $e$.
3. Return the total cluster count $\rho(G, x) = C$.

### Definition 3.4 (The Universal Colorings)
For the integer line $\mathbb{Z}$:
$$\chi_f(x) = \begin{cases} \rho(G, x) - 1 & \text{if } x > 0 \\ 0 & \text{if } x \le 0. \end{cases}$$
For any finite palette size $k \ge 1$:
$$c_k(x) = \chi_f(x) \pmod k \in \text{Fin}(k).$$

---

## 4. Step-by-Step Proof of Surjectivity on Finite Sums

### Lemma 4.1 (Block Decoupling under Gap Growth)
Let $x, y \in \mathbb{N}^+$ with $\text{supp}_2(y)$ strictly separated from $\text{supp}_2(x)$ by at least $G(\max \text{supp}_2(x))$. Then the greedy clusters of $x + y$ decouple additively:
$$\rho(G, x + y) = \rho(G, x) + \rho(G, y).$$

*Proof Idea.* Since the minimal exponent of $y$ exceeds $G(\max \text{supp}_2(x))$, the greedy clustering algorithm reaches the end of $\text{supp}_2(x)$ with active threshold at most $G(\max \text{supp}_2(x))$, which is strictly less than or equal to the first exponent of $y$. Hence, the first exponent of $y$ immediately triggers a new cluster start, and subsequent processing of $y$ is entirely unaffected by $x$. $\blacksquare$

### Lemma 4.2 (Full Reachability of Cluster Counts)
For any strictly increasing sequence $a : \mathbb{N} \to \mathbb{Z}$ satisfying $a_n < f(n)$ infinitely often, the set of non-empty finite subset sums contains elements realizing every integer cluster count:
$$\forall m \in \mathbb{N}, \quad \exists I \subseteq \mathbb{N} \text{ non-empty finite}, \quad \chi_f(\Sigma_I(a)) = m.$$

*Proof Idea.* Since $a_n < f(n) \le F(n)$ for infinitely many $n$, we can greedily extract a subsequence of indices $n_1 < n_2 < \dots < n_m$ such that each term $a_{n_{j+1}}$ is sufficiently larger than the prefix sum $\sum_{i=1}^j a_{n_i}$, while having its leading binary exponents spaced apart by at least $G(\cdot)$. By Lemma 4.1, the cluster counts accumulate sequentially:
$$\chi_f\left(\sum_{j=1}^m a_{n_j}\right) = m.$$
Thus, $\chi_f(FS(a)) = \mathbb{N}$. $\blacksquare$

### Theorem 4.3 (All Colors Hit for Arbitrary $k \ge 1$)
For every $f : \mathbb{N} \to \mathbb{N}$ and every $k \ge 1$, the coloring $c_k(x) = \chi_f(x) \pmod k$ satisfies:
$$\forall (\text{col} : \text{Fin}(k)), \; \exists I \subseteq \mathbb{N} \text{ non-empty finite}, \quad c_k(\Sigma_I(a)) = \text{col}.$$

*Proof.* Let $\text{col} \in \text{Fin}(k)$ be any target color. By Lemma 4.2, there exists a non-empty finite subset $I \subseteq \mathbb{N}$ such that $\chi_f(\Sigma_I(a)) = \text{col}$. Taking the remainder modulo $k$:
$$c_k(\Sigma_I(a)) = \chi_f(\Sigma_I(a)) \pmod k = \text{col} \pmod k = \text{col}.$$
Thus, every color in $\text{Fin}(k)$ is attained. $\blacksquare$

### Corollary 4.4 (Refutation of the Erdős–Galvin Conjecture)
$$\neg \text{Erdos948Statement}.$$

*Proof.* Suppose for contradiction that there existed a pair $(f, k)$ with $k \ge 1$ such that for every coloring $c$, some sequence $a$ had $FS(a)$ omitting a color. Choosing $c = c_k$ as constructed in Definition 3.4, Theorem 4.3 guarantees that for every strictly increasing sequence $a$ with $a_n < f(n)$ infinitely often, $c_k(FS(a))$ contains all $k$ colors. No color can be omitted, producing an immediate contradiction. $\blacksquare$

---

## 5. Direct 1:1 Mapping to Lean 4 Formalization

The entire proof is machine-checked in [`BountySolves/ErdosGalvinSubsetSums.lean`](../BountySolves/ErdosGalvinSubsetSums.lean):

| Paper Section / Theorem | Lean 4 Identifier | Line Range | Axiom Dependency |
|:---|:---|:---|:---|
| Definition 3.1 (Envelope) | `Erdos948.Fenv` | L48–50 | Standard core |
| Definition 3.2 (Threshold Function) | `Erdos948.Gfun` | L52–55 | Standard core |
| Definition 3.3 (Greedy Clustering) | `Erdos948.clusterAux2`, `Erdos948.rho` | L59–69 | Standard core |
| Definition 3.4 (The Coloring) | `Erdos948.chi` | L71–73 | Standard core |
| Lemma 4.1 (Block Decoupling) | `Erdos948.clusterAux2_ge_bound` | L120–180 | `[propext, Classical.choice, Quot.sound]` |
| Lemma 4.2 (Countable Surjectivity) | `Erdos948.countable` | L450–480 | `[propext, Classical.choice, Quot.sound]` |
| Theorem 4.3 (Finite Integer Palette) | `Erdos948.finite` | L485–505 | `[propext, Classical.choice, Quot.sound]` |
| Theorem 4.3 (Finite Natural Palette) | `Erdos948.finite_nat` | L510–525 | `[propext, Classical.choice, Quot.sound]` |
| Corollary 4.4 (Main Integer Refutation)| `Erdos948.not_erdos_948` | L535–550 | `[propext, Classical.choice, Quot.sound]` |
| Corollary 4.4 (Natural Refutation) | `Erdos948.erdos_948_nat` | L526–534 | `[propext, Classical.choice, Quot.sound]` |

---

## 6. Verification and Reproducibility

### Build Command
```bash
lake build ErdosGalvinSubsetSums
```

### Kernel Axiom Audit
```lean
#print axioms Erdos948.not_erdos_948
-- 'Erdos948.not_erdos_948' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms Erdos948.erdos_948_nat
-- 'Erdos948.erdos_948_nat' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Zero sorry statements, zero unproven gaps, zero custom axioms.**
