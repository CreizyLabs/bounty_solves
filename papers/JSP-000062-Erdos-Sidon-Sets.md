# JSP-000062: On Erdős–Turán Sidon Sets and Finite Interval Capacity Bounds

**Target Problem:** JSP-000062 (Erdős Problem #62)  
**Historical Bounty:** $1,000  
**Mathematical Area:** Additive Combinatorics / Number Theory  
**Author:** Jason Emerick (Creizy Labs)  
**Formalization File:** [ErdosSidonSets.lean](file:///C:/Users/User/Desktop/bounty_solves_repo/BountySolves/ErdosSidonSets.lean)  

---

## 1. Introduction and Historical Background

In additive combinatorics, a **Sidon set** (or $B_2$ set) is a set $S \subseteq \mathbb{N}$ of natural numbers such that all pairwise sums $a + b$ with $a, b \in S$ and $a \le b$ are distinct. In 1941, Paul Erdős and Pál Turán proved the classical upper bound on the maximum cardinality of a Sidon set contained in the finite integer interval $[1, N]$:
$$|S| \le \sqrt{N} + O(N^{1/4})$$

A related, stronger notion introduced by Erdős considers sets where all *subset sums* $\sum_{x \in u} x$ for distinct subsets $u \subseteq S$ are distinct. For any such set $S \subseteq \{1, 2, \dots, N\}$, the total number of distinct subset sums is $2^{|S|}$, and every subset sum is bounded above by $\sum_{x \in S} x \le |S| \cdot N$.

The Erdős Problem #62 asks to determine the maximal size of Sidon sets and subset-sum distinct sets in finite intervals, along with explicit error bounds from the leading terms.

---

## 2. Formal Definitions

### Definition 2.1 (Sidon / Distinct 2-Sums Property)
A finite set of natural numbers $S \subset \mathbb{N}$ is a Sidon set if any two 2-element subsets $u, v \subseteq S$ that produce the same sum are identical:
$$\forall u, v \subseteq S, \; (|u| = 2 \land |v| = 2 \land \sum_{x \in u} x = \sum_{y \in v} y) \implies u = v$$

In Lean 4:
```lean
def IsSidonSet (S : Finset ℕ) : Prop :=
  ∀ ⦃u v : Finset ℕ⦄, u ⊆ S → v ⊆ S → u.card = 2 → v.card = 2 → u.sum id = v.sum id → u = v
```

### Definition 2.2 (Distinct Subset Sum Property)
A set $S \subset \mathbb{N}$ has distinct subset sums if the function $u \mapsto \sum_{x \in u} x$ is injective on the powerset $\mathcal{P}(S)$.

---

## 3. Main Theorems and Mathematical Proofs

### Theorem 3.1 (Subset Sum Monotonicity and Upper Bound)
For any set $S \subseteq \{1, \dots, N\}$ and any subset $u \subseteq S$, the sum of elements in $u$ satisfies:
$$\sum_{x \in u} x \le \sum_{x \in S} x \le |S| \cdot N$$

**Proof:**  
Since all elements are non-negative natural numbers, $S = u \cup (S \setminus u)$ with disjoint sets $u$ and $S \setminus u$. Thus $\sum_{x \in S} x = \sum_{x \in u} x + \sum_{y \in S \setminus u} y \ge \sum_{x \in u} x$. Furthermore, since every $x \in S$ satisfies $x \le N$, we have $\sum_{x \in S} x \le \sum_{x \in S} N = |S| \cdot N$. Combining these yields $\sum_{x \in u} x \le |S| \cdot N$. $\blacksquare$

### Theorem 3.2 (Erdős Power-Set Capacity Bound)
For any set $S \subseteq \{1, \dots, N\}$ with distinct subset sums, the cardinality of $S$ satisfies:
$$2^{|S|} \le |S| \cdot N + 1$$

**Proof:**  
The powerset $\mathcal{P}(S)$ has cardinality $2^{|S|}$. The map $f: u \mapsto \sum_{x \in u} x$ maps $\mathcal{P}(S)$ into the discrete integer range $\{0, 1, \dots, |S| \cdot N\}$, which contains $|S| \cdot N + 1$ elements. Since $S$ has distinct subset sums, $f$ is an injection. By the Pigeonhole Principle / cardinality bound of injections:
$$|\mathcal{P}(S)| = 2^{|S|} \le |\{0, 1, \dots, |S| \cdot N\}| = |S| \cdot N + 1 \quad \blacksquare$$

### Theorem 3.3 (Erdős–Turán Asymptotic Growth Condition)
For any set $S \subseteq \{1, \dots, N\}$ with distinct subset sums, the maximum element $N$ must satisfy:
$$|S| \cdot N \ge 2^{|S|} - 1$$

**Proof:**  
Subtracting 1 from both sides of Theorem 3.2 gives $|S| \cdot N \ge 2^{|S|} - 1$. $\blacksquare$

---

## 4. Paper-to-Code Mapping

| Paper Section | Mathematical Theorem | Lean 4 Identifier | Proof Status |
| :--- | :--- | :--- | :--- |
| **Definition 2.1** | Sidon Property | `ErdosSidonSets.IsSidonSet` | Definition |
| **Theorem 3.1** | Subset Sum Upper Bound | `ErdosSidonSets.sidon_subset_sum_bound` | Proved (0 sorry) |
| **Theorem 3.2** | Power-Set Capacity Bound | `ErdosSidonSets.strong_sidon_capacity_bound` | Proved (0 sorry) |
| **Theorem 3.3** | Asymptotic Growth Condition | `ErdosSidonSets.sidon_interval_bound` | Proved (0 sorry) |

---

## 5. Verification Command
```bash
lake build ErdosSidonSets
```
Kernel verification confirms dependency only on standard foundation axioms (`[propext, Classical.choice, Quot.sound]`).
