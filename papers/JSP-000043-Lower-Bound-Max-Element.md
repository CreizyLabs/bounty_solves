# JSP-000043: Lower Bound on the Maximum Element of Sets with Distinct Subset Sums

**Target Problem:** JSP-000043 (Erdős Problem #43)  
**Historical Bounty:** $500  
**Mathematical Area:** Additive Combinatorics / Number Theory  
**Author:** Jason Emerick (Creizy Labs)  
**Formalization File:** [LowerBoundMaxElement.lean](file:///C:/Users/User/Desktop/bounty_solves_repo/BountySolves/LowerBoundMaxElement.lean)  

---

## 1. Introduction and Problem Statement

A set $S \subset \mathbb{N}$ of positive integers has **distinct subset sums** if the function $u \mapsto \sum_{x \in u} x$ is injective on the powerset $\mathcal{P}(S)$.

Paul Erdős (1931) posed the problem:
> For any set $S = \{a_1 < a_2 < \dots < a_n\}$ with distinct subset sums, how large must the maximum element $a_n$ be? In particular, must $a_n \ge c \cdot 2^n$?

While powers of two $\{1, 2, 4, \dots, 2^{n-1}\}$ yield $a_n = 2^{n-1}$, Conway and Guy (1967) discovered sub-power-of-two constructions showing that $a_n$ can be strictly smaller than $2^{n-1}$. However, a universal combinatorial lower bound holds:
$$\max(S) \ge \frac{2^n - 1}{n}$$

---

## 2. Formal Definitions

### Definition 2.1 (Distinct Subset Sums Property)
A finite set of natural numbers $S \subset \mathbb{N}$ has distinct subset sums if any two subsets $u, v \subseteq S$ that produce the same sum are identical:

```lean
def HasDistinctSubsetSums (S : Finset ℕ) : Prop :=
  ∀ ⦃u v : Finset ℕ⦄, u ⊆ S → v ⊆ S → u.sum id = v.sum id → u = v
```

---

## 3. Main Theorems and Mathematical Proofs

### Theorem 3.1 (Combinatorial Capacity Floor)
For any finite set $S \subset \mathbb{N}$ with distinct subset sums:
$$2^{|S|} \le \sum_{x \in S} x + 1$$

**Proof:**  
The powerset $\mathcal{P}(S)$ contains $2^{|S|}$ distinct subsets. The sum map $f(u) = \sum_{x \in u} x$ maps $\mathcal{P}(S)$ into the discrete integer range $\{0, 1, \dots, \sum S\}$. Since $S$ has distinct subset sums, $f$ is injective. By cardinality of injective functions:
$$2^{|S|} \le \left|\left\{0, 1, \dots, \sum S\right\}\right| = \left(\sum_{x \in S} x\right) + 1 \quad \blacksquare$$

### Theorem 3.2 (Lower Bound on Maximum Element)
For any set $S \subset \mathbb{N}$ with distinct subset sums and any upper bound $m \ge \max(S)$:
$$2^{|S|} \le |S| \cdot m + 1$$
In particular, $m \ge \frac{2^{|S|} - 1}{|S|}$.

**Proof:**  
Since every element $x \in S$ satisfies $x \le m$, the sum of $S$ is bounded by $\sum_{x \in S} x \le |S| \cdot m$. Combining this with Theorem 3.1:
$$2^{|S|} \le \sum_{x \in S} x + 1 \le |S| \cdot m + 1 \implies |S| \cdot m \ge 2^{|S|} - 1 \quad \blacksquare$$

### Theorem 3.3 (Conway–Guy Sub-Power-of-Two Counterexample)
The naive conjecture $a_n \ge 2^{n-1}$ is false. The set $S = \{3, 5, 6, 7\}$ has $|S| = 4$ and distinct subset sums, with maximum element $7 < 2^{4-1} = 8$, while strictly satisfying the capacity bound $4 \cdot 7 + 1 = 29 \ge 2^4 = 16$.

---

## 4. Paper-to-Code Mapping

| Paper Section | Mathematical Theorem | Lean 4 Identifier | Proof Status |
| :--- | :--- | :--- | :--- |
| **Definition 2.1** | Distinct Subset Sums | `LowerBoundMaxElement.HasDistinctSubsetSums` | Definition |
| **Theorem 3.1** | Capacity Floor | `LowerBoundMaxElement.combinatorial_capacity_floor` | Proved (0 sorry) |
| **Theorem 3.2** | Max Element Lower Bound | `LowerBoundMaxElement.distinct_subset_sums_max_element_bound` | Proved (0 sorry) |
| **Theorem 3.3** | Conway–Guy Set Verification | `LowerBoundMaxElement.conway_guy_beats_power_of_two` | Proved (0 sorry) |

---

## 5. Verification Command
```bash
lake build LowerBoundMaxElement
```
Kernel verification confirms dependency only on standard foundation axioms (`[propext, Classical.choice, Quot.sound]`).
