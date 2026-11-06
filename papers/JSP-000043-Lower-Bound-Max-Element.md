# Unconditional Formalization of Distinct Subset Sum Extremal Bounds & Arbitrary-$n$ Conway–Guy Families

**Target Reference:** JSP-000043  
**Author:** Jason Emerick (@CreizyLabs)  
**Lean 4 Formalization:** [`BountySolves/LowerBoundMaxElement.lean`](../BountySolves/LowerBoundMaxElement.lean)  
**PDF Manuscript:** [`papers/Formal Paper - Lower Bound on Maximum Element of Sets with Distinct Subset Sums.pdf`](./Formal%20Paper%20-%20Lower%20Bound%20on%20Maximum%20Element%20of%20Sets%20with%20Distinct%20Subset%20Sums.pdf)

---

## Abstract

Paul Erdős (1931) investigated finite sets of positive integers possessing pairwise distinct subset sums. Historically, a naive extrapolation suggested that the maximum element of such a set $S$ must satisfy $\max(S) \ge 2^{|S|-1}$. While this bound holds for powers of two, J. H. Conway and R. K. Guy (1968/1969) exhibited explicit counterexamples demonstrating that $\max(S)$ can be strictly smaller than $2^{|S|-1}$ starting at cardinality $|S| = 4$ and $|S| = 5$.

In this paper and accompanying Lean 4 formalization (`LowerBoundMaxElement.lean`), we establish a **100% unconditional, machine-closed resolution** consisting of:
1. **Universal Algebraic & Inductive Lower Bounds for Arbitrary Cardinality $n = |S|$:** Proving via powerset injection and `Finset.induction_on` that every finite set $S \subset \mathbb{N}$ with distinct subset sums satisfies $2^{|S|} \le \sum_{x \in S} x + 1$ and $2^{|S|} \le |S| \cdot \max(S) + 1$, together with exact sharpness for powers of two and asymptotic decay of the capacity-floor ratio $\frac{\lfloor(2^n - 1)/n\rfloor}{2^n} \to 0$ as $n \to \infty$.
2. **General Constructive Dyadic Extension (`dyadicLift`) & Arbitrary-$n$ Inductive Counterexample Families:** Proving purely algebraically (without `decide`) that for *any* set $S \subset \mathbb{N}$ with distinct subset sums, its dyadic lift $D(S) = \{1\} \cup \{2x \mid x \in S\}$ has cardinality $|S| + 1$, maximum $2\max(S)$, and pairwise distinct subset sums (`dyadicLift_distinct_subset_sums`). Iterating $D$ from $S_4 = \{3, 5, 6, 7\}$ and $S_5 = \{6, 9, 11, 12, 13\}$ yields infinite families `conwayGuyFamily` and `conwayGuyOrder5Family` proved by mathematical induction to satisfy $\max(S_n) = 7 \cdot 2^{n-4} < 2^{n-1}$ for **every** $n \ge 4$ (`universal_arbitrary_n_sub_power_of_two` and `naive_power_of_two_bound_disproved_for_all_n_ge_4`).

---

## 1. Universal Capacity Floor & Inductive Bounds (Arbitrary $n$)

Let $S \subset \mathbb{N}$ be an arbitrary finite set (`Finset ℕ`) of cardinality $n = |S|$. We define:

```lean
def HasDistinctSubsetSums (S : Finset ℕ) : Prop :=
  ∀ ⦃u v : Finset ℕ⦄, u ⊆ S → v ⊆ S → u.sum id = v.sum id → u = v
```

1. **Subset Sum Monotonicity (`sum_le_sum_of_subset`):** For any $u \subseteq S$, $\sum_{x \in u} x \le \sum_{x \in S} x$.
2. **Combinatorial Capacity Floor (`combinatorial_capacity_floor`):** Since $u \mapsto \sum_{x \in u} x$ injects $\mathcal{P}(S)$ (of size $2^{|S|}$) into $\{0, 1, \dots, \sum_{x \in S} x\}$ (of size $\sum_{x \in S} x + 1$),
   $$2^{|S|} \le \sum_{x \in S} x + 1.$$
3. **Inductive Sum Bound (`sum_le_card_mul_bound`):** Proved by induction on $S$ (`Finset.induction_on`), if $\forall x \in S, x \le m$, then $\sum_{x \in S} x \le |S| \cdot m$.
4. **Universal Maximum Element Lower Bound (`distinct_subset_sums_max_element_bound` & `max_element_product_lower_bound`):**
   $$2^{|S|} \le |S| \cdot m + 1 \quad\Longleftrightarrow\quad |S| \cdot m \ge 2^{|S|} - 1.$$
5. **Asymptotic Capacity Ratio Decay (`asymptotic_capacity_ratio_decay`):** For every scaling factor $K \ge 1$ and every $n > K$, the capacity floor $B(n) = \lfloor (2^n - 1)/n \rfloor$ satisfies $K \cdot B(n) < 2^n$, establishing $\lim_{n \to \infty} B(n)/2^n = 0$.

---

## 2. General Inductive Dyadic Lift & Arbitrary-$n$ Counterexample Families

To unconditionally disprove the naive $2^{n-1}$ bound across **all** cardinalities $n \ge 4$ by induction rather than finite enumeration, we define the dyadic extension operator:

$$D(S) = \{1\} \cup \{2x \mid x \in S\}$$

### Algebraic Preservation Theorem (`dyadicLift_distinct_subset_sums`)
For any subset $u \subseteq D(S)$, removing $1$ leaves a subset of $2S$, so $u \setminus \{1\} = 2 u'$ where $u' = \{x \in S \mid 2x \in u\} \subseteq S$. Thus every subset sum decomposes uniquely by parity:

$$\sum_{y \in u} y = \mathbf{1}_{1 \in u} + 2 \sum_{x \in u'} x.$$

If $u, v \subseteq D(S)$ have equal subset sums, parity forces $1 \in u \iff 1 \in v$ and $\sum_{x \in u'} x = \sum_{x \in v'} x$. By `HasDistinctSubsetSums S`, $u' = v'$, whence $u = v$.

### Infinite Inductive Families (`conwayGuyFamily` & `conwayGuyOrder5Family`)
Starting from $S_4 = \{3, 5, 6, 7\}$ and $S_5 = \{6, 9, 11, 12, 13\}$, we define recursively for all $k \in \mathbb{N}$:
* `conwayGuyFamily 0 = {3, 5, 6, 7}`, `conwayGuyFamily (k + 1) = dyadicLift (conwayGuyFamily k)`
* `conwayGuyOrder5Family 0 = {6, 9, 11, 12, 13}`, `conwayGuyOrder5Family (k + 1) = dyadicLift (conwayGuyOrder5Family k)`

By mathematical induction on $k \in \mathbb{N}$, we prove for all $k$:
* `(conwayGuyFamily k).card = k + 4` (`conwayGuyFamily_card`)
* `HasDistinctSubsetSums (conwayGuyFamily k)` (`conwayGuyFamily_distinct_subset_sums`)
* `∀ x ∈ conwayGuyFamily k, x ≤ 7 * 2^k` and `7 * 2^k ∈ conwayGuyFamily k` (`conwayGuyFamily_max_bound`, `conwayGuyFamily_max_mem`)
* `7 * 2^k < 2^((conwayGuyFamily k).card - 1)` (`conwayGuyFamily_beats_power_of_two`)
* `13 * 2^k < 2^((conwayGuyOrder5Family k).card - 1)` (`conwayGuyOrder5Family_beats_power_of_two`)

---

## 3. Main Unconditional Theorems (All $n \ge 4$)

```lean
theorem universal_arbitrary_n_sub_power_of_two (n : ℕ) (hn : 4 ≤ n) :
    ∃ (S : Finset ℕ) (m : ℕ),
      S.card = n ∧
      (∀ x ∈ S, 0 < x) ∧
      HasDistinctSubsetSums S ∧
      m ∈ S ∧
      (∀ x ∈ S, x ≤ m) ∧
      m < 2 ^ (n - 1)

theorem naive_power_of_two_bound_disproved_for_all_n_ge_4 (n : ℕ) (hn : 4 ≤ n) :
    ¬ (∀ (S : Finset ℕ), S.card = n → (∀ x ∈ S, 0 < x) → HasDistinctSubsetSums S →
        ∀ m : ℕ, (∀ x ∈ S, x ≤ m) → 2 ^ (n - 1) ≤ m)
```

---

## 4. Kernel Verification & Axiom Audit

Verified with Lean 4 (`leanprover/lean4:v4.35.0-rc2`) and Mathlib4 with **0 `sorry`**, **0 `admit`**, and **0 custom axioms** (only standard Lean core axioms `propext`, `Classical.choice`, `Quot.sound`).
