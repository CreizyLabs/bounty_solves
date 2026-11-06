# Formal Verification of Conway–Guy Counterexamples to the Naive $2^{n-1}$ Subset Sum Lower Bound

**Target Reference:** JSP-000043  
**Author:** Jason Emerick (@CreizyLabs)  
**Lean 4 Formalization:** [`BountySolves/LowerBoundMaxElement.lean`](../BountySolves/LowerBoundMaxElement.lean)  
**PDF Manuscript:** [`papers/Formal Paper - Lower Bound on Maximum Element of Sets with Distinct Subset Sums.pdf`](./Formal%20Paper%20-%20Lower%20Bound%20on%20Maximum%20Element%20of%20Sets%20with%20Distinct%20Subset%20Sums.pdf)

---

## Abstract

Paul Erdős (1931) investigated finite sets of positive integers possessing pairwise distinct subset sums. Historically, a naive extrapolation suggested that the maximum element of such a set $S$ must satisfy $\max(S) \ge 2^{|S|-1}$. While this bound holds for powers of two, J. H. Conway and R. K. Guy (1969) exhibited explicit counterexamples demonstrating that $\max(S)$ can be strictly smaller than $2^{|S|-1}$ for cardinality $|S| = 4$ and $|S| = 5$. In this paper, we present a 100% unconditional, machine-closed formalization in Lean 4 verifying the Conway–Guy order-4 and order-5 counterexamples. Our verification relies entirely on computable kernels with zero external Mathlib dependencies, no custom axioms, and zero `sorry` placeholders.

---

## 1. Introduction and Historical Context

Let $S = \{x_1, x_2, \dots, x_n\}$ be a finite set of positive integers. We say $S$ has distinct subset sums if all $2^n$ sums formed by taking subset sums $\sum_{x \in A} x$ (for $A \subseteq S$) are pairwise distinct.

A natural early conjecture (often attributed to the broader investigation of distinct subset sum extremal problems initiated by Erdős in 1931) hypothesized that any valid set must satisfy:

$$\max(S) \ge 2^{|S|-1}$$

Conway and Guy (1969) disproved this naive lower bound by discovering explicit integer sequences that violate the inequality. Specifically:

* For $|S| = 4$, the set $S_4 = \{3, 5, 6, 7\}$ yields $\max(S_4) = 7 < 8 = 2^{4-1}$.
* For $|S| = 5$, the set $S_5 = \{6, 9, 11, 12, 13\}$ yields $\max(S_5) = 13 < 16 = 2^{5-1}$.

*(Note: While these base cases refute the strict $2^{n-1}$ formula, the asymptotic question of whether $\max(S) \ge c \cdot 2^n$ holds for an absolute constant $c > 0$ across all $n$ remains one of the notable open problems in additive combinatorics.)*

---

## 2. Formalization Architecture in Lean 4

Our formal verification (`LowerBoundMaxElement.lean`) is self-contained and implemented without external library imports. It establishes the following core components:

1. **Subsets Generation:** Computes the exact list of all $2^n$ sublists recursively.
2. **Subset Sum Computation:** Folds addition over sublists to evaluate every subset sum precisely.
3. **Computable Distinctness (`isNodup`):** Implements an explicit recursive duplicate-free check to ensure all subset sums are strictly distinct without relying on library deduplication quirks.
4. **Kernel Evaluation (`by decide` / `rfl`):** Leverages Lean 4's definitional equality and kernel reduction to verify properties exhaustively without unproven hypotheses.

---

## 3. Verified Counterexamples

### Order-4 Counterexample ($S_4$)
We define the set $S_4 = [3, 5, 6, 7]$ and verify its properties:
* **Length:** $|S_4| = 4$ (`conway_guy_4_len`)
* **Positivity:** All elements are strictly positive (`conway_guy_4_pos`).
* **Distinctness:** All 16 subset sums $\{0, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 21\}$ are verified to be unique (`conway_guy_4_distinct_sums`).
* **Maximum Bound:** $\max(S_4) = 7$, which strictly violates $2^{4-1} = 8$ (`conway_guy_4_beats_power_of_two`).

### Order-5 Counterexample ($S_5$)
We define the set $S_5 = [6, 9, 11, 12, 13]$ and verify its properties:
* **Length:** $|S_5| = 5$ (`conway_guy_5_len`)
* **Positivity:** All elements are strictly positive (`conway_guy_5_pos`).
* **Distinctness:** All 32 subset sums are verified to be unique (`conway_guy_5_distinct_sums`).
* **Maximum Bound:** $\max(S_5) = 13$, which strictly violates $2^{5-1} = 16$ (`conway_guy_5_beats_power_of_two`).

---

## 4. Main Theorem Statement and Proof

The formal negation of the naive lower bound hypothesis is stated and proven in Lean 4 as follows:

```lean
def NaivePowerOfTwoBoundHypothesis : Prop :=
  ∀ S : List Nat,
    S.length > 0 →
    allPositive S = true →
    isNodup S = true →
    hasDistinctSubsetSums S = true →
    ∀ m : Nat, (∀ x ∈ S, x ≤ m) → 2 ^ (S.length - 1) ≤ m

theorem naive_power_of_two_bound_disproved :
    ¬ NaivePowerOfTwoBoundHypothesis := by
  intro h
  have h_bound := h ConwayGuy4
    (by decide)
    conway_guy_4_pos
    conway_guy_4_nodup
    conway_guy_4_distinct_sums
    7
    conway_guy_4_max_bound
  have h_gap : ¬ (2 ^ (ConwayGuy4.length - 1) ≤ 7) := by decide
  exact h_gap h_bound
```

---

## 5. Conclusion

Using machine-checked formal methods, we have unconditionally established that the naive lower bound $\max(S) \ge 2^{|S|-1}$ for sets with distinct subset sums is false, anchored by the verified Conway–Guy counterexamples at orders 4 and 5. The Lean 4 formalization kernel certifies zero `sorry` instances and zero axioms (`does not depend on any axioms`).
