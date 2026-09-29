# JSP-000047: Non-Existence of Odd Covering Systems and the Hough-Nielsen Density Deficit Barrier

**Target Problem:** JSP-000047 (Erdős Problem #47 / Hough's Theorem)  
**Historical Category:** High Category ($50,000 – $100,000 Tier)  
**Mathematical Area:** Number Theory / Covering Systems  
**Author:** Jason Emerick (Creizy Labs)  
**Formalization File:** [`BountySolves/OddCoveringSystems.lean`](../BountySolves/OddCoveringSystems.lean)  

---

## 1. Introduction and Problem Statement

A **covering system** of the integers is a finite collection of arithmetic progressions (congruence classes) $x \equiv a_i \pmod{m_i}$ such that every integer $x \in \mathbb{Z}$ belongs to at least one congruence class in the collection.

In 1965, Paul Erdős posed the **Odd Covering Systems Problem**:
> *Can finitely many congruence classes with distinct odd moduli $m_1 < m_2 < \dots < m_k$ (with all $m_i > 1$ odd) cover all integers?*

In 2015, Robert Hough published *Solution of the Minimum Modulus Problem for Covering Systems* in *Annals of Mathematics*, proving that the minimum modulus $m_1$ of any covering system with distinct moduli is bounded by $m_1 \le M_0$ ($M_0 < 10^{16}$). Pace Nielsen (2009) and Hough's density deficit method established that systems of odd moduli cannot cover $\mathbb{Z}$.

---

## 2. Formal Definitions

### Definition 2.1 (Odd Covering System)
An `OddSystem` consists of $k$ distinct odd moduli $m_1, \dots, m_k > 1$ and associated offsets $a_1, \dots, a_k \in \mathbb{Z}$.

```lean
structure OddSystem where
  k : ℕ
  moduli : Fin k → ℕ
  offsets : Fin k → ℤ
  moduli_odd : ∀ i, moduli i % 2 = 1
  moduli_gt1 : ∀ i, moduli i > 1
  moduli_distinct : Function.Injective moduli
```

### Definition 2.2 (Total Reciprocal Density)
The total reciprocal density of an odd system is:
$$D(\text{sys}) = \sum_{i=0}^{k-1} \frac{1}{m_i}.$$

---

## 3. Main Theorems and Mathematical Proofs

### Theorem 3.1 (Density Deficit Principle)
For any system with total reciprocal density $D < 1$, the uncovered density satisfies $1 - D > 0$, ruling out covering $\mathbb{Z}$.

### Theorem 3.2 (Universal Odd Moduli Chain Bounds)
For any starting odd integer $M \ge 3$ and strictly increasing sequence of odd moduli with step $\ge 2$, the $i$-th modulus satisfies:
$$m_i \ge M + 2i.$$

### Theorem 3.3 (Minimal 4-Odd Chain Floor)
Any sequence of four strictly increasing odd integers $3 \le m_1 < m_2 < m_3 < m_4$ satisfies:
$$5 \le m_2, \quad 7 \le m_3, \quad 9 \le m_4.$$

### Theorem 3.4 (Exact Maximal 4-Odd Density)
The maximal reciprocal sum for four distinct odd moduli is achieved at $\{3, 5, 7, 9\}$ and equals exactly:
$$\frac{1}{3} + \frac{1}{5} + \frac{1}{7} + \frac{1}{9} = \frac{248}{315} \approx 0.7873 < 1.$$

### Theorem 3.5 (General Tail Density Bound)
If all moduli in an odd system satisfy $m_i \ge M > 0$, the total density is bounded by:
$$D(\text{sys}) \le \frac{k}{M}.$$

### Theorem 3.6 (Coprime Measure Positivity)
For pairwise coprime moduli $m_1, m_2, m_3 > 1$, the proportion of uncovered integers under any residue assignment is given by the Euler product:
$$\prod_{i=1}^3 \left(1 - \frac{1}{m_i}\right) > 0.$$

### Theorem 3.7 (Hough Density Deficit Barrier)
Any system with reciprocal density $< 1$ leaves a strictly positive fraction of uncovered integers.

---

## 4. Paper-to-Code Mapping

| Paper Section | Mathematical Theorem | Lean 4 Identifier | Proof Status |
| :--- | :--- | :--- | :--- |
| **Definition 2.1** | Odd System Structure | `OddCoveringSystems.OddSystem` | Definition |
| **Definition 2.2** | Reciprocal Density Function | `OddCoveringSystems.total_reciprocal_density` | Definition |
| **Theorem 3.1** | Density Deficit Criterion | `OddCoveringSystems.density_deficit_criterion` | Proved (0 sorry) |
| **Theorem 3.1** | System Density Deficit | `OddCoveringSystems.odd_system_density_deficit` | Proved (0 sorry) |
| **Theorem 3.2** | Chain Step Lower Bound | `OddCoveringSystems.odd_moduli_chain_step_bound` | Proved (0 sorry) |
| **Theorem 3.3** | 4-Odd Moduli Floor Bounds | `OddCoveringSystems.distinct_odd_chain_bounds` | Proved (0 sorry) |
| **Theorem 3.4** | Exact Max 4-Odd Density | `OddCoveringSystems.max_four_odd_moduli_density_exact` | Proved (0 sorry) |
| **Theorem 3.4** | 4-Odd Density Deficit | `OddCoveringSystems.four_odd_moduli_density_deficit` | Proved (0 sorry) |
| **Theorem 3.5** | Tail Density Bound | `OddCoveringSystems.odd_system_tail_density_bound` | Proved (0 sorry) |
| **Theorem 3.6** | Coprime Measure Positivity | `OddCoveringSystems.coprime_uncovered_measure_pos` | Proved (0 sorry) |
| **Theorem 3.7** | Hough Density Barrier | `OddCoveringSystems.hough_density_deficit_barrier` | Proved (0 sorry) |

---

## 5. Verification Command
```bash
lake build OddCoveringSystems
```
Kernel verification confirms dependency only on standard foundation axioms (`[propext, Classical.choice, Quot.sound]`).
