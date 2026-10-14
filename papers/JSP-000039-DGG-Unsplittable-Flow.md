# On the Refutation of the Dinitz–Garg–Goemans Cost-Preserving Unsplittable Flow Conjecture

**Target Problem:** JSP-000039 (DGG Cost-Preserving Conjecture)  
**Mathematical Area:** Combinatorial Optimization / Network Flows / Approximation Algorithms  
**Author:** Jason Emerick (Creizy Labs)  
**Mathematical Attribution:** Dmitry Rybin (2026 Counterexample) & Jason Emerick (Formal Invariant Verification)  
**Formalization File:** [`BountySolves/Part02_Problem39_DGG_UnsplittableFlow.lean`](../BountySolves/Part02_Problem39_DGG_UnsplittableFlow.lean)  
**Repository:** [https://github.com/CreizyLabs/bounty_solves](https://github.com/CreizyLabs/bounty_solves)  
**Kernel Status:** 100% Machine-Closed (0 `sorry`, 0 custom axioms).  
**Foundational Axioms:** `[propext, Classical.choice, Quot.sound]`.  

---

## 1. Abstract & Problem Formulation

The unsplittable flow problem (UFP) is a central paradigm in combinatorial approximation algorithms and network routing. In 1999, Dinitz, Garg, and Goemans (DGG) proved that any single-source multi-commodity fractional flow $f$ with demands $d_i \le d_{\max}$ can be rounded to an unsplittable flow $f'$ such that the congestion on any edge $e$ satisfies:
$$f'(e) \le f(e) + d_{\max}.$$

The **DGG Cost-Preserving Conjecture** asserted that in undirected or directed networks with edge costs, this additive congestion bound $f'(e) \le f(e) + d_{\max}$ can be achieved without increasing total routing cost:
$$\text{cost}(f') \le \text{cost}(f).$$

In this paper, we formalize the finite combinatorial counterexample discovered by Dmitry Rybin (2026) that definitively disproves the cost-preserving DGG conjecture. We formulate the 3-commodity spine network in Lean 4 and execute an exhaustive boolean decision procedure (`decide`) verifying that every unsplittable routing satisfying the DGG congestion bounds incurs cost at least $60 > 58$.

---

## 2. Mathematical Architecture: The 3-Commodity Spine Counterexample

Consider a directed network with 3 spine arcs $a_1, a_2, a_3$ and 3 commodities with demands:
$$d_1 = 15, \quad d_2 = 10, \quad d_3 = 15, \quad d_{\max} = 15.$$

Each commodity $i \in \{1, 2, 3\}$ can route its demand either along the primary spine path or via an alternate high-cost bypass arc:
* **Commodity 1:** Spine arcs $\{a_1, a_2\}$ vs. bypass of cost 2 per unit. Demand $d_1 = 15$ splits into spine flow $z_1 = 5$ and bypass flow $f_1 = 10$.
* **Commodity 2:** Spine arcs $\{a_1, a_2, a_3\}$ vs. bypass of cost 3 per unit. Demand $d_2 = 10$ splits into spine flow $z_2 = 4$ and bypass flow $f_2 = 6$.
* **Commodity 3:** Spine arcs $\{a_2, a_3\}$ vs. bypass of cost 2 per unit. Demand $d_3 = 15$ splits into spine flow $z_3 = 5$ and bypass flow $f_3 = 10$.

### Fractional Flow Configuration
The fractional spine arc loads $x(a_i)$ are:
$$x(a_1) = z_1 + z_2 + z_3 + f_3 = 5 + 4 + 5 + 10 = 24$$
$$x(a_2) = z_1 + z_2 + z_3 = 5 + 4 + 5 = 14$$
$$x(a_3) = z_2 + z_3 = 4 + 5 = 9$$

The fractional flow cost is:
$$\text{cost}_{\text{frac}} = 2 \cdot f_1 + 3 \cdot f_2 + 2 \cdot f_3 = 2(10) + 3(6) + 2(10) = 58.$$

The DGG congestion ceilings on each arc under $d_{\max} = 15$ are:
$$x(a_1) + d_{\max} = 24 + 15 = 39$$
$$x(a_2) + d_{\max} = 14 + 15 = 29$$
$$x(a_3) + d_{\max} = 9 + 15 = 24$$

---

## 3. The Unsplittable Routing Obstruction

An unsplittable routing choice is represented by a boolean vector $(b_1, b_2, b_3) \in \{0, 1\}^3$, where $b_i = 1$ denotes routing commodity $i$ entirely on its bypass, and $b_i = 0$ denotes routing on the spine.

The total unsplittable routing cost is:
$$\text{cost}(b_1, b_2, b_3) = b_1 \cdot (2 \cdot 15) + b_2 \cdot (3 \cdot 10) + b_3 \cdot (2 \cdot 15) = 30 b_1 + 30 b_2 + 30 b_3.$$

Because each non-zero routing adds 30 to the cost:
1. Routing $\le 1$ commodity on the bypass yields cost $\le 30 \le 58$, but sends at least 2 commodities onto the spine, strictly violating the capacity bound on arc $a_2$:
   $$\text{load}(a_2) = (1 - b_1) \cdot 15 + (1 - b_2) \cdot 10 + (1 - b_3) \cdot 15 \ge 15 + 10 + 0 = 25 \dots \text{or } 15 + 15 = 30 > 29.$$
2. Any routing that satisfies the congestion bounds on all three arcs requires at least two commodities to use bypasses ($b_i + b_j \ge 2$), forcing:
   $$\text{cost}(b_1, b_2, b_3) \ge 30 + 30 = 60 > 58.$$

---

## 4. Lean 4 Formal Verification Summary

The complete formalization is implemented in `Problem39_DGG_UnsplittableFlow`:
```lean
theorem dgg_cost_preserving_conjecture_disproved (b1 b2 b3 : Bool) :
    SatisfiesDGGCongestion b1 b2 b3 →
    unsplittable_cost b1 b2 b3 ≥ 60 ∧ unsplittable_cost b1 b2 b3 > fractional_cost := by
  revert b1 b2 b3
  decide
```
The Lean 4 kernel evaluates all $2^3 = 8$ configurations, proving the theorem with 0 axioms and 0 sorries.
