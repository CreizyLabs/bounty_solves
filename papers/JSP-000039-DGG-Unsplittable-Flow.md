# On the Refutation of the Dinitz–Garg–Goemans Cost-Preserving Unsplittable Flow Conjecture via Spine Network Verification

**Target Problem:** JSP-000039 (DGG Cost-Preserving Conjecture)  
**Mathematical Area:** Combinatorial Optimization / Network Flows / Approximation Algorithms  
**Author:** Jason Emerick (Creizy Labs)  
**Mathematical Attribution:** Dmitry Rybin & Jason Emerick (Creizy Labs)  
**Formalization File:** [`BountySolves/DGGCostPreserving.lean`](../BountySolves/DGGCostPreserving.lean)  
**Repository:** [https://github.com/CreizyLabs/bounty_solves](https://github.com/CreizyLabs/bounty_solves)  
**Kernel Status:** 100% Machine-Closed (`0 sorry`, `0 admit`, `0 custom axioms`).  
**Foundational Axioms:** `[propext, Classical.choice, Quot.sound]`.  

---

## 1. Abstract & Problem Formulation

The unsplittable flow problem (UFP) is a central paradigm in combinatorial approximation algorithms and network routing. In 1999, Dinitz, Garg, and Goemans (DGG) proved that any single-source multi-commodity fractional flow $f$ with demands $d_i \le d_{\max}$ can be rounded to an unsplittable flow $F$ such that the congestion on any edge $e$ satisfies:
$$F(e) \le f(e) + d_{\max}.$$

The **DGG Cost-Preserving Conjecture** (`JSP-000039`) asked whether, when rounding a single-source fractional flow to an unsplittable flow, total cost can always remain unchanged or decrease ($\text{cost}(F) \le \text{cost}(f)$) if each edge is allowed extra capacity of at most the largest individual demand $d_{\max}$.

In this paper, we establish the complete negative resolution of `JSP-000039` with a machine-verified Lean 4 formalization of the 3-commodity single-source spine network counterexample (`fractional_demands_valid`, `dgg_cost_preserving_conjecture_disproved`, and `no_cost_preserving_dgg_unsplittable_flow`), proving that no unsplittable routing can simultaneously satisfy the DGG congestion bound and preserve fractional cost.

---

## 2. Mathematical Architecture: The 3-Commodity Spine Counterexample

Consider a single-source directed network with 3 spine arcs $a_1, a_2, a_3$ and 3 commodities with demands:
$$d_1 = 15, \quad d_2 = 10, \quad d_3 = 15, \quad d_{\max} = \max(d_1, d_2, d_3) = 15.$$

Each commodity $i \in \{1, 2, 3\}$ routes its demand either along its primary zero-cost spine path or via a high-cost bypass arc:
* **Commodity 1:** Spine arcs $\{a_1, a_2\}$ vs. bypass of cost $2$ per unit. Fractional split: spine $z_1 = 5$, bypass $f_1 = 10$ ($z_1 + f_1 = 15 = d_1$).
* **Commodity 2:** Spine arcs $\{a_1, a_2, a_3\}$ vs. bypass of cost $3$ per unit. Fractional split: spine $z_2 = 4$, bypass $f_2 = 6$ ($z_2 + f_2 = 10 = d_2$).
* **Commodity 3:** Spine arcs $\{a_2, a_3\}$ (plus arc $a_1$ feed) vs. bypass of cost $2$ per unit. Fractional split: spine $z_3 = 5$, bypass $f_3 = 10$ ($z_3 + f_3 = 15 = d_3$).

### Fractional Flow Loads and Cost
The fractional spine arc loads $x(a_i)$ are:
$$x(a_1) = z_1 + z_2 + z_3 + f_3 = 5 + 4 + 5 + 10 = 24,$$
$$x(a_2) = z_1 + z_2 + z_3 = 5 + 4 + 5 = 14,$$
$$x(a_3) = z_2 + z_3 = 4 + 5 = 9.$$

The total fractional flow cost is:
$$\text{cost}_{\text{frac}} = 2 f_1 + 3 f_2 + 2 f_3 = 2(10) + 3(6) + 2(10) = 58.$$

The DGG additive-$d_{\max}$ capacity ceilings under $d_{\max} = 15$ are:
$$x(a_1) + d_{\max} = 24 + 15 = 39, \quad x(a_2) + d_{\max} = 14 + 15 = 29, \quad x(a_3) + d_{\max} = 9 + 15 = 24.$$

### The Unsplittable Routing Obstruction
An unsplittable routing is uniquely determined by a boolean vector $(b_1, b_2, b_3) \in \{0, 1\}^3$, where $b_i = 1$ routes commodity $i$ on its bypass and $b_i = 0$ routes commodity $i$ on the spine. Its total cost is:
$$\text{cost}(b_1, b_2, b_3) = 30 b_1 + 30 b_2 + 30 b_3.$$

1. If at most one commodity uses its bypass ($b_1 + b_2 + b_3 \le 1$, so $\text{cost} \le 30 \le 58$), at least two commodities are routed on the spine, which strictly violates at least one arc's DGG ceiling:
   * $(b_1, b_2, b_3) = (0, 0, 0) \implies \text{load}(a_2) = 40 > 29$.
   * $(b_1, b_2, b_3) = (0, 0, 1) \implies \text{load}(a_1) = 40 > 39$.
   * $(b_1, b_2, b_3) = (0, 1, 0) \implies \text{load}(a_2) = 30 > 29$.
   * $(b_1, b_2, b_3) = (1, 0, 0) \implies \text{load}(a_3) = 25 > 24$.
2. Every unsplittable routing satisfying `SatisfiesDGGCongestion b1 b2 b3` therefore requires at least two commodities on bypasses ($b_1 + b_2 + b_3 \ge 2$), forcing:
   $$\text{cost}(b_1, b_2, b_3) \ge 60 > 58 = \text{cost}_{\text{frac}}.$$

---

## 3. Lean 4 Formal Verification Summary

Implemented in [`BountySolves/DGGCostPreserving.lean`](../BountySolves/DGGCostPreserving.lean) (`namespace Problem39_DGG_UnsplittableFlow`):

* `fractional_demands_valid`: Certifies $z_i + f_i = d_i$, $d_i \le d_{\max}$, $x(a_1)=24, x(a_2)=14, x(a_3)=9$, and $\text{fractional\_cost} = 58$.
* `dgg_cost_preserving_conjecture_disproved`: Proves that for all $b_1, b_2, b_3 \in \text{Bool}$, `SatisfiesDGGCongestion b1 b2 b3 → unsplittable_cost b1 b2 b3 ≥ 60 ∧ unsplittable_cost b1 b2 b3 > fractional_cost`.
* `dgg_cost_preserving_forces_congestion_violation`: Proves the dual implication `unsplittable_cost b1 b2 b3 ≤ fractional_cost → ¬ SatisfiesDGGCongestion b1 b2 b3`.
* `no_cost_preserving_dgg_unsplittable_flow`: Proves `¬ ∃ b1 b2 b3 : Bool, SatisfiesDGGCongestion b1 b2 b3 ∧ unsplittable_cost b1 b2 b3 ≤ fractional_cost`.
