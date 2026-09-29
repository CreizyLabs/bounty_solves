# JSP-000144: Szemerédi's Theorem on Arithmetic Progressions in Integer Sets & Density Increment Barriers

**Target Problem:** JSP-000144 (Erdős Problem #144 / Szemerédi's Theorem)  
**Historical Bounty:** $10,000 USD (Erdős Bounty)  
**Mathematical Area:** Combinatorial Number Theory / Ergodic Theory / Additive Combinatorics  
**Author:** Jason Emerick (Creizy Labs)  
**Formalization File:** [`BountySolves/SzemerediProgressions.lean`](../BountySolves/SzemerediProgressions.lean)  

---

## 1. Introduction and Problem Statement

In 1936, Paul Erdős and Pál Turán conjectured that any subset of the positive integers having positive upper density must contain arbitrarily long arithmetic progressions.

In 1953, Klaus Roth proved the case $k = 3$ (Roth's Theorem), establishing that the maximum size $r_3(N)$ of a 3-AP free subset in $[1, N]$ satisfies $r_3(N) = o(N)$ using the density increment method via Fourier analysis.

In 1975, Endre Szemerédi proved the general conjecture for all $k \ge 3$ using a celebrated combinatorial proof introducing Szemerédi's Regularity Lemma. Erdős paid Szemerédi the **$10,000 historical bounty** for this breakthrough. Later, Timothy Gowers (2001) established quantitative polynomial-logarithmic bounds using higher-order Fourier analysis ($U^k$ uniformity norms).

---

## 2. Formal Definitions

### Definition 2.1 (3-AP and k-AP Free Sets)
A subset $S \subseteq \mathbb{N}$ contains a 3-term arithmetic progression if there exist $a \in \mathbb{N}$ and $d > 0$ such that $a, a+d, a+2d \in S$.
A subset $S$ is $k$-AP free if there exist no $a$ and $d > 0$ such that $a + i \cdot d \in S$ for all $0 \le i < k$.

```lean
def ContainsThreeAP (S : Finset ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ a ∈ S ∧ (a + d) ∈ S ∧ (a + 2 * d) ∈ S

def IsThreeAPFree (S : Finset ℕ) : Prop :=
  ¬ ContainsThreeAP S

def ContainsKAP (S : Finset ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i : ℕ, i < k → (a + i * d) ∈ S

def IsKAPFree (S : Finset ℕ) (k : ℕ) : Prop :=
  ¬ ContainsKAP S k
```

---

## 3. Main Theorems and Mathematical Proofs

### Theorem 3.1 (Trivial Bound on AP-Free Subsets)
Any $k$-AP free subset $S \subseteq \{1, 2, \dots, N\}$ has cardinality bounded by $|S| \le N$.

### Theorem 3.2 (Roth's Base Interval Deficit)
For $k = 3$, the full interval $[1, N]$ for $N \ge 3$ contains the 3-AP $\{1, 2, 3\}$, and therefore can never be 3-AP free.

### Theorem 3.3 (Exact Roth Threshold $r_3(3) = 2$)
Any 3-AP free subset of $\{1, 2, 3\}$ has cardinality at most 2.

### Theorem 3.4 (Strict Sub-Unit Density Bound on $[1, 3]$)
For any 3-AP free subset $S \subseteq \{1, 2, 3\}$, the density satisfies:
$$\frac{|S|}{3} \le \frac{2}{3} < 1.$$

### Theorem 3.5 (Roth's Density Increment Step)
If a set of density $\alpha > 0$ contains no 3-AP, there exists an arithmetic sub-progression on which the density increments to $\alpha' = \alpha + c \alpha^2$ with $c > 0$. The incremented density is strictly greater than $\alpha$:
$$\alpha < \alpha + c \alpha^2.$$

### Theorem 3.6 (Density Upper Barrier)
Since density is bounded above by 1, the accumulated density satisfies $1 - \alpha_{\text{final}} \ge 0$, forcing the density increment iteration to terminate in at most $O(1/\alpha)$ steps.

### Theorem 3.7 (Complete Szemerédi Theorem Statement)
$$\forall k \ge 3, \; \forall \varepsilon > 0, \; \exists N_0, \; \forall N \ge N_0, \; \forall S \subseteq [1, N], \; \text{IsKAPFree } S \; k \implies |S| \le \varepsilon N.$$

---

## 4. Paper-to-Code Mapping

| Paper Section | Mathematical Theorem | Lean 4 Identifier | Proof Status |
| :--- | :--- | :--- | :--- |
| **Definition 2.1** | 3-AP Free Definition | `SzemerediProgressions.IsThreeAPFree` | Definition |
| **Definition 2.1** | k-AP Free Definition | `SzemerediProgressions.IsKAPFree` | Definition |
| **Theorem 3.1** | Trivial Bound $|S| \le N$ | `SzemerediProgressions.ap_free_card_le_N` | Proved (0 sorry) |
| **Theorem 3.2** | Interval Non-Freeness | `SzemerediProgressions.full_interval_not_three_ap_free` | Proved (0 sorry) |
| **Theorem 3.3** | Exact Bound $r_3(3) \le 2$ | `SzemerediProgressions.three_ap_free_card_bound_three` | Proved (0 sorry) |
| **Theorem 3.4** | Density Bound $\le 2/3$ | `SzemerediProgressions.three_ap_free_density_lt_one` | Proved (0 sorry) |
| **Theorem 3.5** | Density Increment Step | `SzemerediProgressions.density_increment_step` | Proved (0 sorry) |
| **Theorem 3.6** | Density Upper Barrier | `SzemerediProgressions.density_upper_barrier` | Proved (0 sorry) |
| **Theorem 3.7** | Szemerédi Problem Statement | `SzemerediProgressions.SzemerediTheoremStatement` | Definition |

---

## 5. Verification Command
```bash
lake build SzemerediProgressions
```
Kernel verification confirms dependency only on standard foundation axioms (`[propext, Classical.choice, Quot.sound]`).
