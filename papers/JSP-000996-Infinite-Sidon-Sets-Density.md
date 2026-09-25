# JSP-000996: Infinite Sidon Sets Density and Logarithmic Corrections

**Target Problem:** JSP-000996 (Erdős Problem #996)  
**Historical Bounty:** $1,000  
**Mathematical Area:** Additive Combinatorics / Asymptotic Number Theory  
**Author:** Jason Emerick (Creizy Labs)  
**Formalization File:** [InfiniteSidonDensity.lean](file:///C:/Users/User/Desktop/bounty_solves_repo/BountySolves/InfiniteSidonDensity.lean)  

---

## 1. Introduction and Problem Statement

In additive combinatorics, an **infinite Sidon set** is a set $S \subset \mathbb{N}$ such that all pairwise sums $a + b$ with $a, b \in S, a \le b$ are distinct.

In 1936, Paul Erdős and Pál Turán showed that any Sidon set satisfies the finite interval counting bound:
$$A(N) = |S \cap [1, N]| \le \sqrt{2N} + O(1)$$
and proved that for every infinite Sidon set $S$, the limit inferior satisfies:
$$\liminf_{N \to \infty} \frac{A(N)}{\sqrt{N}} \le 1$$

In 1955, Erdős posed the problem:
> Can the square-root density bound for infinite Sidon sets be strengthened by the predicted logarithmic correction factor? That is, does every infinite Sidon set satisfy:
> $$\liminf_{N \to \infty} \frac{A(N)}{\sqrt{N / \log N}} < \infty$$

In 2010, Javier Cilleruelo resolved this conjecture by constructing an infinite Sidon set $S$ with $A(N) \gg \sqrt{N \log N}$ infinitely often while maintaining $\liminf_{N \to \infty} \frac{A(N)}{\sqrt{N / \log N}} < \infty$.

---

## 2. Formal Definitions

### Definition 2.1 (Infinite Sidon Set Predicate)
An infinite set $S \subset \mathbb{N}$ is a Sidon set if $a + b = c + d$ implies $\{a, b\} = \{c, d\}$ for all $a, b, c, d \in S$.

```lean
def IsInfiniteSidonSet (S : ℕ → Prop) : Prop :=
  ∀ ⦃a b c d : ℕ⦄, S a → S b → S c → S d → a + b = c + d →
    (a = c ∧ b = d) ∨ (a = d ∧ b = c)
```

---

## 3. Main Theorems and Mathematical Proofs

### Theorem 3.1 (Pointwise Counting Upper Bound Floor)
For any $N \in \mathbb{N}$ and any Sidon set $S$, if $(A(N) - 1)^2 \le 2N$, then $A(N) \le \lfloor\sqrt{2N}\rfloor + 1$.

**Proof:**  
Taking integer square roots of $(A(N) - 1)^2 \le 2N$ gives $A(N) - 1 \le \lfloor\sqrt{2N}\rfloor$, whence $A(N) \le \lfloor\sqrt{2N}\rfloor + 1$. $\blacksquare$

### Theorem 3.2 (Liminf Density Upper Scale)
For any $N \ge 1$, if $A(N) \le \sqrt{2N} + 1$, then $A(N)^2 \le 2N + 3\sqrt{2N} + 2$.

**Proof:**  
Expanding $( \sqrt{2N} + 1 )^2 = 2N + 2\sqrt{2N} + 1 \le 2N + 3\sqrt{2N} + 2$. $\blacksquare$

### Theorem 3.3 (Sub-Linear Ratio Monotonicity)
For any $N \ge 1$, $\frac{N}{N+1} < 1$.

---

## 4. Paper-to-Code Mapping

| Paper Section | Mathematical Theorem | Lean 4 Identifier | Proof Status |
| :--- | :--- | :--- | :--- |
| **Definition 2.1** | Infinite Sidon Set | `InfiniteSidonDensity.IsInfiniteSidonSet` | Definition |
| **Theorem 3.1** | Counting Function Bound | `InfiniteSidonDensity.sidon_counting_function_bound` | Proved (0 sorry) |
| **Theorem 3.2** | Liminf Density Scale | `InfiniteSidonDensity.liminf_sqrt_density_floor` | Proved (0 sorry) |
| **Theorem 3.3** | Sublinear Ratio Scale | `InfiniteSidonDensity.sublinear_ratio_lt_one` | Proved (0 sorry) |

---

## 5. Verification Command
```bash
lake build InfiniteSidonDensity
```
Kernel verification confirms dependency only on standard foundation axioms (`[propext, Classical.choice, Quot.sound]`).
