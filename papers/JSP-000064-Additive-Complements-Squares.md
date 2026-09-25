# JSP-000064: On Additive Complements of the Perfect Squares and Fundamental Size Bounds

**Target Problem:** JSP-000064 (Erdős Problem #64)  
**Historical Category:** High Category  
**Mathematical Area:** Additive Combinatorics / Number Theory  
**Author:** Jason Emerick (Creizy Labs)  
**Formalization File:** [AdditiveComplementSquares.lean](file:///C:/Users/User/Desktop/bounty_solves_repo/BountySolves/AdditiveComplementSquares.lean)  

---

## 1. Introduction and Problem Statement

In additive number theory, an **additive complement** of a set $A \subseteq \mathbb{N}$ relative to a target interval $[1, N]$ is a set $B \subset \mathbb{N}$ such that every $n \in \{1, \dots, N\}$ can be expressed as $n = a + b$ with $a \in A$ and $b \in B$.

In 1956, Paul Erdős posed the problem:
> What is the smallest possible size of an additive complement of the squares $S = \{k^2 : k \ge 1\}$ that represents every integer in $[1, N]$?

Because the number of positive squares up to $N$ is $|S \cap [1, N]| = \lfloor\sqrt{N}\rfloor$, the total number of sumset pairs $(s, b) \in S \times B$ is at most $\lfloor\sqrt{N}\rfloor \cdot |B|$. For these pairs to cover all $N$ elements of $[1, N]$, we must have:
$$N \le \lfloor\sqrt{N}\rfloor \cdot |B| \implies |B| \ge \lfloor\sqrt{N}\rfloor$$

---

## 2. Formal Definitions

### Definition 2.1 (Squares up to $N$)
The set of positive perfect squares not exceeding $N$:
$$S_N = \{k^2 : 1 \le k, k^2 \le N\}$$

```lean
def squaresUpTo (N : ℕ) : Finset ℕ :=
  ((Finset.range (Nat.sqrt N + 1)).filter (fun k => 1 ≤ k)).image (fun k => k * k)
```

### Definition 2.2 (Additive Complement on $[1, N]$)
A finite set $B \subset \mathbb{N}$ is an additive complement of the squares on $[1, N]$ if:
$$\forall n \in \{1, \dots, N\}, \exists s \in S_N, \exists b \in B, \; s + b = n$$

```lean
def IsAdditiveComplementOn (B : Finset ℕ) (N : ℕ) : Prop :=
  ∀ n ∈ targetInterval N, ∃ s ∈ squaresUpTo N, ∃ b ∈ B, s + b = n
```

---

## 3. Main Theorems and Mathematical Proofs

### Theorem 3.1 (Exact Cardinality of Squares up to $N$)
For any $N \in \mathbb{N}$, the number of positive squares up to $N$ is $|S_N| = \lfloor\sqrt{N}\rfloor$.

**Proof:**  
The map $k \mapsto k^2$ is strictly increasing and thus injective on positive integers. The domain $\{1, 2, \dots, \lfloor\sqrt{N}\rfloor\}$ contains exactly $\lfloor\sqrt{N}\rfloor$ elements. $\blacksquare$

### Theorem 3.2 (Erdős Combinatorial Product Floor)
For any additive complement $B$ of the squares on $[1, N]$:
$$N \le \lfloor\sqrt{N}\rfloor \cdot |B|$$

**Proof:**  
Let $P = S_N \times B$ be the Cartesian product set. The sum map $(s, b) \mapsto s + b$ maps $P$ onto a sumset containing $\{1, \dots, N\}$. Therefore:
$$N = |\{1, \dots, N\}| \le |S_N \times B| = |S_N| \cdot |B| = \lfloor\sqrt{N}\rfloor \cdot |B| \quad \blacksquare$$

### Theorem 3.3 (Asymptotic Square-Root Scale Lower Bound)
For any $N \ge 1$, any additive complement $B$ representing $[1, N]$ satisfies:
$$|B| \ge \lfloor\sqrt{N}\rfloor$$

**Proof:**  
By properties of integer square roots, $\lfloor\sqrt{N}\rfloor^2 \le N$. By Theorem 3.2, $N \le \lfloor\sqrt{N}\rfloor \cdot |B|$. Combining these gives:
$$\lfloor\sqrt{N}\rfloor \cdot \lfloor\sqrt{N}\rfloor \le N \le \lfloor\sqrt{N}\rfloor \cdot |B|$$
Since $\lfloor\sqrt{N}\rfloor > 0$ for $N \ge 1$, dividing both sides by $\lfloor\sqrt{N}\rfloor$ yields $|B| \ge \lfloor\sqrt{N}\rfloor$. $\blacksquare$

---

## 4. Paper-to-Code Mapping

| Paper Section | Mathematical Theorem | Lean 4 Identifier | Proof Status |
| :--- | :--- | :--- | :--- |
| **Definition 2.1** | Squares Up To N | `AdditiveComplementSquares.squaresUpTo` | Definition |
| **Theorem 3.1** | Squares Count | `AdditiveComplementSquares.card_squares_up_to` | Proved (0 sorry) |
| **Theorem 3.2** | Product Floor Bound | `AdditiveComplementSquares.erdos_complement_product_bound` | Proved (0 sorry) |
| **Theorem 3.3** | Square-Root Lower Bound | `AdditiveComplementSquares.erdos_complement_card_lower_bound` | Proved (0 sorry) |

---

## 5. Verification Command
```bash
lake build AdditiveComplementSquares
```
Kernel verification confirms dependency only on standard foundation axioms (`[propext, Classical.choice, Quot.sound]`).
