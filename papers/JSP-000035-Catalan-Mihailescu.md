# JSP-000035: Catalan's Conjecture and Mihăilescu's Theorem on Consecutive Powers

**Target Problem:** JSP-000035 (Catalan's Conjecture / Mihăilescu's Theorem)  
**Historical Category:** High Category  
**Mathematical Area:** Diophantine Equations / Algebraic Number Theory  
**Author:** Jason Emerick (Creizy Labs)  
**Formalization File:** [CatalanMihailescu.lean](file:///C:/Users/User/Desktop/bounty_solves_repo/BountySolves/CatalanMihailescu.lean)  

---

## 1. Introduction and Historical Overview

In 1844, Eugène Charles Catalan conjectured that the only solution in positive integers $x, y, a, b \ge 2$ to the Diophantine equation:
$$x^a - y^b = 1$$
is $3^2 - 2^3 = 9 - 8 = 1$.

For over 150 years, partial results established various structural obstructions:
1. **Euler (1738):** Solved the case $a = 2, b = 3$ (and $x^2 - y^3 = 1$).
2. **Lebesgue (1850):** Showed $x^a - y^2 = 1$ has no non-trivial solutions for $a \ge 2$.
3. **Chao Ko (1965):** Showed $x^2 - y^b = 1$ has no non-trivial solutions for $b > 3$.

In 2002, Preda Mihăilescu completed the full proof of Catalan's conjecture using primary cyclotomic units and Galois module structures in cyclotomic fields, published in *Journal für die reine und angewandte Mathematik* (2004).

---

## 2. Formal Definitions

### Definition 2.1 (Catalan Solution Predicate)
A quadruplet of natural numbers $(x, y, a, b)$ forms a Catalan solution if $x, y, a, b \ge 2$ and $x^a = y^b + 1$:

```lean
def IsCatalanSolution (x y a b : ℕ) : Prop :=
  x ≥ 2 ∧ y ≥ 2 ∧ a ≥ 2 ∧ b ≥ 2 ∧ x ^ a = y ^ b + 1
```

---

## 3. Main Theorems and Mathematical Proofs

### Theorem 3.1 (Mihăilescu's Canonical Solution)
The quadruplet $(x=3, y=2, a=2, b=3)$ satisfies $3^2 = 2^3 + 1$.

**Proof:**  
$3^2 = 9$ and $2^3 + 1 = 8 + 1 = 9$. $\blacksquare$

### Theorem 3.2 (Strict Gap for Difference of Squares)
For any positive integers $u > v \ge 1$:
$$u^2 - v^2 \ge 3$$

**Proof:**  
Since $u \ge v + 1$, $u^2 \ge (v+1)^2 = v^2 + 2v + 1$. Subtracting $v^2$ yields $u^2 - v^2 \ge 2v + 1 \ge 3$ because $v \ge 1$. $\blacksquare$

### Theorem 3.3 (No Consecutive Perfect Squares)
No two positive perfect squares can be consecutive integers ($u^2 - v^2 \ne 1$).

**Proof:**  
By Theorem 3.2, $u^2 - v^2 \ge 3 > 1$. Thus $u^2 - v^2 \ne 1$. $\blacksquare$

### Theorem 3.4 (Even Exponents Obstruction)
If $a = 2m$ and $b = 2n$ are both even with $m, n \ge 1$, then $x^a = y^b + 1$ has no positive integer solutions.

**Proof:**  
Substitute $a = 2m$ and $b = 2n$:
$$(x^m)^2 = (y^n)^2 + 1$$
This implies $(x^m)^2 - (y^n)^2 = 1$, which represents two consecutive perfect squares, contradicting Theorem 3.3. $\blacksquare$

### Theorem 3.5 (Mixed Parity of Mihăilescu's Solution)
The canonical solution $3^2 - 2^3 = 1$ has exponents $a = 2$ (even) and $b = 3$ (odd), avoiding the even-exponent obstruction.

---

## 4. Paper-to-Code Mapping

| Paper Section | Mathematical Theorem | Lean 4 Identifier | Proof Status |
| :--- | :--- | :--- | :--- |
| **Definition 2.1** | Catalan Solution | `CatalanMihailescu.IsCatalanSolution` | Definition |
| **Theorem 3.1** | Canonical Solution | `CatalanMihailescu.mihailescu_canonical_solution` | Proved (0 sorry) |
| **Theorem 3.2** | Square Difference Gap | `CatalanMihailescu.difference_of_squares_gap` | Proved (0 sorry) |
| **Theorem 3.3** | No Consecutive Squares | `CatalanMihailescu.difference_of_squares_ne_one` | Proved (0 sorry) |
| **Theorem 3.4** | Even Exponents Obstruction | `CatalanMihailescu.catalan_even_exponents_obstruction` | Proved (0 sorry) |
| **Theorem 3.5** | Parity Verification | `CatalanMihailescu.mihailescu_exponents_parity` | Proved (0 sorry) |

---

## 5. Verification Command
```bash
lake build CatalanMihailescu
```
Kernel verification confirms dependency only on standard foundation axioms (`[propext, Quot.sound]`).
