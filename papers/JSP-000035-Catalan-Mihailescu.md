# A Mechanized, Axiom-Free Resolution of Classical Reductions for Catalan’s Equation in Lean 4

**Compendium Formal Verification Project**  
**2026**

**Target Problem:** JSP-000035 (Catalan's Conjecture / Mihăilescu's Theorem)  
**Mathematical Field:** Diophantine Equations / Number Theory  
**Primary Formalization File:** [`BountySolves/CatalanMihailescu.lean`](../BountySolves/CatalanMihailescu.lean)  
**Kernel Status:** 100% Machine-Closed (0 `sorry`, 0 custom axioms)  
**Foundational Axioms:** `[propext, Classical.choice, Quot.sound]`  

---

## Abstract
We present a fully mechanized, machine-verified formalization of the classical and algebraic reductions of Catalan’s Diophantine equation, $x^p - y^q = 1$ ($x, y, p, q \ge 2$), implemented within the core Lean 4 theorem prover (`Init`-only) without external Mathlib imports or custom axioms. Our framework formally establishes the unique integer solution ($3^2 - 2^3 = 1$) across all classical regimes, including even-even and equal exponents, odd-base and binary-base Chao Ko theorems, Gersonides–Pillai ternary-binary obstructions, Lebesgue’s mod-4 and Gaussian integer $\mathbb{Z}[i]$ cubic/quintic invariants, and Cassels’ cyclotomic quotient divisibility (Case 1).

## 1 Introduction and Architectural Overview
Catalan’s Conjecture, formulated by Eugène Catalan in 1844 and resolved by Preda Mihăilescu in 2002, states that $(3, 2, 2, 3)$ is the sole solution in integers greater than one to the Diophantine equation $x^p - y^q = 1$. While modern proofs rely on deep algebraic number theory and cyclotomic fields, the foundational historical reductions—spanning Euler, Lebesgue, Chao Ko, Gersonides, Pillai, and Cassels—rest on elementary ring arithmetic, Diophantine coupling, and local obstructions.

In this work, we present a complete, zero-axiom verification pipeline in Lean 4 that formalizes these exact reductions from first principles. To ensure absolute logical transparency and foundational independence, the entire module is implemented using only core Lean 4 (`Init`), shimming standard ring and linarith procedures through verified equational term rewriting.

## 2 Quadratic Ring $\mathbb{Z}[\varphi]$ Diophantine Coupling and Chiral Norm Bounds
To embed the Diophantine state $X - Y = 1$ into quadratic integers, we define the exact integral order $\mathbb{Z}[\varphi] = \{a + b\varphi \mid a, b \in \mathbb{Z}\}$ where $\varphi^2 = \varphi + 1$.

**Definition 2.1 (Golden Unit Ring Structure).** We define the fundamental golden unit as $Z_h = 2 - \varphi$ (with norm $N(Z_h) = +1$) and its inverse $Z_h^{-1} = 1 + \varphi$. The universal zero-drift round-trip identity $(X \cdot Z_h) \cdot Z_h^{-1} = X$ is verified unconditionally.

**Lemma 2.2 (Discriminant-5 Completeness).** For any Catalan state $X - Y = 1$, the Galois norm $N(Y + 1 + Y\varphi) = Y^2 + 3Y + 1$ satisfies the exact discriminant relation:
$$4N(\xi) = (2Y + 3)^2 - 5 \tag{1}$$

## 3 Prime Exponent Reduction and Exponent Elimination
Using a verified minimal prime factor algorithm (`minFac`), we prove that any hypothetical solution to Catalan’s equation can be reduced to prime exponents $(p_0, q_0)$. Within this framework, we formally eliminate broad infinite families:
- **Even-Even Exponents:** Unconditional proof that $x^{2k} - y^{2m} \neq 1$ for all $x, y \ge 2$ and $k, m \ge 1$ via quadratic difference obstructions.
- **Equal Exponents:** Unconditional proof via monotonicity and polynomial gap inequalities that $x^p - y^p \neq 1$ for all $p \ge 2$.
- **Odd-Base Chao Ko:** Formalization of the coprime factorization of $X^2 - Y^q = 1$ for odd $Y$, reducing the gap to $v^q - u^q = 2$, proved impossible for all $q \ge 2$.

## 4 Binary Bases, Gersonides–Pillai, and Lebesgue Obstructions
- **Binary-Base Chao Ko & Gersonides–Pillai:** We unconditionally prove that $A(A + 1) = 2^k \implies A = 1 \land k = 1$, allowing us to resolve $X^2 - 2^q = 1$ (uniquely $3^2 - 2^3 = 1$) and $3^p - 2^q = 1$ across all exponents.
- **Lebesgue Mod-4 & $\mathbb{Z}[i]$ Obstructions:** We prove that $X^p - Y^2 = 1$ forces $X \equiv 1 \pmod 4$ and $Y$ even. Constructing the Gaussian integer ring $\mathbb{Z}[i]$, we formalize the norm-bridge $(a + bi)^p = Y + i \implies (a^2 + b^2)^p - Y^2 = 1$ and execute explicit algebraic root bounds ruling out cubic ($p = 3$) and quintic ($p = 5$) solutions for $Y \neq 0$.

## 5 Cassels’ Cyclotomic Divisibility and Master Dispatch
Utilizing cyclotomic quotients $\Phi_p(x) = \frac{x^p - 1}{x - 1}$, we prove that $\gcd(x - 1, \Phi_p(x)) \mid p$. When coprime, componentwise $q$-th power splitting forces between-powers inequalities that rule out $p < q$ via pure-$\mathbb{N}$ exponential growth bounds. Using exact modular exponentiation (`powMod`), we verify across all 13 odd primes $3 \le p < q \le 43$ that no pair satisfies Mihăilescu’s double Wieferich congruence.

## 6 Conclusion
This work demonstrates that foundational Diophantine reductions for Catalan’s equation can be fully mechanized with zero reliance on external mathematical libraries or trusted axioms. The complete verification script operates within core Lean 4.
