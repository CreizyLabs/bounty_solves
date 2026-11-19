# A Formal Proof and Machine-Verified Disproof of the Consecutive Powerful Numbers Square Conjecture (JSP-000301)

**Catalog Identifier:** `JSP-000301` ([The Justin Sun Prize Problem Bank](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#JSP-000301))  
**Related Reference:** Erdős Problem #365 (first question); S. W. Golomb (1970)  
**Mathematical Area:** Number Theory / Powerful Numbers  
**Original Mathematical Disproof:** Solomon W. Golomb, *Amer. Math. Monthly* **77**(8) (1970), 848–852  
**Lean 4 Formalization & Exposition:** CreizyLabs (`bountysolves/JSP_000301_GolombPowerful.lean`)  
**Verification Environment:** Lean `4.35.0-rc2`, Mathlib4 (`9f7aa3a1327bbbc1716bdcedb64b2592e54b9bc7`)

---

## Abstract

A positive integer $n$ is called *powerful* (or *2-full*) if $p^2 \mid n$ for every prime divisor $p \mid n$. Catalog entry `JSP-000301` asks whether at least one member of every consecutive pair of powerful positive integers $(n, n+1)$ must be a perfect square. Following Solomon W. Golomb's 1970 counterexample $(12167, 12168) = (23^3, 2^3 \cdot 3^2 \cdot 13^2)$, we present a complete elementary proof of the structural characterization of powerful numbers ($n$ is powerful if and only if $n = a^2 b^3$ for positive integers $a, b$) and a complete, unconditional, kernel-verified Lean 4 disproof of `JSP-000301` depending strictly on Lean's core foundational axioms (`propext`, `Classical.choice`, `Quot.sound`).

---

## 1. Problem Statement and Formal Definitions

### 1.1 Original Problem (`JSP-000301`)
> *If two consecutive positive integers are powerful, must at least one be a perfect square?*

### 1.2 Canonical Definitions
Let $n \in \mathbb{N}$.
1. **Powerful number (`JSP_000301.IsPowerful`):**
   $$\mathrm{IsPowerful}(n) \iff \forall p \in \mathbb{N},\; p \text{ prime} \land p \mid n \implies p^2 \mid n.$$
2. **Perfect square (Mathlib `IsSquare`):**
   $$\mathrm{IsSquare}(n) \iff \exists r \in \mathbb{N},\; n = r \cdot r.$$
3. **Square-times-cube form (`JSP_000301.IsSqMulCube`):**
   $$\mathrm{IsSqMulCube}(n) \iff \exists a, b \in \mathbb{N},\; n = a^2 b^3.$$

### 1.3 Statement Correspondence Table

| Mathematical Concept | Lean 4 Declaration in `bountysolves/JSP_000301_GolombPowerful.lean` |
| --- | --- |
| Powerful integer ($p \mid n \Rightarrow p^2 \mid n$) | `JSP_000301.IsPowerful` |
| Perfect square ($\exists r,\, n = r^2$) | `IsSquare` (Mathlib) |
| Characterization $n > 0 \land \mathrm{IsPowerful}(n) \iff \exists a,b,\, n = a^2 b^3$ | `JSP_000301.isPowerful_iff_isSqMulCube` |
| Counterexample witness $(12167, 12168)$ | `JSP_000301.jsp_000301_counterexample` |
| Disproof of universal claim | `JSP_000301.jsp_000301_disproved` |
| Equivalent consecutive-pair disproof | `JSP_000301.jsp_000301_disproved_pair` |

---

## 2. Complete Mathematical Proof

### Theorem 2.1 (Structural Characterization of Powerful Numbers)
For every integer $n > 0$, $\mathrm{IsPowerful}(n)$ holds if and only if there exist $a, b \in \mathbb{N}$ such that $n = a^2 b^3$.

**Proof.**
($\Leftarrow$) Suppose $n = a^2 b^3$ and let $p$ be a prime dividing $n$. By Euclid's lemma (`Nat.Prime.dvd_mul`), either $p \mid a^2$ or $p \mid b^3$.
- If $p \mid a^2$, then $p \mid a$, hence $p^2 \mid a^2 \mid a^2 b^3 = n$.
- If $p \mid b^3$, then $p \mid b$, hence $p^3 \mid b^3$, and since $p^2 \mid p^3$, we have $p^2 \mid a^2 b^3 = n$.

($\Rightarrow$) We proceed by strong induction on $n \ge 1$.
- If $n = 1$, take $a = b = 1$.
- If $n > 1$, let $p = \mathrm{minFac}(n)$ be the least prime factor of $n$, and let $e = v_p(n)$ be the $p$-adic valuation of $n$ (`n.factorization p`). Since $p \mid n$ and $n$ is powerful, $p^2 \mid n$, so $e \ge 2$. Write $n = p^e m$ where $p \nmid m$ and $m > 0$.
  - Every prime $q \mid m$ satisfies $q \mid n$ and $q \ne p$, so $\gcd(q^2, p^e) = 1$; since $q^2 \mid n = p^e m$, it follows that $q^2 \mid m$. Thus $m$ is powerful.
  - Because $p \ge 2$ and $e \ge 2$, we have $p^e > 1$, so $m < n$. By the strong induction hypothesis, $m = a_0^2 b_0^3$ for some $a_0, b_0 \in \mathbb{N}$.
  - If $e = 2k$ is even, then $n = (p^k a_0)^2 b_0^3$.
  - If $e = 2k + 3$ is odd (using $e \ge 2 \Rightarrow e \ge 3$), then $n = (p^k a_0)^2 (p b_0)^3$. $\square$

### Theorem 2.2 (Disproof of `JSP-000301`)
There exists a positive integer $n$ such that both $n$ and $n + 1$ are powerful, yet neither $n$ nor $n + 1$ is a perfect square. In particular:
$$\neg\Bigl(\forall n > 0,\; \mathrm{IsPowerful}(n) \land \mathrm{IsPowerful}(n+1) \implies \mathrm{IsSquare}(n) \lor \mathrm{IsSquare}(n+1)\Bigr).$$

**Proof.**
Set $n = 12167$ and $n + 1 = 12168$.
1. **Positivity:** $12167 > 0$ and $12168 = 12167 + 1 > 0$.
2. **Powerfulness:** Direct exact arithmetic gives
   $$12167 = 1^2 \cdot 23^3, \qquad 12168 = (3 \cdot 13)^2 \cdot 2^3 = 39^2 \cdot 2^3.$$
   By Theorem 2.1, both $12167$ and $12168$ are powerful. (Equivalently, their prime factorizations $23^3$ and $2^3 \cdot 3^2 \cdot 13^2$ have every prime exponent at least $2$.)
3. **Non-squareness:** Since
   $$110^2 = 12100 < 12167 < 12168 < 12321 = 111^2,$$
   for any $r \in \mathbb{N}$:
   - if $r \le 110$, then $r^2 \le 110^2 = 12100 < 12167 < 12168$;
   - if $r \ge 111$, then $r^2 \ge 111^2 = 12321 > 12168 > 12167$.
   Therefore neither $12167$ nor $12168$ is equal to $r^2$ for any $r \in \mathbb{N}$. $\square$

---

## 3. Lean 4 Formalization and Verification Evidence

The formal proof resides in [`bountysolves/JSP_000301_GolombPowerful.lean`](../bountysolves/JSP_000301_GolombPowerful.lean) (187 lines). All arithmetic is exact over `ℕ`; zero `sorry`, zero `admit`, zero custom axioms, and zero `native_decide` are used.

### Exported Theorems
```lean
theorem JSP_000301.isPowerful_iff_isSqMulCube {n : ℕ} (hn : 0 < n) :
    IsPowerful n ↔ IsSqMulCube n

theorem JSP_000301.jsp_000301_counterexample :
    0 < 12167 ∧ IsPowerful 12167 ∧ IsPowerful (12167 + 1) ∧
    ¬ IsSquare 12167 ∧ ¬ IsSquare (12167 + 1)

theorem JSP_000301.jsp_000301_disproved :
    ¬ (∀ n : ℕ, 0 < n → IsPowerful n → IsPowerful (n + 1) → IsSquare n ∨ IsSquare (n + 1))

theorem JSP_000301.jsp_000301_disproved_pair :
    ¬ (∀ a b : ℕ, 0 < a → 0 < b → b = a + 1 → IsPowerful a → IsPowerful b → IsSquare a ∨ IsSquare b)
```

### Reproduction and Axiom Audit
```bash
lake env lean bountysolves/JSP_000301_GolombPowerful.lean
```
Observed `#print axioms` output (exit code `0`, 0 warnings):
```text
'JSP_000301.isPowerful_iff_isSqMulCube' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000301.jsp_000301_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000301.jsp_000301_disproved' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000301.jsp_000301_disproved_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
```

---

## 4. References

1. S. W. Golomb, *Powerful numbers*, Amer. Math. Monthly **77**(8) (1970), 848–852. DOI: `10.2307/2317020`.
2. D. T. Walker, *Consecutive integer pairs of powerful numbers and related Diophantine equations*, Fibonacci Quart. **14**(2) (1976), 111–116.
3. R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed., Springer (2004), Section B16.
4. The Justin Sun Prize Problem Bank, entry `JSP-000301`, `problems/catalog-0301-0400.md`.
