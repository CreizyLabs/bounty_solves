# Disproof of the Consecutive Powerful Squares Conjecture (JSP-000301)

**Author:** Jason Emerick (`@CreizyLabs`)  
**Target Problem:** JSP-000301 ([The Justin Sun Prize Problem Catalog](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#JSP-000301))  
**Historical Problem Reference:** Solomon W. Golomb (1970), *Powerful Numbers*, American Mathematical Monthly 77(8): 848–852; Erdős Problem #365.  
**Machine-Checked Implementation:** [`BountySolves/GolombPowerful.lean`](../BountySolves/GolombPowerful.lean)  

---

## Abstract

We present a complete, rigorous mathematical resolution to the yes/no question posed in **JSP-000301**: *"If two consecutive positive integers are powerful, must at least one be a perfect square?"* We prove that the answer is strictly **negative** by exhibiting the explicit consecutive integer pair $(12167, 12168)$, demonstrating that both integers are powerful, consecutive, and that neither integer is a perfect square. The entire deduction is presented from first principles with zero omitted cases, accompanied by an exact mapping to a machine-checked Lean 4 kernel formalization depending only on standard core axioms.

---

## 1. Problem Statement and History

In number theory, a positive integer $n$ is defined to be **powerful** (or square-full) if every prime factor $p$ dividing $n$ satisfies $p^2 \mid n$. 

In 1970, Solomon W. Golomb investigated pairs of consecutive powerful numbers in the *American Mathematical Monthly*. A natural question arising from the study of powerful numbers—later recorded in problem collections including Paul Erdős's Problem #365 and The Justin Sun Prize catalog as **JSP-000301**—asks:

> **JSP-000301 Formulation:**  
> *If two consecutive positive integers are powerful, must at least one be a perfect square?*

Formally, the universal conjecture under consideration is:
$$\mathcal{C}_{\text{Golomb}} \iff \forall a, b \in \mathbb{N}_{>0},\; (b = a + 1 \land \text{IsPowerful}(a) \land \text{IsPowerful}(b)) \implies (\text{IsSquare}(a) \lor \text{IsSquare}(b)).$$

We resolve this problem completely by proving that $\mathcal{C}_{\text{Golomb}}$ is **False**:
$$\neg \mathcal{C}_{\text{Golomb}}.$$

---

## 2. Definitions and Structural Lemmas

### Definition 2.1 (Powerful Number)
A positive integer $n \in \mathbb{N}$ is powerful if and only if it can be represented in the canonical form:
$$n = x^2 y^3 \quad \text{for some } x, y \in \mathbb{N}.$$

*(Note: It is a standard classical theorem that any integer whose prime factorization $n = \prod p_i^{e_i}$ has all exponents $e_i \ge 2$ can be factored as $n = x^2 y^3$, since every integer $e_i \ge 2$ can be expressed as $e_i = 2 a_i + 3 b_i$ with $a_i \ge 0, b_i \in \{0, 1\}$.)*

### Definition 2.2 (Perfect Square)
A positive integer $n \in \mathbb{N}$ is a perfect square if there exists an integer $k \in \mathbb{N}$ such that $n = k^2$.

---

## 3. Step-by-Step Mathematical Proof

We prove the conjecture false by explicit witness. Consider the pair of positive integers:
$$a = 12167, \quad b = 12168.$$

### Lemma 3.1 (Consecutiveness)
The integers $a$ and $b$ are strictly consecutive positive integers:
$$b = a + 1.$$
*Proof:*
$$12168 - 12167 = 1.$$
Since $12167 > 0$, both are positive integers. $\blacksquare$

### Lemma 3.2 (Powerful Property of $a = 12167$)
The integer $12167$ is a powerful number.
*Proof:*
Setting $x = 1$ and $y = 23$:
$$x^2 y^3 = 1^2 \cdot 23^3 = 1 \cdot (23 \cdot 23 \cdot 23) = 1 \cdot 12167 = 12167.$$
Since $12167$ is of the form $x^2 y^3$ with $x, y \in \mathbb{N}$, it is powerful by Definition 2.1. $\blacksquare$

### Lemma 3.3 (Powerful Property of $b = 12168$)
The integer $12168$ is a powerful number.
*Proof:*
Setting $x = 39$ and $y = 2$:
$$x^2 y^3 = 39^2 \cdot 2^3 = 1521 \cdot 8 = 12168.$$
Equivalently, in terms of prime factorization:
$$12168 = 2^3 \cdot 3^2 \cdot 13^2.$$
Every prime factor ($2, 3, 13$) appears with exponent $\ge 2$. Thus, $12168$ is powerful by Definition 2.1. $\blacksquare$

### Lemma 3.4 (Non-Square Property of $a = 12167$)
The integer $12167$ is not a perfect square.
*Proof:*
Suppose for contradiction that $12167$ is a perfect square, i.e., $12167 = k^2$ for some integer $k \in \mathbb{N}$.
We evaluate the consecutive integer squares:
$$110^2 = 12100,$$
$$111^2 = 12321.$$
Since the square function $f(k) = k^2$ is strictly increasing on $\mathbb{N}$:
- If $k \le 110$, then $k^2 \le 110^2 = 12100 < 12167$.
- If $k \ge 111$, then $k^2 \ge 111^2 = 12321 > 12167$.
Since every integer $k \in \mathbb{N}$ satisfies either $k \le 110$ or $k \ge 111$, there exists no integer $k$ such that $k^2 = 12167$. 
Therefore, $12167$ is not a perfect square. $\blacksquare$

### Lemma 3.5 (Non-Square Property of $b = 12168$)
The integer $12168$ is not a perfect square.
*Proof:*
Suppose for contradiction that $12168 = k^2$ for some integer $k \in \mathbb{N}$.
Using the same consecutive square bounds:
$$110^2 = 12100 < 12168 < 12321 = 111^2.$$
- If $k \le 110$, then $k^2 \le 12100 < 12168$.
- If $k \ge 111$, then $k^2 \ge 12321 > 12168$.
Hence, no integer $k$ satisfies $k^2 = 12168$. 
Therefore, $12168$ is not a perfect square. $\blacksquare$

---

## 4. Main Theorem

### Theorem 4.1 (Disproof of JSP-000301)
$$\neg \left( \forall a, b \in \mathbb{N}_{>0},\; (b = a + 1 \land \text{IsPowerful}(a) \land \text{IsPowerful}(b)) \implies (\text{IsSquare}(a) \lor \text{IsSquare}(b)) \right).$$

*Proof:*
Assume for contradiction that the universal statement holds. Specializing to the pair $(a, b) = (12167, 12168)$:
1. $a > 0$ holds since $12167 > 0$.
2. $b = a + 1$ holds by Lemma 3.1.
3. $\text{IsPowerful}(a)$ holds by Lemma 3.2.
4. $\text{IsPowerful}(b)$ holds by Lemma 3.3.
By modus ponens, the conclusion must follow:
$$\text{IsSquare}(12167) \lor \text{IsSquare}(12168).$$
However:
- By Lemma 3.4, $\neg \text{IsSquare}(12167)$.
- By Lemma 3.5, $\neg \text{IsSquare}(12168)$.
This yields $(\text{False} \lor \text{False}) \implies \text{False}$, a contradiction.
Thus, the universal conjecture is strictly false. $\blacksquare$

---

## 5. Direct Mapping to Lean 4 Formalization

The formal proof is implemented in [`BountySolves/GolombPowerful.lean`](../BountySolves/GolombPowerful.lean). Each mathematical statement maps one-to-one to the formal theorems in the Lean codebase:

| Mathematical Statement | Lean 4 Symbol / Identifier | Line Number in File | Status |
| :--- | :--- | :--- | :--- |
| **Definition 2.1** (Powerful Number) | `GolombPowerful.IsPowerful` | Line 16 | Complete |
| **Definition 2.2** (Perfect Square) | `GolombPowerful.IsSquare` | Line 20 | Complete |
| **Lemma 3.1** (Consecutiveness) | `GolombPowerful.consecutive_12167_12168` | Line 53 | Machine-Closed (`decide`) |
| **Lemma 3.2** ($12167$ is Powerful) | `GolombPowerful.powerful_12167` | Line 23 | Machine-Closed (`use 1, 23; decide`) |
| **Lemma 3.3** ($12168$ is Powerful) | `GolombPowerful.powerful_12168` | Line 28 | Machine-Closed (`use 39, 2; decide`) |
| **Lemma 3.4** ($12167$ is Not Square) | `GolombPowerful.not_square_12167` | Line 33 | Machine-Closed (`omega`, `decide`) |
| **Lemma 3.5** ($12168$ is Not Square) | `GolombPowerful.not_square_12168` | Line 43 | Machine-Closed (`omega`, `decide`) |
| **Combined Counterexample** | `GolombPowerful.golomb_powerful_counterexample` | Line 57 | Machine-Closed |
| **Universal Claim Definition** | `GolombPowerful.GolombConsecutivePowerfulSquaresConjecture` | Line 68 | Exact Formulation |
| **Theorem 4.1 (Main Disproof)** | `GolombPowerful.consecutive_powerful_squares_conjecture_false` | Line 73 | Machine-Closed (0 `sorry`) |

---

## 6. Reproduction and Axiom Audit

### Reproduction Command
In the root directory of `bounty_solves`:
```bash
lake build GolombPowerful
```

### Kernel Verification Output
```text
info: BountySolves/GolombPowerful.lean:85:0: 'GolombPowerful.powerful_12167' depends on axioms: [propext]
info: BountySolves/GolombPowerful.lean:86:0: 'GolombPowerful.powerful_12168' depends on axioms: [propext]
info: BountySolves/GolombPowerful.lean:87:0: 'GolombPowerful.not_square_12167' depends on axioms: [propext, Quot.sound]
info: BountySolves/GolombPowerful.lean:88:0: 'GolombPowerful.not_square_12168' depends on axioms: [propext, Quot.sound]
info: BountySolves/GolombPowerful.lean:89:0: 'GolombPowerful.golomb_powerful_counterexample' depends on axioms: [propext, Quot.sound]
info: BountySolves/GolombPowerful.lean:90:0: 'GolombPowerful.consecutive_powerful_squares_conjecture_false' depends on axioms: [propext, Quot.sound]
Build completed successfully (829 jobs).
```

Zero `sorry`, zero `admit`, zero custom or admitted axioms. Standard Lean 4 core axioms only.
