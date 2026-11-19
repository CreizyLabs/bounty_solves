# A Formal Proof and Machine-Verified Disproof of Collinearity in Finite-Step Walks in $\mathbb{Z}^3$ (JSP-000183)

**Catalog Identifier:** `JSP-000183` ([The Justin Sun Prize Problem Bank](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0101-0200.md#JSP-000183))  
**Related Reference:** Erdős Problem #193; J. L. Gerver & L. M. Ramsey (1979); S. Cambie & E. Kälviäinen (2026)  
**Mathematical Area:** Combinatorial Geometry / Lattice Walks / $2$-adic Valuations  
**Original Mathematical Disproof:** S. Cambie & E. Kälviäinen, *An infinite small-step $\mathbb{Z}^3$-walk with no collinear triple*, `arXiv:2609.01766` (2026)  
**Lean 4 Formalization & Exposition:** CreizyLabs (`bountysolves/JSP_000183_SmallStepZ3WalkNoCollinear.lean`)  
**Verification Environment:** Lean `4.35.0-rc2`, Mathlib4 (`9f7aa3a1327bbbc1716bdcedb64b2592e54b9bc7`)

---

## Abstract

Catalog entry `JSP-000183` (Erdős Problem #193) asks whether every infinite walk in three-dimensional space using a finite set of step vectors must contain three collinear points. Following Stijn Cambie and Eero Kälviäinen's 2026 construction (`arXiv:2609.01766`), we give a self-contained elementary proof and unconditional Lean 4 disproof using the binary-weight Gaussian lattice walk $z_n = \sum_{r<n} i^{s_2(r)} \in \mathbb{Z}[i]$ embedded into $\mathbb{Z}^3$ via $P(n) = (2 z_n + c(\alpha(n)),\; 4n + \alpha(n))$, where $\alpha(n) \equiv s_2(n) \pmod 4$. All step vectors $P(n+1) - P(n)$ lie in the finite box $\{-2, -1, 0, 1, 2\}^2 \times \{1, \dots, 7\}$, $P$ is injective, and the universal $2$-adic valuation law $v_2(\|w_n - w_m\|^2) = v_2(h_n - h_m)$ for all $m < n$ rules out every collinear triple in both $\mathbb{Z}^3$ and Euclidean $\mathbb{R}^3$.

---

## 1. Problem Statement and Formal Definitions

### 1.1 Original Problem (`JSP-000183`)
> *Must an infinite walk in three-dimensional space using a finite set of step vectors visit three collinear points?*

### 1.2 Canonical Construction and Definitions
1. **Binary digit sum and mod-$4$ automaton (`JSP_000183.s2`, `JSP_000183.alpha`):**
   Let $s_2(n)$ be the number of $1$s in the binary expansion of $n \in \mathbb{N}$, and let $\alpha(n) \in \mathrm{Fin}\; 4$ be $s_2(n) \bmod 4$.
2. **Planar Gaussian walk (`JSP_000183.zWalk`):**
   Set `unitStep 0 = (1, 0)`, `unitStep 1 = (0, 1)`, `unitStep 2 = (-1, 0)`, `unitStep 3 = (0, -1)` (representing $i^a \in \mathbb{Z}[i]$) and define
   $$z_0 = (0, 0), \qquad z_{n+1} = z_n + \mathrm{unitStep}(\alpha(n)).$$
3. **3D small-step walk (`JSP_000183.wWalk`, `JSP_000183.hWalk`, `JSP_000183.P`, `JSP_000183.PReal`):**
   With corners `corner 0 = (0, 0)`, `corner 1 = (0, 1)`, `corner 2 = (-1, 1)`, `corner 3 = (-1, 0)`:
   $$w_n = 2 z_n + \mathrm{corner}(\alpha(n)) \in \mathbb{Z}^2, \qquad h_n = 4n + \alpha(n) \in \mathbb{N}, \qquad P(n) = (w_n, h_n) \in \mathbb{Z}^3,$$
   and `PReal n : Fin 3 → ℝ` is its canonical inclusion into $\mathbb{R}^3$.
4. **Squared Euclidean norm (`JSP_000183.sqNorm`):**
   For $(x, y) \in \mathbb{Z}^2$, $\mathrm{sqNorm}(x, y) = |x|^2 + |y|^2 \in \mathbb{N}$.

### 1.3 Statement Correspondence Table

| Mathematical Concept | Lean 4 Declaration in `bountysolves/JSP_000183_SmallStepZ3WalkNoCollinear.lean` |
| --- | --- |
| Planar Gaussian walk $2$-adic valuation law | `JSP_000183.v2_sqNorm_zWalk_diff` |
| Embedded planar walk universal $2$-adic law | `JSP_000183.v2_sqNorm_wWalk_diff` |
| Small-step $\mathbb{Z}^3$ finite step set & injectivity | `JSP_000183.int_steps_finite`, `JSP_000183.step_in_small_box`, `JSP_000183.P_injective` |
| Non-collinearity in $\mathbb{Z}^3$ and $\mathbb{R}^3$ ($m < n < k$) | `JSP_000183.no_three_collinear_int`, `JSP_000183.no_three_collinear_real` |
| Main $\mathbb{Z}^3$ small-step walk disproof | `JSP_000183.jsp_000183_small_step_z3_walk_no_collinear_triple` |
| Main Euclidean $\mathbb{R}^3$ (`Collinear ℝ`) disproof | `JSP_000183.jsp_000183_no_collinear_triple_euclidean` |

---

## 2. Complete Mathematical Proof

### Lemma 2.1 (Self-Similar Doubling Recurrences)
From $s_2(2n) = s_2(n)$ and $s_2(2n+1) = s_2(n) + 1$, we have $\alpha(2n) = \alpha(n)$ and $\alpha(2n+1) \equiv \alpha(n) + 1 \pmod 4$. Since $i^a + i^{a+1} = (1 + i) i^a$ for every $a \in \mathrm{Fin}\; 4$ (`unitStep_pair`), induction gives for all $n \in \mathbb{N}$:
$$z_{2n} = (1 + i) z_n, \qquad z_{2n+1} = (1 + i) z_n + i^{\alpha(n)},$$
where multiplication by $1 + i$ acts on $\mathbb{Z}^2$ as $\mathrm{rot1i}(x, y) = (x - y, x + y)$ and satisfies $\|(1 + i)v\|^2 = 2 \|v\|^2$.

### Theorem 2.2 (Planar $2$-adic Valuation Identity)
Whenever $m < n$ and $\alpha(m) = \alpha(n)$, we have $z_n \ne z_m$ and
$$v_2\bigl(\|z_n - z_m\|^2\bigr) = v_2(n - m).$$

**Proof.** We induct strongly on $n$.
- *Same parity ($m \equiv n \pmod 2$):* Writing $n = 2q + r$ and $m = 2p + r$ with $p < q$, the condition $\alpha(m) = \alpha(n)$ forces $\alpha(p) = \alpha(q)$, so $z_n - z_m = \mathrm{rot1i}(z_q - z_p)$. Thus $\|z_n - z_m\|^2 = 2 \|z_q - z_p\|^2 \ne 0$, and $v_2(\|z_n - z_m\|^2) = 1 + v_2(\|z_q - z_p\|^2) = 1 + v_2(q - p) = v_2(2(q - p)) = v_2(n - m)$.
- *Opposite parity ($m \not\equiv n \pmod 2$):* Then $n - m$ is odd ($v_2(n - m) = 0$) and $z_n - z_m = \mathrm{rot1i}(z_q - z_p) \pm i^a$. Since $\mathrm{rot1i}(x, y) = (x - y, x + y)$ has equal-parity coordinates while every unit step $(\pm 1, 0), (0, \pm 1)$ has opposite-parity coordinates, $\|z_n - z_m\|^2$ is odd ($v_2(\|z_n - z_m\|^2) = 0$). $\square$

### Theorem 2.3 (Universal $2$-adic Valuation Law for $w_n$)
For **all** integers $0 \le m < n$, $\|w_n - w_m\|^2 \ne 0$ and $v_2(\|w_n - w_m\|^2) = v_2(h_n - h_m)$.

**Proof.**
- If $\alpha(m) = \alpha(n)$, then $w_n - w_m = 2(z_n - z_m)$ and $h_n - h_m = 4(n - m)$, so $v_2(\|w_n - w_m\|^2) = 2 + v_2(\|z_n - z_m\|^2) = 2 + v_2(n - m) = v_2(h_n - h_m)$ by Theorem 2.2.
- If $a = \alpha(m) \ne \alpha(n) = b$, checking the $12$ off-diagonal pairs $(a, b) \in (\mathrm{Fin}\; 4)^2$ shows that $\|2(z_n - z_m) + c(b) - c(a)\|^2 \equiv \|c(b) - c(a)\|^2 \pmod 4$ equals $1 \pmod 2$ precisely when $b \not\equiv a \pmod 2$ (matching $h_n - h_m \equiv b - a \equiv 1 \pmod 2$), and equals $2 \pmod 4$ precisely when $(b - a) \equiv 2 \pmod 4$ (matching $h_n - h_m \equiv 2 \pmod 4$). In every case $v_2(\|w_n - w_m\|^2) = v_2(h_n - h_m)$. $\square$

### Theorem 2.4 (Small Steps, Injectivity, and No Collinear Triple)
The walk $P(n)$ uses at most $16$ step vectors, all in $\{-2, -1, 0, 1, 2\}^2 \times \{1, \dots, 7\}$, is injective ($h_n$ is strictly increasing), and avoids all collinear triples in $\mathbb{Z}^3$ and $\mathbb{R}^3$.

**Proof.** Expanding $w_{n+1} - w_n = 2\,\mathrm{unitStep}(\alpha(n)) + \mathrm{corner}(\alpha(n+1)) - \mathrm{corner}(\alpha(n))$ and $h_{n+1} - h_n = 4 + \alpha(n+1) - \alpha(n)$ depends solely on $(\alpha(n), \alpha(n+1)) \in (\mathrm{Fin}\; 4)^2$, yielding bounds $[-2, 2]^2 \times [1, 7]$.

Suppose $m < n < k$ gave collinear points $P(m), P(n), P(k)$ in $\mathbb{R}^3$ (or linearly dependent difference vectors in $\mathbb{Z}^3$). Comparing the first two coordinates against the third height coordinate yields:
$$b (w_n - w_m) = a (w_k - w_m), \qquad c (w_n - w_m) = a (w_k - w_n),$$
where $a = h_n - h_m > 0$, $c = h_k - h_n > 0$, and $b = h_k - h_m = a + c > 0$. Taking squared norms gives
$$b^2 \|w_n - w_m\|^2 = a^2 \|w_k - w_m\|^2, \qquad c^2 \|w_n - w_m\|^2 = a^2 \|w_k - w_n\|^2.$$
Applying $v_2$ and substituting Theorem 2.3 produces $2 v_2(b) + v_2(a) = 2 v_2(a) + v_2(b)$ and $2 v_2(c) + v_2(a) = 2 v_2(a) + v_2(c)$, forcing $v_2(a) = v_2(c) = v_2(a + c)$. However, adding two non-zero naturals of equal $2$-adic valuation strictly increases $2$-adic valuation ($v_2(a) < v_2(a + c)$), a contradiction. $\square$

---

## 3. Lean 4 Formalization and Verification Evidence

The formal proof resides in [`bountysolves/JSP_000183_SmallStepZ3WalkNoCollinear.lean`](../bountysolves/JSP_000183_SmallStepZ3WalkNoCollinear.lean) (789 lines). It uses exact integer, natural, and real arithmetic with zero `sorry`, zero `admit`, zero custom axioms, zero `native_decide`, zero approximations, and zero warnings under `-DautoImplicit=false`.

### Exported Theorems
```lean
theorem JSP_000183.v2_sqNorm_zWalk_diff :
    ∀ n m : ℕ, m < n → alpha m = alpha n →
      sqNorm ((zWalk n).1 - (zWalk m).1, (zWalk n).2 - (zWalk m).2) ≠ 0 ∧
      (sqNorm ((zWalk n).1 - (zWalk m).1, (zWalk n).2 - (zWalk m).2)).factorization 2 =
        (n - m).factorization 2

theorem JSP_000183.v2_sqNorm_wWalk_diff {m n : ℕ} (hmn : m < n) :
    sqNorm ((wWalk n).1 - (wWalk m).1, (wWalk n).2 - (wWalk m).2) ≠ 0 ∧
    (sqNorm ((wWalk n).1 - (wWalk m).1, (wWalk n).2 - (wWalk m).2)).factorization 2 =
      (hWalk n - hWalk m).factorization 2

theorem JSP_000183.jsp_000183_small_step_z3_walk_no_collinear_triple :
    ∃ (walk : ℕ → ℤ × ℤ × ℤ),
      Function.Injective walk ∧
      (Set.range (fun n : ℕ =>
        ((walk (n + 1)).1 - (walk n).1,
         (walk (n + 1)).2.1 - (walk n).2.1,
         (walk (n + 1)).2.2 - (walk n).2.2))).Finite ∧
      (∀ n : ℕ,
        let d := ((walk (n + 1)).1 - (walk n).1,
                  (walk (n + 1)).2.1 - (walk n).2.1,
                  (walk (n + 1)).2.2 - (walk n).2.2);
        -2 ≤ d.1 ∧ d.1 ≤ 2 ∧ -2 ≤ d.2.1 ∧ d.2.1 ≤ 2 ∧ 1 ≤ d.2.2 ∧ d.2.2 ≤ 7) ∧
      (∀ m n k : ℕ, m < n → n < k →
        ¬ Collinear ℝ ({PReal m, PReal n, PReal k} : Set (Fin 3 → ℝ))) ∧
      (∀ m n k : ℕ, m < n → n < k →
        ¬ ∃ (r s : ℤ), (r ≠ 0 ∨ s ≠ 0) ∧
          r * ((walk n).1 - (walk m).1) + s * ((walk k).1 - (walk m).1) = 0 ∧
          r * ((walk n).2.1 - (walk m).2.1) + s * ((walk k).2.1 - (walk m).2.1) = 0 ∧
          r * ((walk n).2.2 - (walk m).2.2) + s * ((walk k).2.2 - (walk m).2.2) = 0)

theorem JSP_000183.jsp_000183_no_collinear_triple_euclidean :
    ∃ (f : ℕ → Fin 3 → ℝ),
      Function.Injective f ∧
      (Set.range (fun n : ℕ => f (n + 1) - f n)).Finite ∧
      ∀ m n k : ℕ, m ≠ n → m ≠ k → n ≠ k →
        ¬ Collinear ℝ ({f m, f n, f k} : Set (Fin 3 → ℝ))
```

### Reproduction and Axiom Audit
```bash
lake env lean -DautoImplicit=false bountysolves/JSP_000183_SmallStepZ3WalkNoCollinear.lean
```
Observed `#print axioms` output (exit code `0`, 0 warnings):
```text
'JSP_000183.v2_sqNorm_zWalk_diff' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000183.v2_sqNorm_wWalk_diff' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000183.jsp_000183_small_step_z3_walk_no_collinear_triple' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000183.jsp_000183_no_collinear_triple_euclidean' depends on axioms: [propext, Classical.choice, Quot.sound]
```

---

## 4. References

1. S. Cambie and E. Kälviäinen, *An infinite small-step $\mathbb{Z}^3$-walk with no collinear triple*, `arXiv:2609.01766` (2026).
2. J. L. Gerver and L. M. Ramsey, *On certain sequences of lattice points*, Pacific J. Math. **83** (1979), 357–363. DOI: `10.2140/pjm.1979.83.357`.
3. Erdős Problem #193, [https://www.erdosproblems.com/193](https://www.erdosproblems.com/193).
