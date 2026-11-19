# A Formal Proof and Machine-Verified Disproof of Golden-Ratio Convergence for Minimal Stably Complete Sequences (JSP-000288)

**Catalog Identifier:** `JSP-000288` ([The Justin Sun Prize Problem Bank](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0201-0300.md#JSP-000288))  
**Related Reference:** Erdős Problem #346; R. L. Graham (1964); P. Erdős & R. L. Graham (1980); GPT Pro / Liam Price  
**Mathematical Area:** Combinatorial Number Theory / Complete Sequences  
**Mathematical Disproof Credit:** GPT Pro, prompted by Liam Price (catalog-recorded counterexample)  
**Lean 4 Formalization & Exposition:** CreizyLabs (`bountysolves/JSP_000288_StablyCompleteGoldenRatio.lean`)  
**Verification Environment:** Lean `4.35.0-rc2`, Mathlib4 (`9f7aa3a1327bbbc1716bdcedb64b2592e54b9bc7`)

---

## Abstract

Catalog entry `JSP-000288` (Erdős Problem #346) asks whether every strictly increasing positive integer sequence $(a_n)$ that remains complete after deleting any finite subset yet becomes incomplete after deleting any infinite subset must satisfy $a_{n+1}/a_n \to \varphi = (1+\sqrt{5})/2$. The answer is **no**. We formalize an explicit, completely unconditional counterexample `masterSeq : ℕ → ℕ` built via a prefix-sum displacement recurrence $a_{n+1} = \sum_{i<n} a_i + d_n$ satisfying $5 d_n \le a_n$ for all $n \ge 3$. Iterated alternating $\Delta$-block gap-halving stages close every tail to zero-gap completeness (`FiniteDeletionComplete` and `ValueFiniteDeletionComplete`), universal admissibility bounds force $4/3 \le a_{n+1}/a_n \le 2$ and infinite-deletion incompleteness (`InfiniteDeletionIncomplete` and `ValueInfiniteDeletionIncomplete`), and infinitely many periodic ratio jumps $d_K = \lfloor a_K / 5 \rfloor$ force $a_{K+1}/a_K \ge 165/100 > \varphi$, refuting convergence to `Real.goldenRatio`.

---

## 1. Problem Statement and Formal Definitions

### 1.1 Original Problem (`JSP-000288`)
> *Must ratios of consecutive terms in the specified minimal stably complete sequences converge to the golden ratio?*

### 1.2 Canonical Definitions
Let $a : \mathbb{N} \to \mathbb{N}$.
1. **Subset sums and completeness (`JSP_000288.subsetSums`, `JSP_000288.IsCompleteOn`):**
   $$\mathrm{subsetSums}\; a\; I := \Bigl\{\sum_{i \in F} a(i) \;\Big|\; F \text{ finite},\; F \subseteq I\Bigr\},$$
   and `IsCompleteOn a I` holds if there exists $H \in \mathbb{N}$ such that $[H, \infty) \subseteq \mathrm{subsetSums}\; a\; I$.
2. **Minimal stable completeness (`FiniteDeletionComplete`, `ValueFiniteDeletionComplete`, `InfiniteDeletionIncomplete`, `ValueInfiniteDeletionIncomplete`):**
   - Index and value finite deletion leave `a` complete on $D^c$ (resp. $\{i \mid a_i \notin B\}$) for all finite sets $D, B$.
   - Infinite deletion of any infinite index set $D$ (resp. infinite subset $B \subseteq \mathrm{range}(a)$) leaves `a` incomplete.
3. **Consecutive term ratio and uniform ratio gap (`JSP_000288.quotient`, `JSP_000288.HasUniformRatioGap`):**
   `quotient a n = (a (n + 1) : ℝ) / (a n : ℝ)`, and `HasUniformRatioGap a` asserts $\exists \varepsilon > 0,\; \forall n,\; 1 + \varepsilon \le \mathrm{quotient}\; a\; n$.

### 1.3 Statement Correspondence Table

| Mathematical Concept | Lean 4 Declaration in `bountysolves/JSP_000288_StablyCompleteGoldenRatio.lean` |
| --- | --- |
| Explicit counterexample sequence $(a_n)$ | `JSP_000288.masterSeq` |
| Strict monotonicity | `JSP_000288.masterSeq_strictMono` |
| Uniform ratio gap ($1 + 1/3 \le a_{n+1}/a_n$) | `JSP_000288.masterSeq_hasUniformRatioGap` |
| Finite index- and value-deletion completeness | `JSP_000288.masterSeq_finiteDeletionComplete`, `JSP_000288.masterSeq_valueFiniteDeletionComplete` |
| Infinite index- and value-deletion incompleteness | `JSP_000288.masterSeq_infiniteDeletionIncomplete`, `JSP_000288.masterSeq_valueInfiniteDeletionIncomplete` |
| Non-convergence to `Real.goldenRatio` | `JSP_000288.masterSeq_not_tendsto_goldenRatio` |
| Combined full disproof | `JSP_000288.jsp_000288_disproof` |

---

## 2. Complete Mathematical Proof

### 2.1 Prefix-Sum Recurrence and Admissibility
Given any displacement sequence $d : \mathbb{N} \to \mathbb{N}$, define `seqOfDisp d` by initial values $a_0 = 2, a_1 = 3, a_2 = 5, a_3 = 7$ and $a_{n+1} = S_n + d_n$ for $n \ge 3$, where $S_n = \sum_{i<n} a_i$ (`prefSum d n`). Whenever `DispAdmissible d` holds ($5 d_n \le a_n$ for all $n \ge 3$):
1. **Ratio bounds (`seqOfDisp_ratio_bounds`):** $4 a_n \le 3 a_{n+1}$ and $a_{n+1} \le 2 a_n$ for every $n \in \mathbb{N}$. Hence $a$ is strictly increasing (`a n ≥ 2`), satisfies `HasUniformRatioGap` with $\varepsilon = 1/3$, and satisfies $S_n \le a_{n+1}$ for all $n$.
2. **Universal infinite-deletion incompleteness (`seqOfDisp_infiniteDeletionIncomplete`):** Given any infinite index set $D$ and any threshold $H$, choose $i_1, m \in D$ with $\max(i_1, H) < m$. Since $S_m \le a_{m+1}$ and every term exceeds $1$, removing both $i_1$ and $m$ prevents every subset sum of $D^c$ from hitting $a_{m+1} - 1 \ge H$: any sum using indices $\ge m + 1$ exceeds $a_{m+1} - 1$, while any sum using indices $< m$ omits $a_{i_1} \ge 2$ and hence totals at most $S_m - a_{i_1} \le a_{m+1} - 2$.

### 2.2 Alternating $\Delta$-Block Gap-Halving Theorem
For an abstract block $b_0 \le b_1 \le 2 b_0$ obeying $b_{2k} = b_{2k-1} + b_{2k-2} + \Delta$ and $b_{2k+1} = b_{2k} + b_{2k-1} - \Delta$ ($1 \le \Delta \le b_0$):
- Every prefix subset-sum set `blockSubSums b m` is $b_0$-gap-dense on $[0, \mathrm{blockSum}\; b\; m]$.
- Telescoping the even indices yields $b_{2r+2} - j\Delta \in \mathrm{blockSubSums}\; b\; (2r+3)$ for all $0 \le j \le r+1$.
- Combining left and right arithmetic progressions of step $\Delta$ with shifted middle intervals proves `blockPairs_dense_2r5`: for $r \ge 1$ and $b_0 + \Delta \le b_1 - r\Delta$, the $\Delta$-pair set
  $$\{x \mid x \in \Sigma(2r+5) \land x + \Delta \in \Sigma(2r+5)\}$$
  is $(b_1 - r\Delta)$-gap-dense on $[A_r, \mathrm{blockSum}(2r+5) - \Delta - A_r]$, with span $\ge b_{2r+5}$.

Lifting a $W$-dense interval $[L, S_I - L]$ across such a $(2r+5)$-term gadget with $\Delta = \lfloor W/2 \rfloor$ halves the gap $W \mapsto \lceil W/2 \rceil = (W+1)/2$ while preserving $P + 2 L_{\text{new}} \le a_{\text{last}}$ and zero final displacement (`appendHalveStep_invariants`).

### 2.3 Infinite Stage Construction, Completeness, and Ratio Jumps
Starting from `[0, 0]`, each stage `buildStage` runs `halveLoop` from tail $M_q = \text{len}_q + 3$ until $W = 1$ (zero gaps on $[L_q, S_{[M_q, N_q)} - L_q]$ with $P_q + 2 L_q \le a_{N_q - 1}$), pads with $0$-displacements past $2 \max E' + 4$, inserts one jump displacement $d_{K_q} = \lfloor a_{K_q}/5 \rfloor$ with $a_{K_q} \ge 20$, and closes with $0$.
1. **Unbounded inductive extension (`dense_one_extend_of_prefix_bound`):** From $P + 2 L \le a_{N_0 - 1}$ and $4 a_{N_0 - 1} \le 3 a_{N_0}$, admissible growth $5 d_{k-1} \le a_{k-1}$ guarantees $15(P + 2L + d_{k-1}) \le 12 a_{k-1} + 3 a_{k-1} = 15 a_{k-1}$, preserving $1$-density across all future stages (`masterSeq_finiteDeletionComplete`, `masterSeq_valueFiniteDeletionComplete`).
2. **Non-convergence (`masterSeq_not_tendsto_goldenRatio`):** At each jump index $K_q$, $d_{K_q - 1} = 0$ and $a_{K_q} \ge 20$ give $a_{K_q + 1} = S_{K_q} + \lfloor a_{K_q}/5 \rfloor \ge \frac{3}{2} a_{K_q} + \frac{a_{K_q} - 4}{5} \ge \frac{165}{100} a_{K_q}$, whereas $\varphi = (1 + \sqrt{5})/2 < 165/100$ (`goldenRatio_lt_165`). Hence `quotient masterSeq` cannot converge to `Real.goldenRatio`. $\square$

---

## 3. Lean 4 Formalization and Verification Evidence

The self-contained formalization resides in [`bountysolves/JSP_000288_StablyCompleteGoldenRatio.lean`](../bountysolves/JSP_000288_StablyCompleteGoldenRatio.lean) (2,557 lines). All arithmetic and topological limit steps are completely formal, with zero `sorry`, zero `admit`, zero custom axioms, zero `native_decide`, zero approximations, and zero warnings under `-DautoImplicit=false`.

### Exported Theorems
```lean
theorem JSP_000288.masterSeq_strictMono : StrictMono masterSeq
theorem JSP_000288.masterSeq_hasUniformRatioGap : HasUniformRatioGap masterSeq
theorem JSP_000288.masterSeq_finiteDeletionComplete : FiniteDeletionComplete masterSeq
theorem JSP_000288.masterSeq_valueFiniteDeletionComplete : ValueFiniteDeletionComplete masterSeq
theorem JSP_000288.masterSeq_infiniteDeletionIncomplete : InfiniteDeletionIncomplete masterSeq
theorem JSP_000288.masterSeq_valueInfiniteDeletionIncomplete : ValueInfiniteDeletionIncomplete masterSeq
theorem JSP_000288.masterSeq_not_tendsto_goldenRatio :
    ¬ Tendsto (quotient masterSeq) atTop (𝓝 Real.goldenRatio)

theorem JSP_000288.jsp_000288_disproof :
    ∃ a : ℕ → ℕ,
      StrictMono a ∧
      HasUniformRatioGap a ∧
      FiniteDeletionComplete a ∧
      ValueFiniteDeletionComplete a ∧
      InfiniteDeletionIncomplete a ∧
      ValueInfiniteDeletionIncomplete a ∧
      ¬ Tendsto (quotient a) atTop (𝓝 Real.goldenRatio)
```

### Reproduction and Axiom Audit
```bash
lake env lean -DautoImplicit=false bountysolves/JSP_000288_StablyCompleteGoldenRatio.lean
```
Observed `#print axioms` output (exit code `0`, 0 warnings):
```text
'JSP_000288.masterSeq_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000288.masterSeq_hasUniformRatioGap' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000288.masterSeq_finiteDeletionComplete' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000288.masterSeq_valueFiniteDeletionComplete' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000288.masterSeq_infiniteDeletionIncomplete' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000288.masterSeq_valueInfiniteDeletionIncomplete' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000288.masterSeq_not_tendsto_goldenRatio' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000288.jsp_000288_disproof' depends on axioms: [propext, Classical.choice, Quot.sound]
```

---

## 4. References

1. P. Erdős and R. L. Graham, *Old and New Problems and Results in Combinatorial Number Theory*, Monographies de L'Enseignement Mathématique **28**, Geneva (1980), p. 55.
2. R. L. Graham, *A property of Fibonacci numbers*, Fibonacci Quart. **2** (1964), 1–10. DOI: `10.1080/00150517.1964.12431522`.
3. Erdős Problem #346, [https://www.erdosproblems.com/346](https://www.erdosproblems.com/346).
