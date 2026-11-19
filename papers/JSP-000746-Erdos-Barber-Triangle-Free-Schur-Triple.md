# Independent Schur Triples in Every Triangle-Free Graph on the Integers: A Pure Propositional Kernel-Checked Proof at Threshold $N = 18$ (JSP-000746 / Erdős Problem #895)

**Catalog Identifier:** `JSP-000746` ([The Justin Sun Prize Problem Bank](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0701-0800.md#JSP-000746))  
**Original Problem Reference:** Erdős Problem #895 (posed by P. Erdős and A. Hajnal, ca. 1995)  
**Mathematical Area:** Additive Combinatorics / Graph Theory / Ramsey Theory  
**Original Mathematical Solution Attribution:** Ben Barber (SAT-assisted proof of the sharp threshold $N = 18$, personal communication); earlier qualitative infinitary resolution by T. Łuczak, V. Rödl, and T. Schoen (1998)  
**Lean 4 Formalization & Exposition:** CreizyLabs (`bountysolves/JSP_000746_TriangleFreeSchurTriple.lean`)  
**Verification Environment:** Lean `4.35.0-rc2`, Mathlib4 (`9f7aa3a1327bbbc1716bdcedb64b2592e54b9bc7`)

---

## Abstract

Catalog entry `JSP-000746` (Erdős Problem #895) asks whether every triangle-free graph on the integers must contain three distinct pairwise non-adjacent vertices $a, b, c$ satisfying $a + b = c$. Confirming Ben Barber's sharp finite threshold $N = 18$, we establish that **every** triangle-free simple graph on $\{1, \dots, 18\}$ contains three distinct vertices $1 \le x < y < x + y \le 18$ forming an independent set, and immediately deduce the full statements over $\mathbb{N}$ and $\mathbb{Z}$. Crucially, rather than relying on external SAT checker trust (`native_decide`, `bv_decide`, or `Lean.ofReduceBool`), our Lean 4 formalization compiles a trimmed LRAT refutation directly into **pure continuation-passing-style (CPS) Lean 4 lambda terms** (`fun`, `let`, `Classical.byContradiction`) verified directly by Lean's type-checking kernel with zero reflection axioms, zero `sorry`, zero `admit`, and strictly `[propext, Classical.choice, Quot.sound]`.

---

## 1. Problem Statement and Formal Definitions

### 1.1 Original Problem (`JSP-000746` / Erdős #895)
> *Must every triangle-free graph on the integers have three independent vertices, one equal to the sum of the other two?*

### 1.2 Formal Definitions in Lean 4

In `bountysolves/JSP_000746_TriangleFreeSchurTriple.lean`:
- Graphs are represented canonically via Mathlib's `SimpleGraph V` (symmetric, irreflexive adjacency relation `G.Adj`).
- Triangle-freeness is represented canonically via Mathlib's `G.CliqueFree 3` (no 3-element clique in `G`). We prove in `no_triangle_of_cliqueFree` that `G.CliqueFree 3` implies $\forall a, b, c \in V,\; G.\mathrm{Adj}\;a\;b \land G.\mathrm{Adj}\;b\;c \land G.\mathrm{Adj}\;a\;c \implies \mathrm{False}$.

### 1.3 Statement Correspondence Table

| Mathematical Theorem | Lean 4 Declaration in `bountysolves/JSP_000746_TriangleFreeSchurTriple.lean` |
| --- | --- |
| Sharp finite theorem on $\{1, \dots, 18\}$ (`Fin 18`) | `JSP_000746.jsp_000746_fin18` |
| Positive-integer theorem on $\mathbb{N}$ ($1 \le x < y$, $x + y \le 18$) | `JSP_000746.jsp_000746_nat` |
| Full integer theorem on $\mathbb{Z}$ ($a, b, c$ distinct, $a + b = c$) | `JSP_000746.jsp_000746_int` |

---

## 2. Proof Method: Direct CPS Propositional LRAT Refutation

### 2.1 Reduction to Propositional Unsatisfiability on $\{1, \dots, 18\}$
Let $G$ be a triangle-free simple graph on $V = \{1, \dots, 18\}$ (indexed by `Fin 18` via $i \mapsto i + 1$), and suppose for contradiction that $G$ has no independent triple $\{x, y, x + y\}$ with $1 \le x < y$ and $x + y \le 18$. Introduce the $\binom{18}{2} = 153$ atomic edge propositions $E(i, j) := G.\mathrm{Adj}(i, j)$ for $1 \le i < j \le 18$. Then $E$ satisfies the CNF formula $\Phi_{18}$ consisting of:
1. **Triangle-freeness clauses** ($\binom{18}{3} = 816$ clauses): for all $1 \le i < j < k \le 18$,
   $$\neg E(i, j) \lor \neg E(j, k) \lor \neg E(i, k).$$
2. **No-independent-Schur-triple clauses** ($73$ clauses): for all $1 \le x < y$ with $x + y \le 18$,
   $$E(x, y) \lor E(x, x + y) \lor E(y, x + y).$$

### 2.2 Continuation-Passing Style (CPS) Kernel Verification
To verify $\Phi_{18} \vdash \bot$ directly inside Lean 4's kernel without invoking `native_decide`, `Lean.ofReduceBool`, or any external checker:
- Every clause $C = (L_1 \lor L_2 \lor \dots \lor L_k)$ is represented by its classical negation-normal CPS type:
  $$\llbracket C \rrbracket := \overline{L_1} \to \overline{L_2} \to \cdots \to \overline{L_k} \to \mathrm{False},$$
  where $\overline{E(i, j)} = \neg E(i, j)$ and $\overline{\neg E(i, j)} = E(i, j)$.
- Each original triangle clause has immediate proof `ctx.tri` (type $E(i, j) \to E(j, k) \to E(i, k) \to \mathrm{False}$), and each original Schur clause has immediate proof `ctx.sch` (type $\neg E(x, y) \to \neg E(x, z) \to \neg E(y, z) \to \mathrm{False}$).
- A backward-trimmed LRAT derivation from $\Phi_{18}$ to the empty clause $\bot$ uses $700$ original clauses, $1{,}838$ derived clauses, and $29{,}856$ unit-propagation hints. Each LRAT clause derivation $r_m : \llbracket C_m \rrbracket$ assumes the negated literals of $C_m$ and replays its unit-propagation chain strictly via local lambda terms:
  - Propagating a negative literal $\neg E(u, v)$ from an earlier clause $h$ requires only $\lambda p.\, h(\dots, p, \dots) : \neg E(u, v)$.
  - Propagating a positive literal $E(u, v)$ from an earlier clause $h$ applies `Classical.byContradiction (fun n => h ... n) : E(u, v)`.
  - The final conflict hint has all of its CPS hypotheses in scope and returns `False` directly.
- The final theorem `r1837 ctx : False` yields a direct kernel-checked refutation of `RefCtx`, proving `jsp_000746_fin18`.

### 2.3 Lifting to $\mathbb{N}$ and $\mathbb{Z}$
1. **Theorem on $\mathbb{N}$ (`jsp_000746_nat`):** Given any triangle-free `G : SimpleGraph ℕ`, pull `G` back along the embedding $f : \mathrm{Fin}\,18 \hookrightarrow \mathbb{N}$, $i \mapsto i + 1$, forming $G_{18} = G.\mathrm{comap}\;f$. Any $3$-clique in $G_{18}$ maps under $f$ to a $3$-clique in $G$, so $G_{18}$ is triangle-free. Applying `jsp_000746_fin18` yields $1 \le x < y$ with $x + y \le 18$ such that $\{x, y, x + y\}$ is independent in $G$.
2. **Theorem on $\mathbb{Z}$ (`jsp_000746_int`):** Given any triangle-free `G : SimpleGraph ℤ`, pull `G` back along `Int.ofNat : ℕ ↪ ℤ` and apply `jsp_000746_nat`, obtaining three pairwise distinct positive integers $a, b, c \in \mathbb{Z}$ with $a + b = c$ that are pairwise non-adjacent in $G$. $\square$

---

## 3. Lean 4 Formalization and Verification Evidence

The complete formalization resides in [`bountysolves/JSP_000746_TriangleFreeSchurTriple.lean`](../bountysolves/JSP_000746_TriangleFreeSchurTriple.lean) (32,535 lines). Every propositional derivation step is checked directly by the Lean 4 kernel with zero `sorry`, zero `admit`, zero `native_decide`, zero `ofReduceBool`, and zero custom axioms.

### Exported Theorems
```lean
theorem JSP_000746.jsp_000746_fin18 (G : SimpleGraph (Fin 18)) (hG : G.CliqueFree 3) :
    ∃ x y z : Fin 18, x < y ∧ (x.1 + 1) + (y.1 + 1) = z.1 + 1 ∧
      ¬ G.Adj x y ∧ ¬ G.Adj x z ∧ ¬ G.Adj y z

theorem JSP_000746.jsp_000746_nat (G : SimpleGraph ℕ) (hG : G.CliqueFree 3) :
    ∃ x y : ℕ, 0 < x ∧ x < y ∧ x + y ≤ 18 ∧
      ¬ G.Adj x y ∧ ¬ G.Adj x (x + y) ∧ ¬ G.Adj y (x + y)

theorem JSP_000746.jsp_000746_int (G : SimpleGraph ℤ) (hG : G.CliqueFree 3) :
    ∃ a b c : ℤ, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a + b = c ∧
      ¬ G.Adj a b ∧ ¬ G.Adj a c ∧ ¬ G.Adj b c
```

### Reproduction and Axiom Audit
```bash
lake env lean bountysolves/JSP_000746_TriangleFreeSchurTriple.lean
```
Observed `#print axioms` output (exit code `0`, 0 warnings):
```text
'JSP_000746.jsp_000746_fin18' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000746.jsp_000746_nat' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000746.jsp_000746_int' depends on axioms: [propext, Classical.choice, Quot.sound]
```

---

## 4. References

1. T. Łuczak, V. Rödl, and T. Schoen, *Independent finite sums in graphs defined on the natural numbers*, Discrete Math. **181** (1998), 289–294. DOI: `10.1016/S0012-365X(97)00064-2`.
2. B. Barber, *SAT-assisted proof of the threshold $N = 18$ for independent Schur triples in triangle-free graphs*, personal communication cited on [Erdős Problem #895](https://www.erdosproblems.com/895).
3. The Justin Sun Prize Problem Bank, entry `JSP-000746`, `problems/catalog-0701-0800.md`.
