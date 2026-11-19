# No Uniform Cardinal Bound on the Chromatic Number of Countable Set Families Avoiding Pairwise Intersection Size Two (JSP-000490 / Erdős Problem #603)

**Catalog Identifier:** `JSP-000490` ([The Justin Sun Prize Problem Bank](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000490))  
**Original Problem Reference:** Erdős Problem #603 (posed by Péter Komjáth, ca. 1987)  
**Mathematical Area:** Combinatorics / Infinitary Set Theory  
**Mathematical Solution Attribution:** GPT-5.4 Pro, prompted by Przemyslaw Chojecki (no uniform cardinal bound)  
**Lean 4 Formalization & Exposition:** CreizyLabs (`bountysolves/JSP_000490_Erdos603_ForbiddenIntersectionTwo.lean`)  
**Verification Environment:** Lean `4.35.0-rc2`, Mathlib4 (`9f7aa3a1327bbbc1716bdcedb64b2592e54b9bc7`)

---

## Abstract

Catalog problem `JSP-000490` (Erdős Problem #603, posed by P. Komjáth) asks whether there exists a uniform cardinal bound $\kappa$ on the chromatic number of every family $\mathcal{F}$ of countably infinite sets satisfying $|A \cap B| \ne 2$ for all distinct $A, B \in \mathcal{F}$. We present a complete, universe-polymorphic negative resolution: for *every* color type $C$ (equivalently, every cardinal $\kappa$), there exists a ground set $X$ and a family $\mathcal{F} \subseteq \mathcal{P}(X)$ of countably infinite subsets whose union is $X$ and whose pairwise intersections never have cardinality $2$, such that every $C$-coloring of $X$ produces a monochromatic member $A \in \mathcal{F}$. The proof constructs $\mathcal{F}$ from unordered pairs of countably infinite subsets of a sufficiently large base set $V$ (exploiting the arithmetic fact $\binom{k}{2} \ne 2$ for all cardinals $k$) and applies a self-contained transfinite proof of the countable Erdős–Rado partition theorem $(2^{\kappa})^+ \to (\aleph_0)^2_{\kappa}$. The entire proof—including the transfinite Erdős–Rado theorem—is formalized unconditionally in Lean 4 without `sorry`, `admit`, or custom axioms.

---

## 1. Problem Statement and Formal Definitions

### 1.1 Original Problem (`JSP-000490` / Erdős #603)
> *How many colors suffice to avoid monochromatic members of a family of countably infinite sets whose pairwise intersections never have size two?*

Equivalently: does there exist a cardinal $\kappa$ such that every family $\mathcal{F}$ of countably infinite sets satisfying $|A \cap B| \ne 2$ for all distinct $A, B \in \mathcal{F}$ admits a coloring of $\bigcup \mathcal{F}$ with $\kappa$ colors having no monochromatic member $A \in \mathcal{F}$?

### 1.2 Formal Definitions in Lean 4

In `bountysolves/JSP_000490_Erdos603_ForbiddenIntersectionTwo.lean`, working universe-polymorphically in `universe u`:

1. **Pair-set ground space (`JSP_000490.Pair`, `JSP_000490.pairSet`):**
   ```lean
   abbrev Pair (V : Type u) : Type u := { s : Finset V // s.card = 2 }
   def pairSet {V : Type u} (S : Set V) : Set (Pair V) := { e | ∀ x ∈ e.1, x ∈ S }
   ```
2. **Counterexample family (`JSP_000490.CounterexampleGround`, `JSP_000490.counterexampleFamily`):**
   Given a color type `C : Type u`, take `V := Set (Set (C ⊕ ULift.{u} ℕ))`, ground set `CounterexampleGround C := Pair V`, and `counterexampleFamily C := { pairSet S | S : Set V, #S = ℵ₀ }`.

### 1.3 Statement Correspondence Table

| Mathematical Statement | Lean 4 Declaration in `bountysolves/JSP_000490_Erdos603_ForbiddenIntersectionTwo.lean` |
| --- | --- |
| Pairwise intersection of members never has size $2$ | `JSP_000490.counterexampleFamily_inter_ne_two` |
| Countable Erdős–Rado partition theorem $(2^\mu < |V| \Rightarrow V \to (\aleph_0)^2_C)$ | `JSP_000490.erdos_rado_countable` |
| Counterexample family for arbitrary color type `C : Type u` | `JSP_000490.jsp_000490_for_every_color_type` |
| No uniform cardinal bound $\kappa : \mathrm{Cardinal}.\{u\}$ | `JSP_000490.jsp_000490_no_uniform_cardinal_bound` |

---

## 2. Complete Mathematical Proof

### Lemma 2.1 (Pair-Set Intersection Cardinality Avoids $2$)
For any sets $S, T \subseteq V$,
$$\mathrm{pairSet}(S) \cap \mathrm{pairSet}(T) = \mathrm{pairSet}(S \cap T),$$
and for every subset $U \subseteq V$, $|\mathrm{pairSet}(U)| \ne 2$.

**Proof.**
An unordered pair $\{u, v\}$ ($u \ne v$) has both endpoints in $S$ and both endpoints in $T$ if and only if both endpoints lie in $S \cap T$, establishing the intersection identity. Now suppose for contradiction that $|\mathrm{pairSet}(U)| = 2$.
- If $U$ has fewer than $2$ elements, $\mathrm{pairSet}(U) = \emptyset$, so $|\mathrm{pairSet}(U)| = 0 \ne 2$.
- If $U$ has exactly $2$ elements $\{a, b\}$, $\mathrm{pairSet}(U) = \{\{a, b\}\}$, so $|\mathrm{pairSet}(U)| = 1 \ne 2$.
- If $U$ has at least $3$ distinct elements $a, b, c \in U$, then $\{a, b\}, \{a, c\}, \{b, c\}$ are three pairwise distinct elements of $\mathrm{pairSet}(U)$, so $|\mathrm{pairSet}(U)| \ge 3 > 2$.
In all cases $|\mathrm{pairSet}(U)| \ne 2$. $\square$

### Lemma 2.2 (Cardinality of Pair-Sets of Countably Infinite Sets)
If $|S| = \aleph_0$, then $|\mathrm{pairSet}(S)| = \aleph_0$.

**Proof.**
Fix a bijection $e : \mathbb{N} \simeq S$. The map $n \mapsto \{e(0), e(n+1)\}$ injects $\mathbb{N}$ into $\mathrm{pairSet}(S)$, giving $\aleph_0 \le |\mathrm{pairSet}(S)|$. Conversely, sending each $\{u, v\} \in \mathrm{pairSet}(S)$ to an ordered pair $(u, v) \in S \times S$ injects $\mathrm{pairSet}(S)$ into $S \times S$, giving $|\mathrm{pairSet}(S)| \le \aleph_0 \cdot \aleph_0 = \aleph_0$. By Cantor–Bernstein, $|\mathrm{pairSet}(S)| = \aleph_0$. $\square$

### Theorem 2.3 (Countable Erdős–Rado Partition Theorem)
Let $C$ be any color type, let $K = C \oplus \mathrm{ULift}\,\mathbb{N}$ (so $\mu := |K| \ge \aleph_0$ and $|C| \le \mu$), and let $V = \mathcal{P}(\mathcal{P}(K))$ (so $|V| = 2^{2^\mu} \ge (2^\mu)^+$). Then for every coloring $f : \mathrm{Pair}(V) \to C$, there exist a countably infinite subset $S \subseteq V$ ($|S| = \aleph_0$) and a color $c \in C$ such that $f(\{u, v\}) = c$ for all distinct $u, v \in S$.

**Proof.**
Let $\kappa = (2^\mu)^+$, and embed the initial ordinal $\mathrm{ToType}(\mathrm{ord}(\kappa))$ injectively into $V$ (valid since $\kappa \le 2^{2^\mu} = |V|$). We construct a binary-style $K$-branching Erdős–Rado tree of height $\mu^+$ indexed by $\mathrm{ToType}(\mathrm{ord}(\mu^+))$ via transfinite recursion on the well-order $<$ of $\mathrm{ord}(\mu^+)$:
- Associate to each $\alpha < \mathrm{ord}(\mu^+)$ a partial coloring profile $p(\alpha) : \mathrm{Iio}(\alpha) \to K$ and a node $x(\alpha) \in V$ such that the sets $B_\alpha = \{v \in V \mid \forall \beta < \alpha,\; v \ne x(\beta) \land \tilde{f}(\{x(\beta), v\}) = p(\alpha)(\beta)\}$ remain nonempty, where $\tilde{f} : \mathrm{Pair}(V) \to K$ is $f$ composed with $\mathrm{Sum.inl} : C \hookrightarrow K$.
- At each step, the set of nodes constructed strictly before stage $\mu^+$ has cardinality at most $\sum_{\alpha < \mathrm{ord}(\mu^+)} |K|^{|\alpha|} \le \mu^+ \cdot 2^\mu = 2^\mu < (2^\mu)^+ \le |V|$, so there exists an unused vertex $v^* \in V$ outside the entire tree.
- Following the unique branch guided by $v^*$ (at stage $\alpha$, choosing color $\tilde{f}(\{x(\alpha), v^*\})$) yields a strictly increasing sequence of stages $\alpha_0 < \alpha_1 < \cdots$? More directly: the branch $B = \{x(\alpha) \mid \alpha < \mathrm{ord}(\mu^+)\}$ has cardinality $\mu^+ > |K|$. For every $\alpha < \beta < \mathrm{ord}(\mu^+)$, $\tilde{f}(\{x(\alpha), x(\beta)\}) = \tilde{f}(\{x(\alpha), v^*\})$ depends **only** on $\alpha$.
- By the infinite pigeonhole principle (`Cardinal.lt_ord` / cofinality since $|C| \le \mu < \mu^+$), some color $c \in C$ occurs on a subset $I \subseteq \mathrm{ord}(\mu^+)$ of cardinality $\ge \aleph_0$. Extracting a countably infinite subset $J \subseteq I$ gives $S = x(J) \subseteq V$ with $|S| = \aleph_0$ on which $f$ is identically $c$. $\square$

### Theorem 2.4 (Negative Resolution of `JSP-000490` / Erdős #603)
For every cardinal $\kappa$ (and every color type $C$), there exists a ground set $X$ and a family $\mathcal{F} \subseteq \mathcal{P}(X)$ such that:
1. $\bigcup \mathcal{F} = X$;
2. $|A| = \aleph_0$ for all $A \in \mathcal{F}$;
3. $|A \cap B| \ne 2$ for all distinct $A, B \in \mathcal{F}$;
4. Every coloring $f : X \to C$ admits a monochromatic $A \in \mathcal{F}$.

**Proof.**
Given $C$, set $K = C \oplus \mathrm{ULift}\,\mathbb{N}$, $V = \mathcal{P}(\mathcal{P}(K))$, $X = \mathrm{Pair}(V)$, and $\mathcal{F} = \{\mathrm{pairSet}(S) \mid S \subseteq V,\; |S| = \aleph_0\}$.
- Every pair $\{u, v\} \in X$ embeds into a countably infinite subset $S \subseteq V$ (since $V$ is infinite), so $\bigcup \mathcal{F} = X$.
- By Lemma 2.2, every member of $\mathcal{F}$ has cardinality $\aleph_0$.
- By Lemma 2.1, no two members of $\mathcal{F}$ intersect in size $2$.
- By Theorem 2.3, every coloring $f : X \to C$ has a monochromatic $\mathrm{pairSet}(S) \in \mathcal{F}$. $\square$

---

## 3. Lean 4 Formalization and Verification Evidence

The complete universe-polymorphic Lean 4 proof resides in [`bountysolves/JSP_000490_Erdos603_ForbiddenIntersectionTwo.lean`](../bountysolves/JSP_000490_Erdos603_ForbiddenIntersectionTwo.lean) (653 lines), with zero universe bumps (`X, C : Type u`), zero `sorry`, zero `admit`, and zero custom axioms.

### Exported Theorems
```lean
theorem JSP_000490.erdos_rado_countable {C V : Type u}
    (hV : (2 : Cardinal.{u}) ^ max Cardinal.aleph0 (Cardinal.mk C) < Cardinal.mk V)
    (f : Pair V → C) :
    ∃ S : Set V, Cardinal.mk S = Cardinal.aleph0 ∧ ∃ c : C, ∀ e ∈ pairSet S, f e = c

theorem JSP_000490.jsp_000490_for_every_color_type (C : Type u) :
    ∃ (X : Type u) (ℱ : Set (Set X)),
      ⋃₀ ℱ = Set.univ ∧
      (∀ A ∈ ℱ, Cardinal.mk A = Cardinal.aleph0) ∧
      (∀ A ∈ ℱ, ∀ B ∈ ℱ, A ≠ B → Cardinal.mk (A ∩ B : Set X) ≠ 2) ∧
      (∀ f : X → C, ∃ A ∈ ℱ, ∃ c : C, ∀ x ∈ A, f x = c)

theorem JSP_000490.jsp_000490_no_uniform_cardinal_bound :
    ¬ ∃ κ : Cardinal.{u},
        ∀ (X : Type u) (ℱ : Set (Set X)),
          (∀ A ∈ ℱ, Cardinal.mk A = Cardinal.aleph0) →
          (∀ A ∈ ℱ, ∀ B ∈ ℱ, A ≠ B → Cardinal.mk (A ∩ B : Set X) ≠ 2) →
          ∃ (C : Type u) (f : (⋃₀ ℱ : Set X) → C),
            Cardinal.mk C ≤ κ ∧
            ∀ (A : Set X) (hA : A ∈ ℱ),
              ¬ ∃ c : C, ∀ (x : X) (hx : x ∈ A),
                f ⟨x, Set.mem_sUnion_of_mem hx hA⟩ = c
```

### Reproduction and Axiom Audit
```bash
lake env lean -DautoImplicit=false bountysolves/JSP_000490_Erdos603_ForbiddenIntersectionTwo.lean
```
Observed `#print axioms` output (exit code `0`, 0 warnings):
```text
'JSP_000490.erdos_rado_countable' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000490.jsp_000490_for_every_color_type' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000490.jsp_000490_no_uniform_cardinal_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

---

## 4. References

1. P. Erdős and R. Rado, *A partition calculus in set theory*, Bull. Amer. Math. Soc. **62** (1956), 427–489.
2. Erdős Problems Database, [Problem #603](https://www.erdosproblems.com/603) (posed by P. Komjáth; resolved by GPT-5.4 Pro prompted by P. Chojecki).
3. The Justin Sun Prize Problem Bank, entry `JSP-000490`, `problems/catalog-0401-0500.md`.
