# A Formal Proof and Machine-Verified Bounds for Chromatic Number via Distinct Odd Cycle Lengths (JSP-000078)

**Catalog Identifier:** `JSP-000078` ([The Justin Sun Prize Problem Bank](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0001-0100.md#JSP-000078))  
**Related Reference:** Erdős Problem #65; A. Gyárfás (1992)  
**Mathematical Area:** Graph Theory / Chromatic Number / Odd Cycles  
**Original Mathematical Proof:** A. Gyárfás, *Graphs with $k$ odd cycle lengths*, Discrete Mathematics **103** (1992), 41–48  
**Lean 4 Formalization & Exposition:** CreizyLabs (`bountysolves/JSP_000078_GyarfasOddCycleLengths.lean`)  
**Verification Environment:** Lean `4.35.0-rc2`, Mathlib4 (`9f7aa3a1327bbbc1716bdcedb64b2592e54b9bc7`)

---

## Abstract

Catalog entry `JSP-000078` (Erdős Problem #65) asks how the number of distinct odd cycle lengths realized in a graph constrains its chromatic number. We present a complete, self-contained proof and unconditional Lean 4 formalization of Gyárfás's tight upper bound: every finite simple graph $G$ realizing at most $k$ distinct odd cycle lengths is $(2k + 2)$-colorable, so $\chi(G) \le 2k + 2$. Furthermore, this bound is sharp for every $k \in \mathbb{N}$: the complete graph $K_{2k+2}$ has chromatic number $\chi(K_{2k+2}) = 2k + 2$ while realizing exact set of odd cycle lengths $\{3, 5, \dots, 2k + 1\}$, of cardinality $k$. Our Lean 4 development constructs rooted depth-first spanning trees from scratch and depends strictly on Lean's core axioms (`propext`, `Classical.choice`, `Quot.sound`).

---

## 1. Problem Statement and Formal Definitions

### 1.1 Original Problem (`JSP-000078`)
> *How does the number of distinct odd cycle lengths constrain a graph's chromatic number?*

### 1.2 Canonical Definitions
Let $G = (V, E)$ be a finite simple graph (`SimpleGraph V` with `[Fintype V] [DecidableEq V]`).
1. **Distinct odd cycle lengths (`JSP_000078.OddCycleLengths`):**
   $$\mathrm{OddCycleLengths}(G) := \bigl\{\ell \in \mathbb{N} \;\big|\; \mathrm{Odd}(\ell) \land \exists v \in V,\; \exists p \in G.\mathrm{Walk}\; v\; v,\; p.\mathrm{IsCycle} \land p.\mathrm{length} = \ell\bigr\}.$$
2. **Graph colorability & chromatic number (Mathlib `SimpleGraph.Colorable`, `SimpleGraph.chromaticNumber`):**
   $G.\mathrm{Colorable}\; m$ asserts the existence of a proper vertex coloring $V \to \mathrm{Fin}\; m$, and $\chi(G) = G.\mathrm{chromaticNumber} \in \mathbb{N}^\infty$ is the infimal such color count.
3. **Rooted DFS spanning tree (`JSP_000078.DFSTree`):**
   For a connected graph $G$ and root $r \in V$, a structure assigning each $v \in V$ a depth $\mathrm{dep}(v) \in \mathbb{N}$ and a simple path `pathFrom v` of length $\mathrm{dep}(v)$ from $r$ to $v$ such that:
   - $\mathrm{dep}(r) = 0$;
   - for every edge $\{u, v\} \in E(G)$, $\mathrm{dep}(u) \ne \mathrm{dep}(v)$;
   - whenever $\{u, v\} \in E(G)$ with $\mathrm{dep}(u) < \mathrm{dep}(v)$, the vertex at step $\mathrm{dep}(u)$ on `pathFrom v` is $u$.

### 1.3 Statement Correspondence Table

| Mathematical Concept | Lean 4 Declaration in `bountysolves/JSP_000078_GyarfasOddCycleLengths.lean` |
| --- | --- |
| Set of odd cycle lengths realized in $G$ | `JSP_000078.OddCycleLengths` |
| Finiteness of $\mathrm{OddCycleLengths}(G)$ on finite $V$ | `JSP_000078.oddCycleLengths_finite` |
| Rooted DFS spanning tree existence | `JSP_000078.exists_dfsTree` |
| Gyárfás $(2k+2)$-colorability bound | `JSP_000078.gyarfas_colorable_of_oddCycleLengths_le` |
| Gyárfás chromatic bound (`encard` form) | `JSP_000078.gyarfas_chromaticNumber_le_of_oddCycleLengths_le` |
| Gyárfás chromatic bound (`ncard` form) | `JSP_000078.gyarfas_chromaticNumber_le_of_ncard_le` |
| Sharpness on $K_{2k+2}$ (`χ = 2k + 2`, `k` odd cycle lengths) | `JSP_000078.completeGraph_sharpness` |

---

## 2. Complete Mathematical Proof

### Theorem 2.1 (Existence of DFS Spanning Trees)
For every finite connected graph $G$ and every vertex $r \in V(G)$, there exists a rooted DFS spanning tree (`DFSTree G r`).

**Proof.** We induct on $|V(G)|$. Deleting $r$ leaves connected components $\{C\}$ of $G - r$, each of size strictly less than $|V(G)|$. Since $G$ is connected, every non-empty component $C$ contains a vertex $r_C$ adjacent to $r$ in $G$. Applying the induction hypothesis inside each induced subgraph $G[C]$ rooted at $r_C$ yields internal depths $\mathrm{dep}_C$ and paths `pathFrom_C`. Lifting to $G$ by setting $\mathrm{dep}(r) = 0$, $\mathrm{dep}(v) = \mathrm{dep}_C(v) + 1$, and prepending the edge $r r_C$ to `pathFrom_C v` preserves path simplicity and the ancestor invariant across all edges, because no $G$-edge joins distinct components of $G - r$. $\square$

### Lemma 2.2 (Minimum-Degree Induced Subgraph)
If a finite graph $H$ is not $m$-colorable, then $H$ has a non-empty vertex subset $S \subseteq V(H)$ of minimum induced degree at least $m$.

**Proof.** Contrapositively, if every non-empty subset $T \subseteq S$ contains a vertex $v \in T$ with $|N_T(v)| < m$, greedy backwards induction on $|S|$ builds a proper $m$-coloring by removing $v$, $m$-coloring $S \setminus \{v\}$, and assigning $v$ an unused color in $\mathrm{Fin}\; m$. $\square$

### Theorem 2.3 (Gyárfás's Theorem: $\chi(G) \le 2k + 2$)
Every finite simple graph $G$ with at most $k$ distinct odd cycle lengths is $(2k + 2)$-colorable, hence $\chi(G) \le 2k + 2$.

**Proof.**
Suppose $G$ is not $(2k + 2)$-colorable. Then some connected component $H$ of $G$ fails to be $(2k + 2)$-colorable (`colorable_iff_forall_connectedComponent`). Pick a root $r_0 \in V(H)$ and a DFS tree $T$ on $H$ via Theorem 2.1.

Partition $V(H) = V_{\text{even}} \sqcup V_{\text{odd}}$ according to the parity of $\mathrm{dep}(v)$. If both $H[V_{\text{even}}]$ and $H[V_{\text{odd}}]$ were $(k + 1)$-colorable, disjoint union of color sets would produce a $(2k + 2)$-coloring of $H$ (`colorable_add_of_bipartition`). Thus at least one parity class $V_b$ induces a non-$(k + 1)$-colorable subgraph.

By Lemma 2.2, there is a non-empty subset $S \subseteq V_b$ such that every vertex $x \in S$ has $|N_S(x)| \ge k + 1$. Choose $v \in S$ maximizing $\mathrm{dep}(v)$, and let $N_S = \{w \in S \mid \{v, w\} \in E(H)\}$, so $|N_S| \ge k + 1$. For each $w \in N_S$:
1. Since $T$ is a DFS tree and $\mathrm{dep}(w) \le \mathrm{dep}(v)$ with $\mathrm{dep}(w) \ne \mathrm{dep}(v)$, we have $\mathrm{dep}(w) < \mathrm{dep}(v)$.
2. Because both $w, v \in S \subseteq V_b$ share the same depth parity, $\mathrm{dep}(v) - \mathrm{dep}(w)$ is even and at least $2$.
3. By the DFS ancestor property, dropping the first $\mathrm{dep}(w)$ steps of `T.pathFrom v` gives a simple path $q$ from $w$ to $v$ of length $\mathrm{dep}(v) - \mathrm{dep}(w) \ge 2$. Prepending the edge $v w$ forms a cycle in $H$ (and hence in $G$) of **odd** length
   $$\ell(w) = \mathrm{dep}(v) - \mathrm{dep}(w) + 1 \in \mathrm{OddCycleLengths}(G).$$
4. Moreover, $w \mapsto \ell(w)$ is injective on $N_S$: if $\ell(w_1) = \ell(w_2)$, then $\mathrm{dep}(w_1) = \mathrm{dep}(w_2)$, forcing $w_1 = (\text{T.pathFrom } v).\mathrm{getVert}(\mathrm{dep}(w_1)) = (\text{T.pathFrom } v).\mathrm{getVert}(\mathrm{dep}(w_2)) = w_2$.

Therefore $|\mathrm{OddCycleLengths}(G)| \ge |N_S| \ge k + 1 > k$, contradiction. $\square$

### Theorem 2.4 (Sharpness via $K_{2k+2}$)
For every $k \in \mathbb{N}$, the complete graph $K_{2k+2}$ has chromatic number $2k + 2$ and realizes exactly $k$ distinct odd cycle lengths, namely $\mathrm{OddCycleLengths}(K_{2k+2}) = \{2j + 3 \mid 0 \le j < k\}$.

**Proof.** Every cycle in $K_{2k+2}$ has length between $3$ and $2k + 2$, so any odd cycle length lies in $\{2j + 3 \mid 0 \le j < k\}$. Conversely, for each $j < k$, setting $m = 2j + 2 < 2k + 2$, closing the path $0 \to 1 \to \dots \to m$ with the edge $m \to 0$ yields a simple cycle of odd length $m + 1 = 2j + 3$. Finally, $\chi(K_{2k+2}) = 2k + 2$. $\square$

---

## 3. Lean 4 Formalization and Verification Evidence

The self-contained formalization resides in [`bountysolves/JSP_000078_GyarfasOddCycleLengths.lean`](../bountysolves/JSP_000078_GyarfasOddCycleLengths.lean) (634 lines). It uses zero `sorry`, zero `admit`, zero custom axioms, zero `native_decide`, zero approximations, and compiles with zero warnings under `-DautoImplicit=false`.

### Exported Theorems
```lean
lemma JSP_000078.exists_dfsTree {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected) (r : V) : Nonempty (DFSTree G r)

theorem JSP_000078.gyarfas_colorable_of_oddCycleLengths_le {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ)
    (hk : ∃ L : Finset ℕ, L.card ≤ k ∧ ∀ ℓ ∈ OddCycleLengths G, ℓ ∈ L) :
    G.Colorable (2 * k + 2)

theorem JSP_000078.gyarfas_chromaticNumber_le_of_oddCycleLengths_le {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ)
    (hk : (OddCycleLengths G).encard ≤ k) :
    G.chromaticNumber ≤ 2 * k + 2

theorem JSP_000078.gyarfas_chromaticNumber_le_of_ncard_le {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ)
    (hk : (OddCycleLengths G).ncard ≤ k) :
    G.chromaticNumber ≤ 2 * k + 2

theorem JSP_000078.completeGraph_sharpness (k : ℕ) :
    let K : SimpleGraph (Fin (2 * k + 2)) := ⊤
    OddCycleLengths K = ((Finset.range k).image (fun j => 2 * j + 3) : Set ℕ) ∧
    (OddCycleLengths K).ncard = k ∧
    (OddCycleLengths K).encard = k ∧
    K.chromaticNumber = 2 * k + 2
```

### Reproduction and Axiom Audit
```bash
lake env lean -DautoImplicit=false bountysolves/JSP_000078_GyarfasOddCycleLengths.lean
```
Observed `#print axioms` output (exit code `0`, 0 warnings):
```text
'JSP_000078.exists_dfsTree' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000078.gyarfas_colorable_of_oddCycleLengths_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000078.gyarfas_chromaticNumber_le_of_oddCycleLengths_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000078.gyarfas_chromaticNumber_le_of_ncard_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'JSP_000078.completeGraph_sharpness' depends on axioms: [propext, Classical.choice, Quot.sound]
```

---

## 4. References

1. A. Gyárfás, *Graphs with $k$ odd cycle lengths*, Discrete Mathematics **103** (1992), 41–48. DOI: `10.1016/0012-365x(92)90037-g`.
2. J. Gao, Q. Huo, and J. Ma, *A strengthening on odd cycles in graphs of given chromatic number*, SIAM J. Discrete Math. **35** (2021), 2317–2327.
3. Erdős Problem #65, [https://www.erdosproblems.com/65](https://www.erdosproblems.com/65).
