import Mathlib

/-!
# JSP-000078 (Erdős Problem #65 / Gyárfás 1992): Bounding Chromatic Number by Distinct Odd Cycle Lengths

- **Catalog ID:** `JSP-000078` (`catalog-0001-0100.md`)
- **Live Catalog Status:** `Current status: Solved`, `Lean proof: No`
- **Problem Statement:** How does the number of distinct odd cycle lengths constrain a graph's
  chromatic number?
- **Historical & Mathematical Source:**
  A. Gyárfás (1992), *Graphs with $k$ odd cycle lengths*, Discrete Mathematics 103 (1992), 41–48
  (DOI `10.1016/0012-365x(92)90037-g`).
- **Complete Quantitative Resolution (`χ(G) ≤ 2k + 2`, sharp via `K_{2k+2}`):**
  1. **Upper bound (`gyarfas_chromaticNumber_le_of_oddCycleLengths_le` &
     `gyarfas_colorable_of_oddCycleLengths_le`):** Every finite simple graph `G` with at most `k`
     distinct odd cycle lengths satisfies `G.Colorable (2 * k + 2)` and `G.chromaticNumber ≤ 2 * k + 2`.
  2. **Sharpness (`completeGraph_sharpness`):** For every `k : ℕ`, the complete graph `K_{2k+2}`
     (`⊤ : SimpleGraph (Fin (2 * k + 2))`) has `chromaticNumber = 2 * k + 2` and attains
     **exactly `k`** distinct odd cycle lengths `{3, 5, ..., 2k + 1}`.

## Proof Method (Self-Contained DFS-Tree Parity Decomposition)
1. **DFS spanning tree (`exists_dfsTree`):** Every finite connected graph with any chosen root
   admits a depth function `dep : V → ℕ` and root-to-vertex paths `pathFrom v` such that every
   edge `{u, v}` connects vertices at different depths (`dep u ≠ dep v`), and whenever
   `dep u < dep v`, `u` lies at depth `dep u` along `pathFrom v`. Constructed by strong induction
   on `Fintype.card V` over connected components of `G - {r}`.
2. **Minimum-degree subgraph extraction (`exists_minDeg_subgraph_of_not_colorable`):** Every
   finite non-`m`-colorable graph contains a nonempty induced subgraph of minimum degree `≥ m`.
3. **Bipartite depth-parity split:** On a non-`(2k + 2)`-colorable connected component `H`,
   partitioning `V(H)` into even-depth vertices `V₀` and odd-depth vertices `V₁` forces at least
   one side `H[V_b]` to fail `(k + 1)`-colorability, yielding a nonempty subset `S ⊆ V_b` with
   minimum internal degree `≥ k + 1`. A vertex `v ∈ S` of maximum `dep` has at least `k + 1`
   strict-ancestor neighbors `u ∈ S`, each producing a cycle `(cons huv ((pathFrom v).drop (dep u)))`
   of **odd** length `dep v - dep u + 1` with pairwise distinct depths `dep u` (injective along
   `pathFrom v`), forcing `≥ k + 1` distinct odd cycle lengths.

## Formal Guarantees
- Unconditional, zero `sorry`, zero `admit`, zero custom axioms
  (`#print axioms` strictly a subset of `[propext, Classical.choice, Quot.sound]`),
  zero `native_decide`, zero approximations, zero warnings under `-DautoImplicit=false`.
-/

namespace JSP_000078

open SimpleGraph Finset

universe u

/-- The set of distinct odd cycle lengths realized in a simple graph `G`. -/
def OddCycleLengths {V : Type u} (G : SimpleGraph V) : Set ℕ :=
  {ℓ : ℕ | Odd ℓ ∧ ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = ℓ}

lemma oddCycleLengths_finite {V : Type u} [Fintype V] (G : SimpleGraph V) :
    (OddCycleLengths G).Finite := by
  refine (Set.finite_le_nat (Fintype.card V)).subset ?_
  rintro ℓ ⟨_, v, p, hp, rfl⟩
  have hlen : p.length = p.support.dropLast.length := by
    simp [List.length_dropLast, p.length_support]
  rw [Set.mem_ofPred_eq, hlen]
  exact hp.nodup_dropLast_support.length_le_card

lemma isCycle_cons_of_isPath {V : Type*} {G : SimpleGraph V} {u v : V}
    (h : G.Adj u v) (q : G.Walk v u) (hq : q.IsPath) (hlen : 2 ≤ q.length) :
    (Walk.cons h q).IsCycle := by
  rw [Walk.isCycle_iff_isPath_tail_and_le_length]
  refine ⟨?_, ?_⟩
  · simp only [Walk.getVert_cons_succ, Walk.tail_cons, Walk.isPath_copy]
    exact hq
  · simp only [Walk.length_cons]
    omega

lemma oddCycleLengths_map_subset {V : Type*} {W : Type u} {G : SimpleGraph V} {G' : SimpleGraph W}
    (f : G →g G') (hf : Function.Injective f) :
    OddCycleLengths G ⊆ OddCycleLengths G' := by
  rintro ℓ ⟨hodd, v, p, hp, rfl⟩
  cases p with
  | nil => exact absurd hp Walk.not_isCycle_nil
  | cons hadj q =>
    rename_i u_mid
    have hq_path : q.IsPath := ((Walk.cons_isCycle_iff q hadj).mp hp).1
    have hlen2 : 2 ≤ q.length := by
      have h3 := hp.three_le_length
      simp only [Walk.length_cons] at h3
      omega
    have hq_map_path : (q.map f).IsPath := by
      rw [Walk.isPath_def, Walk.support_map]
      exact hq_path.support_nodup.map hf
    have hcons_cyc : (Walk.cons (f.map_adj hadj) (q.map f)).IsCycle :=
      isCycle_cons_of_isPath (f.map_adj hadj) (q.map f) hq_map_path (by simpa using hlen2)
    refine ⟨hodd, f v, Walk.cons (f.map_adj hadj) (q.map f), hcons_cyc, ?_⟩
    simp

/-! ### 1. Normal / DFS Spanning Trees in Finite Connected Graphs -/

/-- A rooted DFS spanning tree on a connected graph `G` with root `root`. -/
structure DFSTree {V : Type u} (G : SimpleGraph V) (root : V) where
  dep : V → ℕ
  dep_root : dep root = 0
  pathFrom : ∀ v : V, G.Walk root v
  pathFrom_isPath : ∀ v : V, (pathFrom v).IsPath
  pathFrom_length : ∀ v : V, (pathFrom v).length = dep v
  dfs_ne : ∀ {u v : V}, G.Adj u v → dep u ≠ dep v
  dfs_anc : ∀ {u v : V}, G.Adj u v → dep u < dep v → (pathFrom v).getVert (dep u) = u

lemma exists_adj_target_in_induce {V : Type u} (G : SimpleGraph V) (r : V) :
    ∀ {a b : V}, G.Walk a b → (ha : a ≠ r) → b = r →
      ∃ y : {x : V // x ≠ r}, (G.induce {x : V | x ≠ r}).Reachable ⟨a, ha⟩ y ∧ G.Adj y.1 r
  | _, _, .nil, ha, hb => False.elim (ha hb)
  | a, _, .cons (v := z) hadj w', ha, rfl => by
    by_cases hz : z = r
    · subst hz
      exact ⟨⟨a, ha⟩, Reachable.refl _, hadj⟩
    · obtain ⟨y, hreach, hadjy⟩ := exists_adj_target_in_induce G r w' hz rfl
      have hadj' : (G.induce {x : V | x ≠ r}).Adj ⟨a, ha⟩ ⟨z, hz⟩ := hadj
      exact ⟨y, Reachable.trans hadj'.reachable hreach, hadjy⟩

lemma card_ne_lt {V : Type u} [Fintype V] [DecidableEq V] (r : V) :
    Fintype.card {x : V // x ≠ r} < Fintype.card V := by
  rw [Fintype.card_subtype]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro heq
  have hr : r ∈ (Finset.univ : Finset V).filter (fun x : V => x ≠ r) := by
    rw [heq]
    exact Finset.mem_univ r
  exact (Finset.mem_filter.mp hr).2 rfl

lemma exists_dfsTree_aux :
    ∀ (n : ℕ) {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.Connected → ∀ r : V, Fintype.card V ≤ n → Nonempty (DFSTree G r)
  | 0, V, _, _, _, hconn, r, hcard => by
    have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨r⟩
    omega
  | n + 1, V, _, _, G, hconn, r, hcard => by
    classical
    let S' : Set V := {x : V | x ≠ r}
    let G' : SimpleGraph {x : V // x ≠ r} := G.induce S'
    have hlt_V' : Fintype.card {x : V // x ≠ r} < Fintype.card V := card_ne_lt r
    -- Pick a representative vertex adjacent to `r` in each connected component `c` of `G'`
    have exists_root_in_comp : ∀ c : G'.ConnectedComponent,
        ∃ rc : c.supp, G.Adj rc.1.1 r := by
      intro c
      obtain ⟨x0, hx0⟩ := c.nonempty_supp
      obtain ⟨w⟩ := hconn.preconnected x0.1 r
      obtain ⟨y, hreach, hadjy⟩ := exists_adj_target_in_induce G r w x0.2 rfl
      have hy_mem : y ∈ c.supp := by
        rw [ConnectedComponent.mem_supp_iff, ← (ConnectedComponent.mem_supp_iff c x0).mp hx0]
        exact (ConnectedComponent.sound hreach).symm
      exact ⟨⟨y, hy_mem⟩, hadjy⟩
    let rc : (c : G'.ConnectedComponent) → c.supp := fun c => Classical.choose (exists_root_in_comp c)
    have hrc_adj : ∀ c : G'.ConnectedComponent, G.Adj r (rc c).1.1 :=
      fun c => (Classical.choose_spec (exists_root_in_comp c)).symm
    have hT_comp : ∀ c : G'.ConnectedComponent, DFSTree c.toSimpleGraph (rc c) := by
      intro c
      have hcard_c : Fintype.card ↥c ≤ n := by
        have hle : Fintype.card ↥c ≤ Fintype.card {x : V // x ≠ r} :=
          Fintype.card_le_of_injective Subtype.val Subtype.val_injective
        omega
      exact Classical.choice (exists_dfsTree_aux n c.toSimpleGraph c.connected_toSimpleGraph (rc c) hcard_c)
    let homComp : (c : G'.ConnectedComponent) → c.toSimpleGraph →g G := fun c =>
      { toFun := fun x => x.1.1
        map_rel' := fun {_ _} h => h }
    have homComp_inj : ∀ c : G'.ConnectedComponent, Function.Injective (homComp c) := by
      intro c x y hxy
      exact Subtype.ext (Subtype.ext hxy)
    have homComp_ne_r : ∀ (c : G'.ConnectedComponent) (x : c.supp), (homComp c x) ≠ r :=
      fun _ x => x.1.2
    let dep : V → ℕ := fun v =>
      if h : v = r then 0 else (hT_comp (G'.connectedComponentMk ⟨v, h⟩)).dep ⟨⟨v, h⟩, rfl⟩ + 1
    let pathFrom : ∀ v : V, G.Walk r v := fun v =>
      if h : v = r then Walk.nil.copy rfl h.symm
      else
        let c := G'.connectedComponentMk ⟨v, h⟩
        Walk.cons (hrc_adj c) (((hT_comp c).pathFrom ⟨⟨v, h⟩, rfl⟩).map (homComp c))
    have dep_root : dep r = 0 := by simp [dep]
    have pathFrom_isPath : ∀ v : V, (pathFrom v).IsPath := by
      intro v
      dsimp [pathFrom]
      split_ifs with hv
      · simp
      · set c := G'.connectedComponentMk ⟨v, hv⟩
        have hmap_path : (((hT_comp c).pathFrom ⟨⟨v, hv⟩, rfl⟩).map (homComp c)).IsPath := by
          rw [Walk.isPath_def, Walk.support_map]
          exact ((hT_comp c).pathFrom_isPath ⟨⟨v, hv⟩, rfl⟩).support_nodup.map (homComp_inj c)
        rw [Walk.cons_isPath_iff]
        refine ⟨hmap_path, ?_⟩
        intro hr_mem
        rw [Walk.support_map, List.mem_map] at hr_mem
        rcases hr_mem with ⟨x, _, hx⟩
        exact homComp_ne_r c x hx
    have pathFrom_length : ∀ v : V, (pathFrom v).length = dep v := by
      intro v
      dsimp [pathFrom, dep]
      split_ifs with hv
      · simp
      · simp [(hT_comp _).pathFrom_length]
    have dep_eq_of_mem : ∀ {x : V} (hx : x ≠ r) (c : G'.ConnectedComponent)
        (hmem : (⟨x, hx⟩ : {y : V // y ≠ r}) ∈ c.supp),
        dep x = (hT_comp c).dep ⟨⟨x, hx⟩, hmem⟩ + 1 := by
      intro x hx c hmem
      have hceq : G'.connectedComponentMk ⟨x, hx⟩ = c := hmem
      dsimp [dep]
      simp only [hx, ↓reduceDIte]
      congr 1
      revert hmem
      rw [← hceq]
      intro _; rfl
    have dfs_props : ∀ {u v : V}, G.Adj u v →
        dep u ≠ dep v ∧ (dep u < dep v → (pathFrom v).getVert (dep u) = u) := by
      intro u v huv
      by_cases hu : u = r
      · rcases hu with rfl
        have hv : v ≠ u := (G.ne_of_adj huv).symm
        have hdu : dep u = 0 := dep_root
        have hdv : dep v = (hT_comp (G'.connectedComponentMk ⟨v, hv⟩)).dep ⟨⟨v, hv⟩, rfl⟩ + 1 := by
          dsimp [dep]; simp only [hv, ↓reduceDIte]
        refine ⟨by omega, fun _ => ?_⟩
        rw [hdu]
        simp
      · by_cases hv : v = r
        · rcases hv with rfl
          have hdv : dep v = 0 := dep_root
          have hdu : dep u = (hT_comp (G'.connectedComponentMk ⟨u, hu⟩)).dep ⟨⟨u, hu⟩, rfl⟩ + 1 := by
            dsimp [dep]; simp only [hu, ↓reduceDIte]
          exact ⟨by omega, fun hlt => by omega⟩
        · let u' : {x : V // x ≠ r} := ⟨u, hu⟩
          let v' : {x : V // x ≠ r} := ⟨v, hv⟩
          let c := G'.connectedComponentMk v'
          have hadj' : G'.Adj u' v' := huv
          have humem : u' ∈ c.supp := c.mem_supp_of_adj_mem_supp rfl hadj'.symm
          have hvmem : v' ∈ c.supp := rfl
          have hc_adj : c.toSimpleGraph.Adj ⟨u', humem⟩ ⟨v', hvmem⟩ := huv
          have hdu : dep u = (hT_comp c).dep ⟨u', humem⟩ + 1 := dep_eq_of_mem hu c humem
          have hdv : dep v = (hT_comp c).dep ⟨v', hvmem⟩ + 1 := dep_eq_of_mem hv c hvmem
          have hne_c := (hT_comp c).dfs_ne hc_adj
          have hanc_c := (hT_comp c).dfs_anc hc_adj
          refine ⟨by omega, fun hlt => ?_⟩
          have hlt_c : (hT_comp c).dep ⟨u', humem⟩ < (hT_comp c).dep ⟨v', hvmem⟩ := by omega
          have hgv := hanc_c hlt_c
          dsimp [pathFrom]
          simp only [hv, ↓reduceDIte]
          rw [hdu, Walk.getVert_cons_succ, Walk.getVert_map, hgv]
          rfl
    exact ⟨{
      dep := dep
      dep_root := dep_root
      pathFrom := pathFrom
      pathFrom_isPath := pathFrom_isPath
      pathFrom_length := pathFrom_length
      dfs_ne := fun h => (dfs_props h).1
      dfs_anc := fun h => (dfs_props h).2
    }⟩

lemma exists_dfsTree {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hconn : G.Connected) (r : V) : Nonempty (DFSTree G r) :=
  exists_dfsTree_aux (Fintype.card V) G hconn r (le_refl _)

/-! ### 2. Minimum-Degree Subgraph Extraction for Non-Colorable Finite Graphs -/

lemma colorable_induce_of_degeneracy {V : Type u} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (m : ℕ) :
    ∀ (k : ℕ) (S : Finset V), S.card ≤ k →
      (∀ T : Finset V, T.Nonempty → T ⊆ S → ∃ v ∈ T, (T.filter (G.Adj v)).card < m) →
      (G.induce (S : Set V)).Colorable m
  | 0, S, hk, _ => by
    have hS0 : S = ∅ := Finset.card_eq_zero.mp (by omega)
    exact ⟨Coloring.mk (fun x => False.elim (by simpa [hS0] using x.2))
      (fun {x} => False.elim (by simpa [hS0] using x.2))⟩
  | k + 1, S, hk, hdeg => by
    by_cases hSne : S.Nonempty
    · obtain ⟨v, hvS, hvdeg⟩ := hdeg S hSne (Subset.refl S)
      let S' := S.erase v
      have hcard' : S'.card ≤ k := by
        have := Finset.card_erase_lt_of_mem hvS
        dsimp [S']
        omega
      have hC' : (G.induce (S' : Set V)).Colorable m := by
        apply colorable_induce_of_degeneracy G m k S' hcard'
        intro T hTne hTS'
        exact hdeg T hTne (hTS'.trans (Finset.erase_subset v S))
      obtain ⟨C'⟩ := hC'
      let Nv := S.filter (G.Adj v)
      let used : Finset (Fin m) := Nv.attach.image (fun x =>
        C' ⟨x.1, by
          have hx := Finset.mem_filter.mp x.2
          have hne : x.1 ≠ v := (G.ne_of_adj hx.2).symm
          exact Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hne, hx.1⟩)⟩)
      have hused_card : used.card < m := by
        calc
          used.card ≤ Nv.attach.card := Finset.card_image_le
          _ = Nv.card := Finset.card_attach
          _ < m := hvdeg
      have hm_lt : used.card < (Finset.univ : Finset (Fin m)).card := by
        simpa using hused_card
      obtain ⟨c0, hc0⟩ := Finset.exists_mem_notMem_of_card_lt_card hm_lt
      let C : (G.induce (S : Set V)).Coloring (Fin m) :=
        Coloring.mk (fun x =>
          if hx : x.1 = v then c0
          else C' ⟨x.1, Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hx, Finset.mem_coe.mp x.2⟩)⟩)
          (by
            intro x y hadj
            change G.Adj x.1 y.1 at hadj
            by_cases hx : x.1 = v
            · have hy : y.1 ≠ v := by
                intro hy; rw [hx, hy] at hadj; exact G.ne_of_adj hadj rfl
              simp only [hx, hy, ↓reduceDIte]
              intro heq
              have hyS : y.1 ∈ Nv := Finset.mem_filter.mpr ⟨Finset.mem_coe.mp y.2, hx ▸ hadj⟩
              have hmem_used : c0 ∈ used := by
                rw [heq]
                exact Finset.mem_image.mpr ⟨⟨y.1, hyS⟩, Finset.mem_attach _ _, rfl⟩
              exact hc0.2 hmem_used
            · by_cases hy : y.1 = v
              · simp only [hx, hy, ↓reduceDIte]
                intro heq
                have hxS : x.1 ∈ Nv := Finset.mem_filter.mpr ⟨Finset.mem_coe.mp x.2, hy ▸ hadj.symm⟩
                have hmem_used : c0 ∈ used := by
                  rw [← heq]
                  exact Finset.mem_image.mpr ⟨⟨x.1, hxS⟩, Finset.mem_attach _ _, rfl⟩
                exact hc0.2 hmem_used
              · simp only [hx, hy, ↓reduceDIte]
                exact C'.valid hadj)
      exact ⟨C⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at hSne
      exact ⟨Coloring.mk (fun x => False.elim (by simpa [hSne] using x.2))
        (fun {x} => False.elim (by simpa [hSne] using x.2))⟩

lemma exists_minDeg_subgraph_of_not_colorable {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ) (hnc : ¬ G.Colorable m) :
    ∃ S : Finset V, S.Nonempty ∧ ∀ v ∈ S, m ≤ (S.filter (G.Adj v)).card := by
  by_contra hnone
  push Not at hnone
  have hcol_ind : (G.induce ((Finset.univ : Finset V) : Set V)).Colorable m :=
    colorable_induce_of_degeneracy G m (Finset.univ : Finset V).card Finset.univ (le_refl _)
      (fun T hTne _ => hnone T hTne)
  obtain ⟨C⟩ := hcol_ind
  let C' : G.Coloring (Fin m) := Coloring.mk (fun v => C ⟨v, by simp⟩) (fun hadj => C.valid hadj)
  exact hnc ⟨C'⟩

/-! ### 3. Gyárfás's Theorem: `χ(G) ≤ 2k + 2` for Graphs with At Most `k` Odd Cycle Lengths -/

lemma colorable_add_of_bipartition {V : Type u} (H : SimpleGraph V) (P : V → Prop)
    (m : ℕ)
    (h0 : (H.induce {v : V | P v}).Colorable m)
    (h1 : (H.induce {v : V | ¬ P v}).Colorable m) :
    H.Colorable (2 * m) := by
  classical
  obtain ⟨C0⟩ := h0
  obtain ⟨C1⟩ := h1
  refine ⟨Coloring.mk (fun v =>
    if hv : P v then ⟨(C0 ⟨v, hv⟩).val, by omega⟩
    else ⟨m + (C1 ⟨v, hv⟩).val, by omega⟩) (by
      intro u v huv
      by_cases hu : P u <;> by_cases hv : P v <;> simp only [hu, hv, ↓reduceDIte] <;> intro h
      · exact C0.valid (show (H.induce {x | P x}).Adj ⟨u, hu⟩ ⟨v, hv⟩ from huv)
          (Fin.ext (by simpa using congrArg Fin.val h))
      · have hlt := (C0 ⟨u, hu⟩).isLt
        have hval := congrArg Fin.val h
        dsimp at hval
        omega
      · have hlt := (C0 ⟨v, hv⟩).isLt
        have hval := congrArg Fin.val h
        dsimp at hval
        omega
      · exact C1.valid (show (H.induce {x | ¬ P x}).Adj ⟨u, hu⟩ ⟨v, hv⟩ from huv)
          (Fin.ext (by
            have hval := congrArg Fin.val h
            dsimp at hval
            omega)))⟩

/-- **Gyárfás's Theorem (Colorability Form, JSP-000078 / Erdős #65):**
Every finite simple graph with at most `k` distinct odd cycle lengths is `(2 * k + 2)`-colorable. -/
theorem gyarfas_colorable_of_oddCycleLengths_le {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ)
    (hk : ∃ L : Finset ℕ, L.card ≤ k ∧ ∀ ℓ ∈ OddCycleLengths G, ℓ ∈ L) :
    G.Colorable (2 * k + 2) := by
  classical
  by_contra hnc
  obtain ⟨c, hnc_c⟩ : ∃ c : G.ConnectedComponent, ¬ (c.toSimpleGraph).Colorable (2 * k + 2) := by
    by_contra h
    push Not at h
    exact hnc (SimpleGraph.colorable_iff_forall_connectedComponent.mpr h)
  let H := c.toSimpleGraph
  obtain ⟨r0, hr0⟩ := c.nonempty_supp
  obtain ⟨T⟩ := exists_dfsTree H c.connected_toSimpleGraph ⟨r0, hr0⟩
  -- Partition `c.supp` into even-depth and odd-depth vertices
  have hex_half : ¬ (H.induce {v | Even (T.dep v)}).Colorable (k + 1) ∨
      ¬ (H.induce {v | ¬ Even (T.dep v)}).Colorable (k + 1) := by
    by_contra hboth
    push Not at hboth
    have heq : 2 * (k + 1) = 2 * k + 2 := by omega
    exact hnc_c (heq ▸ colorable_add_of_bipartition H (fun v => Even (T.dep v)) (k + 1) hboth.1 hboth.2)
  -- Extract dense induced subset `S : Finset c.supp` inside one parity part
  have extract_dense : ∀ (Q : c.supp → Prop),
      (∀ u v : c.supp, u ∈ ({x | Q x} : Set c.supp) → v ∈ ({x | Q x} : Set c.supp) →
        (T.dep u + T.dep v) % 2 = 0) →
      ¬ (H.induce {x | Q x}).Colorable (k + 1) →
      ∃ S : Finset c.supp, S.Nonempty ∧
        (∀ x ∈ S, Q x) ∧
        ∀ x ∈ S, k + 1 ≤ (S.filter (H.Adj x)).card := by
    intro Q _ hQ_nc
    obtain ⟨S₀, hS₀_ne, hS₀_deg⟩ := exists_minDeg_subgraph_of_not_colorable (H.induce {x | Q x}) (k + 1) hQ_nc
    let S : Finset c.supp := S₀.map ⟨Subtype.val, Subtype.val_injective⟩
    refine ⟨S, ?_, ?_, ?_⟩
    · rcases hS₀_ne with ⟨x, hx⟩
      exact ⟨x.1, Finset.mem_map.mpr ⟨x, hx, rfl⟩⟩
    · intro x hx
      rcases Finset.mem_map.mp hx with ⟨x₀, _, rfl⟩
      exact x₀.2
    · intro x hx
      rcases Finset.mem_map.mp hx with ⟨x₀, hx₀, rfl⟩
      have hcard_le : (S₀.filter ((H.induce {y | Q y}).Adj x₀)).card ≤ (S.filter (H.Adj x₀.1)).card := by
        apply Finset.card_le_card_of_injOn Subtype.val
        · intro y hy
          rw [Finset.mem_coe, Finset.mem_filter] at hy ⊢
          exact ⟨Finset.mem_map.mpr ⟨y, hy.1, rfl⟩, hy.2⟩
        · intro y₁ _ y₂ _ heq
          exact Subtype.ext heq
      exact le_trans (hS₀_deg x₀ hx₀) hcard_le
  have hS_ex : ∃ S : Finset c.supp, S.Nonempty ∧
      (∀ x y : c.supp, x ∈ S → y ∈ S → T.dep x % 2 = T.dep y % 2) ∧
      ∀ x ∈ S, k + 1 ≤ (S.filter (H.Adj x)).card := by
    rcases hex_half with h0 | h1
    · obtain ⟨S, hSne, hSQ, hSdeg⟩ := extract_dense (fun v => Even (T.dep v))
        (fun u v hu hv => by obtain ⟨a, ha⟩ := hu; obtain ⟨b, hb⟩ := hv; omega) h0
      refine ⟨S, hSne, ?_, hSdeg⟩
      intro x y hx hy
      obtain ⟨a, ha⟩ := hSQ x hx
      obtain ⟨b, hb⟩ := hSQ y hy
      omega
    · obtain ⟨S, hSne, hSQ, hSdeg⟩ := extract_dense (fun v => ¬ Even (T.dep v))
        (fun u v hu hv => by simp only [Set.mem_ofPred_eq, Nat.not_even_iff_odd] at hu hv; obtain ⟨a, ha⟩ := hu; obtain ⟨b, hb⟩ := hv; omega) h1
      refine ⟨S, hSne, ?_, hSdeg⟩
      intro x y hx hy
      have hx' := Nat.not_even_iff_odd.mp (hSQ x hx)
      have hy' := Nat.not_even_iff_odd.mp (hSQ y hy)
      obtain ⟨a, ha⟩ := hx'
      obtain ⟨b, hb⟩ := hy'
      omega
  obtain ⟨S, hSne, hS_par, hS_deg⟩ := hS_ex
  obtain ⟨v, hvS, hv_max⟩ := S.exists_max_image T.dep hSne
  let N_S := S.filter (H.Adj v)
  have hNS_card : k + 1 ≤ N_S.card := hS_deg v hvS
  -- Every neighbor `w ∈ N_S` yields a distinct odd cycle length `T.dep v - T.dep w + 1 ∈ OddCycleLengths G`
  let lenFn : c.supp → ℕ := fun w => T.dep v - T.dep w + 1
  have hNS_odd : ∀ w ∈ N_S, lenFn w ∈ OddCycleLengths G := by
    intro w hw
    rw [Finset.mem_filter] at hw
    obtain ⟨hwS, hvw⟩ := hw
    have hwv : H.Adj w v := hvw.symm
    have hle : T.dep w ≤ T.dep v := hv_max w hwS
    have hne : T.dep w ≠ T.dep v := T.dfs_ne hwv
    have hlt : T.dep w < T.dep v := lt_of_le_of_ne hle hne
    have hpar : T.dep w % 2 = T.dep v % 2 := hS_par w v hwS hvS
    have hdiff2 : 2 ≤ T.dep v - T.dep w := by omega
    have hodd : Odd (lenFn w) := by
      dsimp [lenFn]
      rw [Nat.odd_iff]
      omega
    have hget : (T.pathFrom v).getVert (T.dep w) = w := T.dfs_anc hwv hlt
    let q : H.Walk w v := ((T.pathFrom v).drop (T.dep w)).copy hget rfl
    have hq_path : q.IsPath := by
      rw [Walk.isPath_copy]
      exact (T.pathFrom_isPath v).drop (T.dep w)
    have hq_len : q.length = T.dep v - T.dep w := by
      rw [Walk.length_copy, Walk.drop_length, T.pathFrom_length v]
    have hcyc_H : (Walk.cons hvw q).IsCycle :=
      isCycle_cons_of_isPath hvw q hq_path (by rw [hq_len]; omega)
    have hmem_H : lenFn w ∈ OddCycleLengths H :=
      ⟨hodd, v, Walk.cons hvw q, hcyc_H, by simp [lenFn, hq_len]⟩
    exact oddCycleLengths_map_subset c.toSimpleGraph_hom Subtype.val_injective hmem_H
  have hNS_inj : Set.InjOn lenFn (N_S : Set c.supp) := by
    intro w₁ hw₁ w₂ hw₂ heq
    rw [Finset.mem_coe, Finset.mem_filter] at hw₁ hw₂
    have h1_lt : T.dep w₁ < T.dep v :=
      lt_of_le_of_ne (hv_max w₁ hw₁.1) (T.dfs_ne hw₁.2.symm)
    have h2_lt : T.dep w₂ < T.dep v :=
      lt_of_le_of_ne (hv_max w₂ hw₂.1) (T.dfs_ne hw₂.2.symm)
    have hdep_eq : T.dep w₁ = T.dep w₂ := by
      dsimp [lenFn] at heq
      omega
    have hg1 := T.dfs_anc hw₁.2.symm h1_lt
    have hg2 := T.dfs_anc hw₂.2.symm h2_lt
    rw [← hg1, ← hg2, hdep_eq]
  obtain ⟨L, hL_card, hL_cov⟩ := hk
  have himg_sub : N_S.image lenFn ⊆ L := by
    intro ℓ hℓ
    rcases Finset.mem_image.mp hℓ with ⟨w, hw, rfl⟩
    exact hL_cov (lenFn w) (hNS_odd w hw)
  have himg_card : N_S.card ≤ L.card := by
    rw [← Finset.card_image_of_injOn hNS_inj]
    exact Finset.card_le_card himg_sub
  omega

/-- **Gyárfás's Theorem (Chromatic Number Bound, JSP-000078 / Erdős #65):**
Every finite graph with at most `k` distinct odd cycle lengths has chromatic number `≤ 2 * k + 2`. -/
theorem gyarfas_chromaticNumber_le_of_oddCycleLengths_le {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ)
    (hk : (OddCycleLengths G).encard ≤ k) :
    G.chromaticNumber ≤ 2 * k + 2 := by
  have hfin : (OddCycleLengths G).Finite := oddCycleLengths_finite G
  let L : Finset ℕ := hfin.toFinset
  have hL_card : L.card ≤ k := by
    have h1 : (L.card : ℕ∞) = (OddCycleLengths G).encard := by
      simpa [L] using hfin.encard_eq_coe_toFinset_card.symm
    have hk' : (L.card : ℕ∞) ≤ (k : ℕ∞) := h1 ▸ hk
    exact Nat.cast_le.mp hk'
  have hL_cov : ∀ ℓ ∈ OddCycleLengths G, ℓ ∈ L := fun ℓ hℓ => hfin.mem_toFinset.mpr hℓ
  exact_mod_cast (gyarfas_colorable_of_oddCycleLengths_le G k ⟨L, hL_card, hL_cov⟩).chromaticNumber_le

/-- `ncard` form of Gyárfás's bound. -/
theorem gyarfas_chromaticNumber_le_of_ncard_le {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ)
    (hk : (OddCycleLengths G).ncard ≤ k) :
    G.chromaticNumber ≤ 2 * k + 2 := by
  have hfin : (OddCycleLengths G).Finite := oddCycleLengths_finite G
  apply gyarfas_chromaticNumber_le_of_oddCycleLengths_le G k
  rw [← hfin.cast_ncard_eq]
  exact Nat.cast_le.mpr hk

/-! ### 4. Sharpness via Complete Graphs `K_{2k+2}` -/

/-- The odd integers in `[3, 2 * k + 2]` are contained in `{ 2 * j + 3 | j ∈ range k }`,
which has cardinality `k`. -/
theorem completeGraph_oddCycleLengths_subset (k : ℕ) :
    ∀ ℓ ∈ OddCycleLengths (⊤ : SimpleGraph (Fin (2 * k + 2))),
      ℓ ∈ (Finset.range k).image (fun j => 2 * j + 3) := by
  rintro ℓ ⟨hodd, v, p, hp, rfl⟩
  have h3 : 3 ≤ p.length := hp.three_le_length
  have hle : p.length ≤ 2 * k + 2 := by
    have hlen : p.length = p.support.dropLast.length := by
      simp [List.length_dropLast, p.length_support]
    rw [hlen]
    simpa using hp.nodup_dropLast_support.length_le_card
  obtain ⟨m, hm⟩ := hodd
  have hm1 : 1 ≤ m := by omega
  have hm_lt : m - 1 < k := by omega
  refine Finset.mem_image.mpr ⟨m - 1, Finset.mem_range.mpr hm_lt, ?_⟩
  omega

/-- Auxiliary simple path `0 → 1 → ... → m` in `(⊤ : SimpleGraph (Fin N))`. -/
def topPath (N : ℕ) : ∀ (m : ℕ) (hm : m < N),
    (⊤ : SimpleGraph (Fin N)).Walk ⟨0, by omega⟩ ⟨m, hm⟩
  | 0, _ => Walk.nil
  | j + 1, hm =>
    (topPath N j (by omega)).concat (by
      change (⟨j, by omega⟩ : Fin N) ≠ ⟨j + 1, hm⟩
      simp)

lemma topPath_length (N : ℕ) : ∀ (m : ℕ) (hm : m < N), (topPath N m hm).length = m
  | 0, _ => rfl
  | j + 1, hm => by simp [topPath, topPath_length N j (by omega)]

lemma topPath_support (N : ℕ) : ∀ (m : ℕ) (hm : m < N),
    ∀ x ∈ (topPath N m hm).support, x.val ≤ m
  | 0, hm, x, hx => by
    simp only [topPath, Walk.support_nil, List.mem_singleton] at hx
    subst hx; simp
  | j + 1, hm, x, hx => by
    dsimp [topPath] at hx
    rw [Walk.support_concat, List.mem_append] at hx
    rcases hx with hx | hx
    · have := topPath_support N j (by omega) x hx
      omega
    · simp only [List.mem_singleton] at hx
      subst hx
      simp

lemma topPath_isPath (N : ℕ) : ∀ (m : ℕ) (hm : m < N), (topPath N m hm).IsPath
  | 0, _ => Walk.IsPath.nil
  | j + 1, hm => by
    dsimp [topPath]
    rw [Walk.isPath_concat]
    refine ⟨topPath_isPath N j (by omega), ?_⟩
    intro hmem
    have hle := topPath_support N j (by omega) ⟨j + 1, hm⟩ hmem
    dsimp at hle
    omega

/-- **Exact Sharpness Witness (`K_{2k+2}`):** For every `k : ℕ`, `⊤ : SimpleGraph (Fin (2 * k + 2))`
has **exactly `k`** distinct odd cycle lengths AND chromatic number `2 * k + 2`. -/
theorem completeGraph_sharpness (k : ℕ) :
    let K : SimpleGraph (Fin (2 * k + 2)) := ⊤
    OddCycleLengths K = ((Finset.range k).image (fun j => 2 * j + 3) : Set ℕ) ∧
    (OddCycleLengths K).ncard = k ∧
    (OddCycleLengths K).encard = k ∧
    K.chromaticNumber = 2 * k + 2 := by
  intro K
  have hset : OddCycleLengths K = ((Finset.range k).image (fun j => 2 * j + 3) : Set ℕ) := by
    ext ℓ
    constructor
    · exact completeGraph_oddCycleLengths_subset k ℓ
    · intro hℓ
      simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_range] at hℓ
      rcases hℓ with ⟨j, hj, rfl⟩
      let m := 2 * j + 2
      have hm : m < 2 * k + 2 := by omega
      have h0m : K.Adj ⟨m, hm⟩ ⟨0, by omega⟩ := by
        change (⟨m, hm⟩ : Fin (2 * k + 2)) ≠ ⟨0, by omega⟩
        simp [m]
      let p := Walk.cons h0m (topPath (2 * k + 2) m hm)
      have hp_cyc : p.IsCycle :=
        isCycle_cons_of_isPath h0m (topPath (2 * k + 2) m hm) (topPath_isPath _ _ _)
          (by rw [topPath_length]; omega)
      refine ⟨⟨j + 1, by omega⟩, ⟨m, hm⟩, p, hp_cyc, ?_⟩
      simp only [p, Walk.length_cons, topPath_length, m]
  have hinj : Set.InjOn (fun j : ℕ => 2 * j + 3) (Finset.range k : Set ℕ) := by
    intro a _ b _ h
    dsimp at h
    omega
  have hcard : ((Finset.range k).image (fun j => 2 * j + 3)).card = k := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hncard : (OddCycleLengths K).ncard = k := by
    rw [hset, Set.ncard_coe_finset, hcard]
  have hencard : (OddCycleLengths K).encard = k := by
    rw [← (oddCycleLengths_finite K).cast_ncard_eq, hncard]
  have hchi : K.chromaticNumber = 2 * k + 2 := by
    simp [K]
  exact ⟨hset, hncard, hencard, hchi⟩

end JSP_000078

#check JSP_000078.exists_dfsTree
#check JSP_000078.gyarfas_colorable_of_oddCycleLengths_le
#check JSP_000078.gyarfas_chromaticNumber_le_of_oddCycleLengths_le
#check JSP_000078.gyarfas_chromaticNumber_le_of_ncard_le
#check JSP_000078.completeGraph_sharpness

#print axioms JSP_000078.exists_dfsTree
#print axioms JSP_000078.gyarfas_colorable_of_oddCycleLengths_le
#print axioms JSP_000078.gyarfas_chromaticNumber_le_of_oddCycleLengths_le
#print axioms JSP_000078.gyarfas_chromaticNumber_le_of_ncard_le
#print axioms JSP_000078.completeGraph_sharpness
