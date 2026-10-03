import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Ring

namespace ErdosGimbel

/-!
# JSP-000506: Erdős–Gimbel Cochromatic Number Unbounded Gap
Theorem: The gap between the chromatic number χ(G) and the cochromatic
number ζ(G) can be arbitrarily large.

Construction:
For any parameter m, let k = m + 2.
Consider the cocktail party graph CPGraph(k) on vertices Fin k × Fin 2:
- (i₁, j₁) ~ (i₂, j₂) ↔ i₁ ≠ i₂.
Properties:
1. Every independent set has cardinality ≤ 2 (all vertices must share first coordinate).
2. Any proper coloring (partition into independent sets) requires ≥ k colors.
3. The vertex set is partitioned into 2 cliques:
   C₀ = {(i, 0) : i ∈ Fin k}
   C₁ = {(i, 1) : i ∈ Fin k}
   hence the cochromatic number is at most 2.
4. Gap: χ(CPGraph(k)) - ζ(CPGraph(k)) ≥ k - 2 = m.
-/

/-- A simple graph on vertex type V. -/
structure SimpleGraph (V : Type*) where
  Adj : V → V → Prop
  symm : ∀ {u v : V}, Adj u v → Adj v u
  loopless : ∀ {u : V}, ¬ Adj u u

/-- Vertex set of the order-k cocktail party graph: Fin k × Fin 2. -/
abbrev CPVert (k : ℕ) : Type := Fin k × Fin 2

/-- The cocktail party graph CPGraph(k):
Two vertices are adjacent if and only if their first coordinates differ. -/
def CPGraph (k : ℕ) : SimpleGraph (CPVert k) where
  Adj u v := u.1 ≠ v.1
  symm := by
    intro u v h
    exact h.symm
  loopless := by
    intro u h
    exact h rfl

/-! ### 1. Graph Invariant Definitions -/

/-- A subset of vertices is an independent set if no two vertices are adjacent. -/
def IsIndSet {V : Type*} (G : SimpleGraph V) (s : Finset V) : Prop :=
  ∀ u ∈ s, ∀ v ∈ s, ¬ G.Adj u v

/-- A subset of vertices is a clique if every pair of distinct vertices is adjacent. -/
def IsClique {V : Type*} (G : SimpleGraph V) (s : Finset V) : Prop :=
  ∀ u ∈ s, ∀ v ∈ s, u ≠ v → G.Adj u v

/-- A co-part is either an independent set or a clique. -/
def IsCoPart {V : Type*} (G : SimpleGraph V) (s : Finset V) : Prop :=
  IsIndSet G s ∨ IsClique G s

/-! ### 2. Independent Set Cardinality Bound -/

lemma fin2_cases (j : Fin 2) : j = 0 ∨ j = 1 := by
  rcases j with ⟨val, hlt⟩
  cases val with
  | zero => left; ext; rfl
  | succ val =>
    cases val with
    | zero => right; ext; rfl
    | succ val => omega

/-- Lemma 1: Any independent set in CPGraph(k) contains at most 2 vertices. -/
theorem indSet_card_le_two (k : ℕ) (s : Finset (CPVert k))
    (hs : IsIndSet (CPGraph k) s) : s.card ≤ 2 := by
  have h_inj : ∀ u ∈ s, ∀ v ∈ s, u.2 = v.2 → u = v := by
    intro u hu v hv h_snd
    have h_not_adj := hs u hu v hv
    dsimp [CPGraph] at h_not_adj
    have h_fst : u.1 = v.1 := by
      by_contra hne
      exact h_not_adj hne
    exact Prod.ext h_fst h_snd
  have h_card_img : (s.image Prod.snd).card = s.card :=
    Finset.card_image_of_injOn h_inj
  have h_sub : s.image Prod.snd ⊆ (Finset.univ : Finset (Fin 2)) :=
    Finset.subset_univ _
  have h_le := Finset.card_le_card h_sub
  have h_univ_card : (Finset.univ : Finset (Fin 2)).card = 2 := by decide
  rw [h_card_img] at h_le
  rw [h_univ_card] at h_le
  exact h_le

/-! ### 3. Chromatic Lower Bound via Fiber Injection -/

/-- Lemma 2: Any proper coloring (family of independent sets covering V)
requires at least k colors. -/
theorem ind_cover_card_ge (k : ℕ) (ind_parts : Finset (Finset (CPVert k)))
    (h_cov : ∀ v : CPVert k, ∃ s ∈ ind_parts, v ∈ s)
    (h_ind : ∀ s ∈ ind_parts, IsIndSet (CPGraph k) s) :
    k ≤ ind_parts.card := by
  classical
  let choice_part : Fin k → Finset (CPVert k) :=
    fun i => Classical.choose (h_cov (i, 0))
  have h_choice_mem : ∀ i : Fin k, choice_part i ∈ ind_parts :=
    fun i => (Classical.choose_spec (h_cov (i, 0))).1
  have h_choice_spec : ∀ i : Fin k, (i, (0 : Fin 2)) ∈ choice_part i :=
    fun i => (Classical.choose_spec (h_cov (i, 0))).2
  have h_inj : ∀ i j : Fin k, choice_part i = choice_part j → i = j := by
    intro i j heq
    by_contra hne
    have hi : (i, (0 : Fin 2)) ∈ choice_part i := h_choice_spec i
    have hj : (j, (0 : Fin 2)) ∈ choice_part i := by
      rw [heq]
      exact h_choice_spec j
    have hind := h_ind (choice_part i) (h_choice_mem i)
    have h_not_adj := hind (i, (0 : Fin 2)) hi (j, (0 : Fin 2)) hj
    dsimp [CPGraph] at h_not_adj
    exact h_not_adj hne
  let img := (Finset.univ : Finset (Fin k)).image choice_part
  have h_img_sub : img ⊆ ind_parts := by
    intro s hs
    rw [Finset.mem_image] at hs
    rcases hs with ⟨i, _, rfl⟩
    exact h_choice_mem i
  have h_card_le : img.card ≤ ind_parts.card :=
    Finset.card_le_card h_img_sub
  have h_card_img : img.card = (Finset.univ : Finset (Fin k)).card :=
    Finset.card_image_of_injective (Finset.univ : Finset (Fin k)) h_inj
  rw [Finset.card_univ, Fintype.card_fin] at h_card_img
  omega

/-! ### 4. Explicit 2-Clique Cocoloring -/

/-- The clique formed by setting the second coordinate to 0. -/
def clique_zero (k : ℕ) : Finset (CPVert k) :=
  (Finset.univ : Finset (Fin k)).image (fun i => (i, (0 : Fin 2)))

/-- The clique formed by setting the second coordinate to 1. -/
def clique_one (k : ℕ) : Finset (CPVert k) :=
  (Finset.univ : Finset (Fin k)).image (fun i => (i, (1 : Fin 2)))

theorem clique_zero_is_clique (k : ℕ) : IsClique (CPGraph k) (clique_zero k) := by
  intro u hu v hv hne
  dsimp [clique_zero] at hu hv
  rw [Finset.mem_image] at hu hv
  rcases hu with ⟨i1, _, rfl⟩
  rcases hv with ⟨i2, _, rfl⟩
  dsimp [CPGraph]
  intro h_same
  cases h_same
  exact hne rfl

theorem clique_one_is_clique (k : ℕ) : IsClique (CPGraph k) (clique_one k) := by
  intro u hu v hv hne
  dsimp [clique_one] at hu hv
  rw [Finset.mem_image] at hu hv
  rcases hu with ⟨i1, _, rfl⟩
  rcases hv with ⟨i2, _, rfl⟩
  dsimp [CPGraph]
  intro h_same
  cases h_same
  exact hne rfl

/-- The canonical cocoloring family consisting of the two cliques. -/
def canonicalCoParts (k : ℕ) : Finset (Finset (CPVert k)) :=
  {clique_zero k, clique_one k}

theorem canonicalCoParts_covers (k : ℕ) :
    ∀ v : CPVert k, ∃ s ∈ canonicalCoParts k, v ∈ s := by
  intro ⟨i, b⟩
  rcases fin2_cases b with rfl | rfl
  · use clique_zero k
    refine ⟨by simp [canonicalCoParts], ?_⟩
    dsimp [clique_zero]
    rw [Finset.mem_image]
    exact ⟨i, Finset.mem_univ _, rfl⟩
  · use clique_one k
    refine ⟨by simp [canonicalCoParts], ?_⟩
    dsimp [clique_one]
    rw [Finset.mem_image]
    exact ⟨i, Finset.mem_univ _, rfl⟩

theorem canonicalCoParts_all_coparts (k : ℕ) :
    ∀ s ∈ canonicalCoParts k, IsCoPart (CPGraph k) s := by
  intro s hs
  simp only [canonicalCoParts, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl
  · right
    exact clique_zero_is_clique k
  · right
    exact clique_one_is_clique k

theorem canonicalCoParts_card_le_two (k : ℕ) :
    (canonicalCoParts k).card ≤ 2 := by
  dsimp [canonicalCoParts]
  have h1 := Finset.card_insert_le (clique_zero k) {clique_one k}
  have h2 : ({clique_one k} : Finset (Finset (CPVert k))).card = 1 :=
    Finset.card_singleton (clique_one k)
  omega

/-! ### 5. Main Theorems: Unbounded Gap -/

/-- Theorem 1 (Erdős–Gimbel Gap Construction):
For any m, the cocktail party graph with k = m + 2 admits a cocoloring
of size at most 2, while every proper coloring requires at least m + 2 parts. -/
theorem erdos_gimbel_chromatic_cochromatic_gap (m : ℕ) :
    ∃ (V : Type) (_ : DecidableEq V) (_ : Fintype V) (G : SimpleGraph V)
      (co_parts : Finset (Finset V)),
      co_parts.card ≤ 2 ∧
      (∀ v : V, ∃ s ∈ co_parts, v ∈ s) ∧
      (∀ s ∈ co_parts, IsCoPart G s) ∧
      (∀ (ind_parts : Finset (Finset V)),
        (∀ v : V, ∃ s ∈ ind_parts, v ∈ s) →
        (∀ s ∈ ind_parts, IsIndSet G s) →
        m + 2 ≤ ind_parts.card) := by
  let k := m + 2
  refine ⟨CPVert k, inferInstance, inferInstance, CPGraph k, canonicalCoParts k, ?_⟩
  refine ⟨canonicalCoParts_card_le_two k,
          canonicalCoParts_covers k,
          canonicalCoParts_all_coparts k, ?_⟩
  intro ind_parts h_cov h_ind
  exact ind_cover_card_ge k ind_parts h_cov h_ind

/-- Theorem 2 (JSP-000506 Unbounded Gap Closed):
For any natural number m, there exists a finite graph G admitting a cocoloring
`co_parts` such that EVERY proper vertex coloring `ind_parts` satisfies:
|ind_parts| ≥ |co_parts| + m. -/
theorem chromatic_cochromatic_gap_unbounded (m : ℕ) :
    ∃ (V : Type) (_ : DecidableEq V) (_ : Fintype V) (G : SimpleGraph V)
      (co_parts : Finset (Finset V)),
      (∀ v : V, ∃ s ∈ co_parts, v ∈ s) ∧
      (∀ s ∈ co_parts, IsCoPart G s) ∧
      (∀ (ind_parts : Finset (Finset V)),
        (∀ v : V, ∃ s ∈ ind_parts, v ∈ s) →
        (∀ s ∈ ind_parts, IsIndSet G s) →
        co_parts.card + m ≤ ind_parts.card) := by
  obtain ⟨V, _, _, G, co_parts, h_co_card, h_co_cov, h_co_type, h_ind_bound⟩ :=
    erdos_gimbel_chromatic_cochromatic_gap m
  refine ⟨V, inferInstance, inferInstance, G, co_parts, h_co_cov, h_co_type, ?_⟩
  intro ind_parts h_cov h_ind
  have h_bound := h_ind_bound ind_parts h_cov h_ind
  omega

/-! ### 6. Axiomatic Kernel Audits -/
#print axioms indSet_card_le_two
#print axioms ind_cover_card_ge
#print axioms clique_zero_is_clique
#print axioms clique_one_is_clique
#print axioms canonicalCoParts_covers
#print axioms canonicalCoParts_all_coparts
#print axioms canonicalCoParts_card_le_two
#print axioms erdos_gimbel_chromatic_cochromatic_gap
#print axioms chromatic_cochromatic_gap_unbounded

end ErdosGimbel
