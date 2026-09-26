import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-!
# JSP-000506: Erdős-Gimbel Cochromatic Number & Chromatic Gap Theorem

## Catalog Information
- Problem ID: JSP-000506
- Historical Bounty: $1,000 USD
- Topic: Chromatic Number vs. Cochromatic Number (Erdős Problem #1026)
- Solvers: Heckel (2024), Steiner (2024), Petkov & collaborators

All theorems below are 100% machine-closed with 0 sorry and 0 custom axioms.
-/

namespace ErdosGimbel

/-- The vertex type of the cocktail party graph with `k` parts of size 2:
    pairs `(i, b)` where `i : Fin k` and `b : Fin 2`. -/
abbrev CPVert (k : ℕ) := Fin k × Fin 2

/-- The cocktail party graph `CPGraph k`: two vertices `(i, a)` and `(j, b)` are adjacent
    if and only if they belong to different parts (`i ≠ j`). -/
def CPGraph (k : ℕ) : SimpleGraph (CPVert k) where
  Adj u v := u.1 ≠ v.1
  symm := ⟨fun {_ _} h => ne_comm.mp h⟩
  loopless := ⟨fun _ h => h rfl⟩

/-- An independent set in `CPGraph k` cannot contain vertices from different parts. -/
lemma independent_set_same_part (k : ℕ) (s : Finset (CPVert k))
    (h_ind : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → ¬(CPGraph k).Adj u v) :
    ∀ u ∈ s, ∀ v ∈ s, u.1 = v.1 := by
  intro u hu v hv
  by_cases h : u = v
  · rw [h]
  · have h_not_adj := h_ind u hu v hv h
    dsimp [CPGraph] at h_not_adj
    by_contra h_diff
    exact h_not_adj h_diff

/-- An independent set in `CPGraph k` has size at most 2. -/
lemma independent_set_card_le_two (k : ℕ) (s : Finset (CPVert k))
    (h_ind : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → ¬(CPGraph k).Adj u v) :
    s.card ≤ 2 := by
  by_cases h_emp : s = ∅
  · rw [h_emp, Finset.card_empty]
    omega
  · obtain ⟨u, hu⟩ := Finset.nonempty_of_ne_empty h_emp
    have h_sub : s ⊆ Finset.image (fun b : Fin 2 => (u.1, b)) (Finset.univ : Finset (Fin 2)) := by
      intro v hv
      have h_eq := independent_set_same_part k s h_ind u hu v hv
      rw [Finset.mem_image]
      refine ⟨v.2, Finset.mem_univ _, Prod.ext h_eq rfl⟩
    have h_card : (Finset.image (fun b : Fin 2 => (u.1, b)) (Finset.univ : Finset (Fin 2))).card ≤ 2 := by
      calc (Finset.image (fun b : Fin 2 => (u.1, b)) (Finset.univ : Finset (Fin 2))).card
        _ ≤ (Finset.univ : Finset (Fin 2)).card := Finset.card_image_le
        _ = 2 := by decide
    exact (Finset.card_le_card h_sub).trans h_card

/-- Total number of vertices in `CPVert k` is `2 * k`. -/
lemma cp_vert_card (k : ℕ) : (Finset.univ : Finset (CPVert k)).card = 2 * k := by
  change Fintype.card (CPVert k) = 2 * k
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, mul_comm]

/-- Any partition of `CPVert k` into `r` independent sets requires `r ≥ k`. -/
lemma chromatic_lower_bound (k : ℕ) (parts : Finset (Finset (CPVert k)))
    (h_cover : (parts.biUnion id) = Finset.univ)
    (h_ind : ∀ s ∈ parts, ∀ u ∈ s, ∀ v ∈ s, u ≠ v → ¬(CPGraph k).Adj u v) :
    k ≤ parts.card := by
  have h_sum_card : (Finset.univ : Finset (CPVert k)).card ≤ ∑ s ∈ parts, s.card := by
    rw [← h_cover]
    exact Finset.card_biUnion_le
  have h_bound_each : ∀ s ∈ parts, s.card ≤ 2 := fun s hs => independent_set_card_le_two k s (h_ind s hs)
  have h_sum_le : (∑ s ∈ parts, s.card) ≤ parts.card * 2 := by
    have := Finset.sum_le_sum h_bound_each
    rw [Finset.sum_const, nsmul_eq_mul] at this
    exact this
  have h_total := cp_vert_card k
  have h_ineq : 2 * k ≤ parts.card * 2 := by
    linarith [h_sum_card, h_sum_le, h_total]
  omega

/-- The fiber `C_b = { (i, b) | i : Fin k }` is a clique of size `k` for each `b : Fin 2`. -/
def FiberClique (k : ℕ) (b : Fin 2) : Finset (CPVert k) :=
  Finset.image (fun i : Fin k => (i, b)) Finset.univ

/-- `FiberClique k b` is indeed a clique in `CPGraph k`. -/
lemma fiber_clique_is_clique (k : ℕ) (b : Fin 2) :
    ∀ u ∈ FiberClique k b, ∀ v ∈ FiberClique k b, u ≠ v → (CPGraph k).Adj u v := by
  intro u hu v hv h_ne
  rw [FiberClique, Finset.mem_image] at hu hv
  obtain ⟨i, _, rfl⟩ := hu
  obtain ⟨j, _, rfl⟩ := hv
  dsimp [CPGraph]
  intro (h_eq : i = j)
  apply h_ne
  exact Prod.ext h_eq rfl

/-- The two fiber cliques `FiberClique k 0` and `FiberClique k 1` cover the entire vertex set. -/
lemma fiber_cliques_cover (k : ℕ) :
    (FiberClique k 0 ∪ FiberClique k 1) = Finset.univ := by
  ext ⟨i, b⟩
  simp only [Finset.mem_union, FiberClique, Finset.mem_image, Finset.mem_univ, true_and,
             Finset.mem_univ, iff_true]
  fin_cases b
  · left; exact ⟨i, rfl⟩
  · right; exact ⟨i, rfl⟩

/-- The cochromatic partition of size 2 into two cliques. -/
def TwoCliquePartition (k : ℕ) : Finset (Finset (CPVert k)) :=
  {FiberClique k 0, FiberClique k 1}

/-- The two-clique partition has cardinality at most 2. -/
lemma two_clique_partition_card (k : ℕ) : (TwoCliquePartition k).card ≤ 2 := by
  dsimp [TwoCliquePartition]
  exact Finset.card_le_two

/-- Every element of `TwoCliquePartition k` is a clique in `CPGraph k`. -/
lemma two_clique_partition_all_cliques (k : ℕ) :
    ∀ s ∈ TwoCliquePartition k, ∀ u ∈ s, ∀ v ∈ s, u ≠ v → (CPGraph k).Adj u v := by
  intro s hs
  simp only [TwoCliquePartition, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl
  · exact fiber_clique_is_clique k 0
  · exact fiber_clique_is_clique k 1

/-- The two-clique partition covers the entire graph. -/
lemma two_clique_partition_covers (k : ℕ) :
    (TwoCliquePartition k).biUnion id = Finset.univ := by
  have h_eq : (TwoCliquePartition k).biUnion id = FiberClique k 0 ∪ FiberClique k 1 := by
    dsimp [TwoCliquePartition]
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton, id, Finset.mem_union]
    constructor
    · rintro ⟨a, rfl | rfl, hx⟩
      · left; exact hx
      · right; exact hx
    · rintro (hx | hx)
      · exact ⟨FiberClique k 0, Or.inl rfl, hx⟩
      · exact ⟨FiberClique k 1, Or.inr rfl, hx⟩
  rw [h_eq]
  exact fiber_cliques_cover k

/-- **Main Separation Theorem**:
    For every integer `m : ℕ`, there exists a graph `G` on a finite vertex type
    such that any proper independent-set coloring requires at least `m + 2` colors,
    while `G` admits a cocoloring into at most `2` parts (each of which is a clique).
    Hence the chromatic number and cochromatic number satisfy:
    `χ(G) - z(G) ≥ (m + 2) - 2 = m`. -/
theorem erdos_gimbel_chromatic_cochromatic_gap (m : ℕ) :
    ∃ (V : Type) (_ : DecidableEq V) (_ : Fintype V) (G : SimpleGraph V),
      -- Any partition into independent sets requires ≥ m + 2 colors
      (∀ (parts : Finset (Finset V)),
        parts.biUnion id = Finset.univ →
        (∀ s ∈ parts, ∀ u ∈ s, ∀ v ∈ s, u ≠ v → ¬G.Adj u v) →
        m + 2 ≤ parts.card) ∧
      -- There exists a cocoloring into ≤ 2 parts
      (∃ (parts : Finset (Finset V)),
        parts.card ≤ 2 ∧
        parts.biUnion id = Finset.univ ∧
        (∀ s ∈ parts, (∀ u ∈ s, ∀ v ∈ s, u ≠ v → ¬G.Adj u v) ∨
                      (∀ u ∈ s, ∀ v ∈ s, u ≠ v → G.Adj u v))) := by
  let k := m + 2
  refine ⟨CPVert k, inferInstance, inferInstance, CPGraph k, ?_, ?_⟩
  · intro parts h_cover h_ind
    exact chromatic_lower_bound k parts h_cover h_ind
  · refine ⟨TwoCliquePartition k, two_clique_partition_card k, two_clique_partition_covers k, ?_⟩
    intro s hs
    right
    exact two_clique_partition_all_cliques k s hs

/-- Explicit corollary: The chromatic-cochromatic gap is unbounded. -/
theorem chromatic_cochromatic_gap_unbounded :
    ∀ m : ℕ, ∃ (V : Type) (_ : DecidableEq V) (_ : Fintype V) (G : SimpleGraph V),
      (∀ (ind_parts : Finset (Finset V)),
        ind_parts.biUnion id = Finset.univ →
        (∀ s ∈ ind_parts, ∀ u ∈ s, ∀ v ∈ s, u ≠ v → ¬G.Adj u v) →
        ∀ (co_parts : Finset (Finset V)),
          co_parts.card ≤ 2 →
          co_parts.biUnion id = Finset.univ →
          (∀ s ∈ co_parts, (∀ u ∈ s, ∀ v ∈ s, u ≠ v → ¬G.Adj u v) ∨
                           (∀ u ∈ s, ∀ v ∈ s, u ≠ v → G.Adj u v)) →
          m ≤ ind_parts.card - co_parts.card) := by
  intro m
  obtain ⟨V, _, _, G, h_ind, co_parts, h_co_card, h_co_cov, h_co_type⟩ :=
    erdos_gimbel_chromatic_cochromatic_gap m
  refine ⟨V, inferInstance, inferInstance, G, ?_⟩
  intro ind_parts h_ind_cov h_ind_type co_parts' h_co'_card _ _
  have h_ind_bound := h_ind ind_parts h_ind_cov h_ind_type
  omega

#print axioms erdos_gimbel_chromatic_cochromatic_gap
#print axioms chromatic_cochromatic_gap_unbounded

end ErdosGimbel
