/-
Copyright (c) 2026 Compendium Formal Verification Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Erdős Problem 64 (JSP-000064): Additive Complements of the Squares

An additive complement of the squares `S = {k² | k ≥ 1}` on `[1, N]` is a finite set `B`
such that every `n ∈ [1, N]` can be written as `n = s + b` with `s ∈ S ∩ [1, N]` and `b ∈ B`.
Because there are exactly `Nat.sqrt N` positive squares up to `N`, the sumset cardinality
bound forces:
* `N ≤ Nat.sqrt N * |B|` (`erdos_complement_product_bound`)
* `Nat.sqrt N ≤ |B|` for all `N ≥ 1` (`erdos_complement_card_lower_bound`)

## Verification Guarantees
* Zero `sorry`
* Zero `axiom`
* Zero floating-point approximations (exact `Nat` and `Finset ℕ` combinatorics)
-/

namespace AdditiveComplementSquares

open Finset

/-- The finite set of positive integers `{1, ..., M}` defined as `(range (M + 1)).filter (1 ≤ ·)`. -/
def posInterval (M : ℕ) : Finset ℕ :=
  (Finset.range (M + 1)).filter (fun k => 1 ≤ k)

/-- The cardinality of `posInterval M = {1, ..., M}` is exactly `M`. -/
lemma card_posInterval (M : ℕ) : (posInterval M).card = M := by
  dsimp [posInterval]
  have h_split : Finset.range (M + 1) =
      ({0} : Finset ℕ) ∪ (Finset.range (M + 1)).filter (fun k => 1 ≤ k) := by
    ext a
    simp only [mem_range, mem_union, mem_singleton, mem_filter]
    constructor
    · intro ha
      by_cases h0 : a = 0
      · left; exact h0
      · right; exact ⟨ha, by omega⟩
    · rintro (rfl | ⟨ha, _⟩)
      · omega
      · exact ha
  have h_disj : Disjoint ({0} : Finset ℕ) ((Finset.range (M + 1)).filter (fun k => 1 ≤ k)) := by
    simp only [disjoint_singleton_left, mem_filter, not_and]
    intro _ h
    omega
  have h_card_union := Finset.card_union_eq_card_add_card.mpr h_disj
  rw [← h_split, Finset.card_range, Finset.card_singleton] at h_card_union
  omega

/-- The set of non-zero squares up to `N`: `{k² | 1 ≤ k ≤ Nat.sqrt N}`. -/
def squaresUpTo (N : ℕ) : Finset ℕ :=
  (posInterval (Nat.sqrt N)).image (fun k => k * k)

/-- The squaring map `k ↦ k * k` is injective on `ℕ`. -/
lemma sq_injective_nat : Function.Injective (fun k : ℕ => k * k) := by
  intro x y hxy
  nlinarith

/-- The number of positive squares up to `N` is exactly `Nat.sqrt N`. -/
lemma card_squares_up_to (N : ℕ) :
    (squaresUpTo N).card = Nat.sqrt N := by
  unfold squaresUpTo
  rw [Finset.card_image_of_injective _ sq_injective_nat, card_posInterval]

/-- Target interval of positive integers up to `N`: `{1, ..., N}`. -/
def targetInterval (N : ℕ) : Finset ℕ :=
  posInterval N

/-- The cardinality of `targetInterval N` is `N`. -/
lemma card_target_interval (N : ℕ) : (targetInterval N).card = N :=
  card_posInterval N

/-- `B` is an additive complement of the squares on `[1, N]` if every `n ∈ targetInterval N`
    can be written as `s + b` with `s ∈ squaresUpTo N` and `b ∈ B`. -/
def IsAdditiveComplementOn (B : Finset ℕ) (N : ℕ) : Prop :=
  ∀ n ∈ targetInterval N, ∃ s ∈ squaresUpTo N, ∃ b ∈ B, s + b = n

/-- Theorem 1 (Erdős Combinatorial Product Floor):
    For any additive complement `B` of the squares on `[1, N]`,
    `N ≤ Nat.sqrt N * B.card`. -/
theorem erdos_complement_product_bound (B : Finset ℕ) (N : ℕ)
    (hB : IsAdditiveComplementOn B N) :
    N ≤ (Nat.sqrt N) * B.card := by
  classical
  let pairs := (squaresUpTo N) ×ˢ B
  let img := pairs.image (fun p => p.1 + p.2)
  have h_sub : targetInterval N ⊆ img := by
    intro n hn
    rcases hB n hn with ⟨s, hs, b, hb, heq⟩
    rw [mem_image]
    exact ⟨(s, b), mem_product.mpr ⟨hs, hb⟩, heq⟩
  have h_card_le : (targetInterval N).card ≤ img.card := Finset.card_le_card h_sub
  have h_img_le : img.card ≤ pairs.card := Finset.card_image_le
  have h_pairs : pairs.card = (Nat.sqrt N) * B.card := by
    rw [Finset.card_product, card_squares_up_to]
  rw [card_target_interval] at h_card_le
  omega

/-- Theorem 2 (Erdős Asymptotic Scale Lower Bound):
    Any additive complement `B` of the squares representing `[1, N]` (`N ≥ 1`) satisfies
    `Nat.sqrt N ≤ B.card`. -/
theorem erdos_complement_card_lower_bound (B : Finset ℕ) (N : ℕ)
    (hN : 1 ≤ N) (hB : IsAdditiveComplementOn B N) :
    Nat.sqrt N ≤ B.card := by
  have h_prod : N ≤ Nat.sqrt N * B.card := erdos_complement_product_bound B N hB
  have h_sqrt_pos : 0 < Nat.sqrt N := Nat.sqrt_pos.mpr hN
  have h_sqrt_sq : Nat.sqrt N * Nat.sqrt N ≤ N := Nat.sqrt_le N
  have h_chain : Nat.sqrt N * Nat.sqrt N ≤ Nat.sqrt N * B.card :=
    le_trans h_sqrt_sq h_prod
  exact Nat.le_of_mul_le_mul_left h_chain h_sqrt_pos

#print axioms erdos_complement_product_bound
#print axioms erdos_complement_card_lower_bound

end AdditiveComplementSquares
