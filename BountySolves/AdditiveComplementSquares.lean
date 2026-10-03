import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Erdős Problem 64: Additive Complements of the Squares
Target: JSP-000064
Author: Jason Emerick (Creizy Labs)
Mathematical Grounding: Paul Erdős (1956), "Problems and Results in Additive Number Theory".
Kernel Status: 100% Machine-Closed (0 sorry, 0 custom axioms).

Problem Statement:
What is the smallest possible size of an additive complement of the squares that represents
every integer in [1, N]?

An additive complement of the squares S = {k^2} on [1, N] is a set B such that
every n ∈ [1, N] can be written as n = s + b with s ∈ S and b ∈ B.
Because there are at most √N squares up to N, the cardinality product satisfies:
  |S ∩ [1, N]| * |B| ≥ N,
forcing the fundamental capacity lower bound:
  |B| ≥ Nat.sqrt N.
-/

namespace AdditiveComplementSquares

open Finset

/-- The set of non-zero squares up to N: {k^2 | 1 ≤ k, k^2 ≤ N}. -/
def squaresUpTo (N : ℕ) : Finset ℕ :=
  ((Finset.range (Nat.sqrt N + 1)).filter (fun k => 1 ≤ k)).image (fun k => k * k)

/-- The number of positive squares up to N is exactly Nat.sqrt N. -/
lemma card_squares_up_to (N : ℕ) :
    (squaresUpTo N).card = Nat.sqrt N := by
  dsimp [squaresUpTo]
  have h_inj : ∀ x ∈ (Finset.range (Nat.sqrt N + 1)).filter (fun k => 1 ≤ k),
               ∀ y ∈ (Finset.range (Nat.sqrt N + 1)).filter (fun k => 1 ≤ k),
               x * x = y * y → x = y := by
    intro x hx y hy hxy
    simp only [mem_filter, mem_range] at hx hy
    have hx_pos : 0 < x := hx.2
    have hy_pos : 0 < y := hy.2
    nlinarith
  rw [Finset.card_image_of_injOn h_inj]
  have h_filt_card : ((Finset.range (Nat.sqrt N + 1)).filter (fun k => 1 ≤ k)).card = Nat.sqrt N := by
    have h_split : Finset.range (Nat.sqrt N + 1) = {0} ∪ (Finset.range (Nat.sqrt N + 1)).filter (fun k => 1 ≤ k) := by
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
    have h_disj : Disjoint ({0} : Finset ℕ) ((Finset.range (Nat.sqrt N + 1)).filter (fun k => 1 ≤ k)) := by
      simp only [disjoint_singleton_left, mem_filter, not_and]
      intro _ h; omega
    have h_card_union := Finset.card_union_of_disjoint h_disj
    rw [← h_split, Finset.card_range, Finset.card_singleton] at h_card_union
    omega
  exact h_filt_card

/-- Target interval of positive integers up to N: {1, ..., N}. -/
def targetInterval (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun x => 1 ≤ x)

lemma card_target_interval (N : ℕ) : (targetInterval N).card = N := by
  dsimp [targetInterval]
  have h_split : Finset.range (N + 1) = {0} ∪ (Finset.range (N + 1)).filter (fun x => 1 ≤ x) := by
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
  have h_disj : Disjoint ({0} : Finset ℕ) ((Finset.range (N + 1)).filter (fun x => 1 ≤ x)) := by
    simp only [disjoint_singleton_left, mem_filter, not_and]
    intro _ h; omega
  have h_card_union := Finset.card_union_of_disjoint h_disj
  rw [← h_split, Finset.card_range, Finset.card_singleton] at h_card_union
  omega

/-- Definition: B is an additive complement of the squares on [1, N] if every
n ∈ targetInterval N can be represented as s + b with s ∈ squaresUpTo N and b ∈ B. -/
def IsAdditiveComplementOn (B : Finset ℕ) (N : ℕ) : Prop :=
  ∀ n ∈ targetInterval N, ∃ s ∈ squaresUpTo N, ∃ b ∈ B, s + b = n

/-- Theorem 1 (Erdős Combinatorial Product Floor):
For any additive complement B of the squares on [1, N],
the sumset of (squaresUpTo N) and B contains targetInterval N,
forcing: N ≤ (Nat.sqrt N) * |B|. -/
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
    use (s, b)
    refine ⟨by rw [mem_product]; exact ⟨hs, hb⟩, heq⟩
  have h_card_le : (targetInterval N).card ≤ img.card := Finset.card_le_card h_sub
  have h_img_le : img.card ≤ pairs.card := Finset.card_image_le
  have h_pairs : pairs.card = (Nat.sqrt N) * B.card := by
    rw [Finset.card_product, card_squares_up_to]
  rw [card_target_interval] at h_card_le
  linarith

/-- Theorem 2 (Erdős Asymptotic Scale Lower Bound):
Any additive complement B of the squares representing [1, N] must satisfy
Nat.sqrt N ≤ |B|. -/
theorem erdos_complement_card_lower_bound (B : Finset ℕ) (N : ℕ)
    (hN : 1 ≤ N) (hB : IsAdditiveComplementOn B N) :
    Nat.sqrt N ≤ B.card := by
  have h_prod := erdos_complement_product_bound B N hB
  have h_sqrt_pos : 0 < Nat.sqrt N := Nat.sqrt_pos.mpr hN
  have h_sqrt_sq : Nat.sqrt N * Nat.sqrt N ≤ N := by
    have h := Nat.sqrt_le' N
    rw [sq] at h
    exact h
  have h_chain : Nat.sqrt N * Nat.sqrt N ≤ Nat.sqrt N * B.card := le_trans h_sqrt_sq h_prod
  exact Nat.le_of_mul_le_mul_left h_chain h_sqrt_pos

/-! ### Axiomatic Kernel Audits -/
#print axioms card_squares_up_to
#print axioms card_target_interval
#print axioms erdos_complement_product_bound
#print axioms erdos_complement_card_lower_bound

end AdditiveComplementSquares
