import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith

/-!
# Lower Bound on the Maximum Element of Sets with Distinct Subset Sums
Problem: Lower Bound on the Maximum Element
Author: Jason Emerick (Creizy Labs)
Problem Reference: JSP-000043
Description: For any finite set S ⊂ ℕ with distinct subset sums, the maximum element
max(S) is bounded below by (2^|S| - 1) / |S|, forcing any upper bound m on S to satisfy
2^|S| ≤ |S| * m + 1.
Kernel Status: 100% Machine-Closed Core (0 sorry, 0 custom axioms).
-/

namespace LowerBoundMaxElement

open Finset

/-- A set of natural numbers S has distinct subset sums if distinct subsets
produce distinct sums. -/
def HasDistinctSubsetSums (S : Finset ℕ) : Prop :=
  ∀ ⦃u v : Finset ℕ⦄, u ⊆ S → v ⊆ S → u.sum id = v.sum id → u = v

/-- Monotonicity: For any subset u ⊆ S of natural numbers, the sum of elements in u
is bounded above by the total sum of S. -/
lemma sum_le_sum_of_subset (u S : Finset ℕ) (h : u ⊆ S) :
    u.sum id ≤ S.sum id := by
  classical
  have h_disj : Disjoint u (S \ u) := Finset.disjoint_sdiff
  have h_sum : (u ∪ (S \ u)).sum id = u.sum id + (S \ u).sum id :=
    Finset.sum_union h_disj
  rw [Finset.union_sdiff_of_subset h] at h_sum
  omega

/-- Theorem 1 (Combinatorial Capacity Floor):
For any finite set S of natural numbers with distinct subset sums,
the powerset of size 2^|S| injects into the integer range [0, ∑ S],
forcing the capacity inequality: 2^|S| ≤ (∑ S) + 1. -/
theorem combinatorial_capacity_floor (S : Finset ℕ) (h_distinct : HasDistinctSubsetSums S) :
    2 ^ S.card ≤ S.sum id + 1 := by
  classical
  let f : Finset ℕ → ℕ := fun u => u.sum id
  let target := Finset.range (S.sum id + 1)
  have h_maps_to : ∀ u ∈ S.powerset, f u ∈ target := by
    intro u hu
    rw [Finset.mem_powerset] at hu
    have h_le : u.sum id ≤ S.sum id := sum_le_sum_of_subset u S hu
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le h_le
  have h_inj : ∀ u ∈ S.powerset, ∀ v ∈ S.powerset, f u = f v → u = v := by
    intro u hu v hv heq
    rw [Finset.mem_powerset] at hu hv
    exact h_distinct hu hv heq
  have h_card_le := Finset.card_le_card_of_injOn f h_maps_to h_inj
  rw [Finset.card_powerset, Finset.card_range] at h_card_le
  exact h_card_le

/-- The sum of elements in S is bounded by the cardinality times any upper bound m. -/
lemma sum_le_card_mul_bound (S : Finset ℕ) (m : ℕ) (hm : ∀ x ∈ S, x ≤ m) :
    S.sum id ≤ S.card * m := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    have hx : a ≤ m := hm a (Finset.mem_insert_self a s)
    have hsub : ∀ y ∈ s, y ≤ m := fun y hy => hm y (Finset.mem_insert_of_mem hy)
    have h_ih := ih hsub
    change a + s.sum id ≤ (s.card + 1) * m
    rw [add_mul, one_mul]
    omega

/-- Theorem 2 (Lower Bound on the Maximum Element):
For any finite set S ⊂ ℕ with distinct subset sums and any upper bound m ≥ max(S),
we have 2^|S| ≤ |S| * m + 1, which guarantees that the maximum element satisfies
m ≥ (2^|S| - 1) / |S|. -/
theorem distinct_subset_sums_max_element_bound (S : Finset ℕ)
    (h_distinct : HasDistinctSubsetSums S) (m : ℕ) (hm : ∀ x ∈ S, x ≤ m) :
    2 ^ S.card ≤ S.card * m + 1 := by
  have h_cap := combinatorial_capacity_floor S h_distinct
  have h_sum := sum_le_card_mul_bound S m hm
  omega

/-- Geometric sum: ∑_{i=0}^{n-1} 2^i = 2^n - 1. -/
lemma geom_sum_powers_of_two (n : ℕ) :
    (Finset.range n).sum (fun i => 2 ^ i) = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega

/-- Sharpness of the capacity floor for powers of two. -/
theorem capacity_floor_sharpness (n : ℕ) :
    2 ^ n ≤ ((Finset.range n).sum (fun i => 2 ^ i)) + 1 := by
  rw [geom_sum_powers_of_two n]
  have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  omega

/-! ### Axiomatic Kernel Audits -/
#print axioms sum_le_sum_of_subset
#print axioms combinatorial_capacity_floor
#print axioms sum_le_card_mul_bound
#print axioms distinct_subset_sums_max_element_bound
#print axioms geom_sum_powers_of_two
#print axioms capacity_floor_sharpness

end LowerBoundMaxElement
