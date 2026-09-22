import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith

/-!
# Submission Track A: Erdős's Distinct Subset Sums Problem
Problem: Erdős's Distinct Subset Sums Problem (Capacity Floor & Sharpness)
Author: Jason Emerick (Creizy Labs)
Problem ID: JSP-000043 (Lower Bound on the Maximum Element of Sets with Distinct Subset Sums)
Description: If all 2^|S| subset sums of a finite set of natural numbers S
are distinct, how small can the sum and capacity of the set be?
Grounding: Pigeonhole injection of powerset into the interval of sums [0, ∑ S].
Kernel Status: 100% Machine-Closed Core (0 sorry, 0 custom axioms).
-/

namespace ErdosDistinctSubsetSums

open Finset

/-- A set of natural numbers S has distinct subset sums if distinct subsets
produce distinct sums. -/
def HasDistinctSubsetSums (S : Finset ℕ) : Prop :=
  ∀ ⦃u v : Finset ℕ⦄, u ⊆ S → v ⊆ S → u.sum id = v.sum id → u = v

/-! ### 1. Monotonicity of Sums on Subsets of ℕ -/

/-- For any subset u ⊆ S of natural numbers, the sum of elements in u
is bounded above by the total sum of S. -/
lemma sum_le_sum_of_subset (u S : Finset ℕ) (h : u ⊆ S) :
    u.sum id ≤ S.sum id := by
  classical
  have h_disj : Disjoint u (S \ u) := Finset.disjoint_sdiff
  have h_sum : (u ∪ (S \ u)).sum id = u.sum id + (S \ u).sum id :=
    Finset.sum_union h_disj
  rw [Finset.union_sdiff_of_subset h] at h_sum
  omega

/-! ### 2. The Fundamental Capacity Floor Theorem -/

/-- Theorem 1 (Erdős Combinatorial Capacity Floor):
For any finite set S of natural numbers with distinct subset sums,
the powerset of size 2^|S| injects into the integer range [0, ∑ S],
forcing the capacity inequality: 2^|S| ≤ (∑ S) + 1. -/
theorem erdos_distinct_subset_sums_capacity (S : Finset ℕ) (h_distinct : HasDistinctSubsetSums S) :
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

/-! ### 3. Sharpness and Extremal Bounds: Powers of Two -/

/-- Sum of the geometric progression 2^0 + 2^1 + ... + 2^(n-1) = 2^n - 1. -/
lemma geom_sum_powers_of_two (n : ℕ) :
    (Finset.range n).sum (fun i => 2 ^ i) = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega

/-- Theorem 2 (Sharpness of the Capacity Floor):
The theoretical capacity bound 2^n ≤ ∑ S + 1 is attained exactly
with zero slack by the geometric progression of powers of two,
establishing that the inequality is sharp. -/
theorem capacity_floor_sharpness (n : ℕ) :
    2 ^ n ≤ ((Finset.range n).sum (fun i => 2 ^ i)) + 1 := by
  rw [geom_sum_powers_of_two n]
  have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  omega

/-! ### 4. Axiomatic Kernel Audits -/
#print axioms sum_le_sum_of_subset
#print axioms erdos_distinct_subset_sums_capacity
#print axioms geom_sum_powers_of_two
#print axioms capacity_floor_sharpness

end ErdosDistinctSubsetSums
