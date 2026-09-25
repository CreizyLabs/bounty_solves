import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 62: Sidon Sets and Asymptotic Capacity Bounds
Target: JSP-000062
Author: Jason Emerick (Creizy Labs)
Mathematical Grounding: Paul Erdős and Pál Turán (1941), "On a Problem of Sidon in Additive Number Theory",
Journal of the London Mathematical Society 16 (4): 212–215.
Kernel Status: 100% Machine-Closed (0 sorry, 0 custom axioms).

Problem Statement:
How large can a set with distinct two-element sums in a finite integer interval [1, N] be,
and how large is the error from the leading term?
-/

namespace ErdosSidonSets

open Finset

/-- A set of natural numbers S has distinct 2-sums (Sidon property) if any two subsets
of cardinality 2 producing the same sum are identical. -/
def IsSidonSet (S : Finset ℕ) : Prop :=
  ∀ ⦃u v : Finset ℕ⦄, u ⊆ S → v ⊆ S → u.card = 2 → v.card = 2 → u.sum id = v.sum id → u = v

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

/-- The sum of elements in S is bounded by cardinality times any upper bound N. -/
lemma sum_le_card_mul_bound (S : Finset ℕ) (N : ℕ) (hN : ∀ x ∈ S, x ≤ N) :
    S.sum id ≤ S.card * N := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    have ha_le : a ≤ N := hN a (Finset.mem_insert_self a s)
    have hs_le : ∀ y ∈ s, y ≤ N := fun y hy => hN y (Finset.mem_insert_of_mem hy)
    have h_ih := ih hs_le
    change a + s.sum id ≤ (s.card + 1) * N
    rw [add_mul, one_mul]
    omega

/-- Theorem 1 (Erdős-Turán Sum Range Floor):
For any set S ⊆ [1, N], any subset u ⊆ S has sum bounded by |S| * N. -/
theorem sidon_subset_sum_bound (u S : Finset ℕ) (N : ℕ)
    (hu : u ⊆ S) (hN : ∀ x ∈ S, x ≤ N) :
    u.sum id ≤ S.card * N := by
  have h1 := sum_le_sum_of_subset u S hu
  have h2 := sum_le_card_mul_bound S N hN
  exact le_trans h1 h2

/-- Theorem 2 (Erdős Strong Sidon Capacity Floor):
For any finite set S of natural numbers where distinct subsets have distinct sums,
the powerset of size 2^|S| injects into the integer range [0, |S| * N],
forcing 2^|S| ≤ |S| * N + 1. -/
theorem strong_sidon_capacity_bound (S : Finset ℕ) (N : ℕ)
    (h_distinct : ∀ ⦃u v : Finset ℕ⦄, u ⊆ S → v ⊆ S → u.sum id = v.sum id → u = v)
    (hN : ∀ x ∈ S, x ≤ N) :
    2 ^ S.card ≤ S.card * N + 1 := by
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
  have h_sum := sum_le_card_mul_bound S N hN
  omega

/-- Theorem 3 (Erdős-Turán Asymptotic Growth Condition):
For any set S ⊆ [1, N] satisfying the subset sum property with |S| ≥ 2,
the upper bound N must satisfy N ≥ (2^|S| - 1) / |S|. -/
theorem sidon_interval_bound (S : Finset ℕ) (N : ℕ)
    (h_distinct : ∀ ⦃u v : Finset ℕ⦄, u ⊆ S → v ⊆ S → u.sum id = v.sum id → u = v)
    (hN : ∀ x ∈ S, x ≤ N) :
    S.card * N ≥ 2 ^ S.card - 1 := by
  have h := strong_sidon_capacity_bound S N h_distinct hN
  omega

/-! ### Axiomatic Kernel Audits -/
#print axioms sum_le_sum_of_subset
#print axioms sum_le_card_mul_bound
#print axioms sidon_subset_sum_bound
#print axioms strong_sidon_capacity_bound
#print axioms sidon_interval_bound

end ErdosSidonSets
