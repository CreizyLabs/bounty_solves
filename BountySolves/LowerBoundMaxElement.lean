/-!
# Formal Verification of Conway–Guy Counterexamples to the 2^(n-1) Subset Sum Bound
Target: Problem Reference JSP-000043 / Formal Verification of Conway–Guy Base Cases
Historical Context:
For a finite set S of n positive integers with pairwise distinct subset sums, the powers of two
{1, 2, ..., 2^(n-1)} achieve max(S) = 2^(n-1). It was early observed (and systematically
generalized by J. H. Conway and R. K. Guy in 1969) that max(S) can be strictly smaller than
2^(n-1) starting at n = 4 with S_4 = {3, 5, 6, 7} (max = 7 < 8) and n = 5 with
S_5 = {6, 9, 11, 12, 13} (max = 13 < 16). Note: Erdős's asymptotic conjecture max(S) ≥ c · 2^n
for an absolute constant c > 0 remains open.


Kernel Status: 100% Machine-Closed (0 sorry, 0 admit, 0 custom axioms).
Self-Contained: Zero external Mathlib imports required.
-/


namespace LowerBoundMaxElement


/-- Generates the list of all 2^|L| sublists of a given list. -/
def subsets : List Nat → List (List Nat)
  | [] => [[]]
  | x :: xs => subsets xs ++ (subsets xs).map (x :: ·)


/-- Exact integer sum of a list of natural numbers. -/
def listSum (l : List Nat) : Nat :=
  l.foldl (· + ·) 0


/-- Explicit computable check that a list has no duplicate elements (pairwise distinct).
    Avoids reliance on `List.eraseDups` implementation details. -/
def isNodup : List Nat → Bool
  | [] => true
  | x :: xs => !(xs.contains x) && isNodup xs


/-- Computable check that all elements of a list are strictly positive (> 0). -/
def allPositive (L : List Nat) : Bool :=
  L.all (fun x => x > 0)


/-- Predicate checking whether all 2^|L| subset sums of L are pairwise distinct. -/
def hasDistinctSubsetSums (L : List Nat) : Bool :=
  isNodup ((subsets L).map listSum)


/-! ### 1. Sanity Checks on Specification Definitions -/


theorem subsets_len_4 : (subsets [3, 5, 6, 7]).length = 16 := rfl
theorem subsets_len_5 : (subsets [6, 9, 11, 12, 13]).length = 32 := rfl


/-! ### 2. The Order-4 Counterexample S_4 = {3, 5, 6, 7} -/


/-- Canonical order-4 Conway-Guy set S_4 = {3, 5, 6, 7}. -/
def ConwayGuy4 : List Nat := [3, 5, 6, 7]


theorem conway_guy_4_len : ConwayGuy4.length = 4 := rfl
theorem conway_guy_4_pos : allPositive ConwayGuy4 = true := rfl
theorem conway_guy_4_nodup : isNodup ConwayGuy4 = true := rfl


/-- Exact verification that all 16 subset sums of {3, 5, 6, 7} are pairwise distinct:
    Sums: {0, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 21}. -/
theorem conway_guy_4_distinct_sums : hasDistinctSubsetSums ConwayGuy4 = true := rfl


theorem conway_guy_4_max_mem : 7 ∈ ConwayGuy4 := by decide
theorem conway_guy_4_max_bound : ∀ x ∈ ConwayGuy4, x ≤ 7 := by decide
theorem conway_guy_4_beats_power_of_two : (7 : Nat) < 2 ^ (ConwayGuy4.length - 1) := by decide


/-! ### 3. The Order-5 Counterexample S_5 = {6, 9, 11, 12, 13} -/


/-- Canonical order-5 Conway-Guy set S_5 = {6, 9, 11, 12, 13}. -/
def ConwayGuy5 : List Nat := [6, 9, 11, 12, 13]


theorem conway_guy_5_len : ConwayGuy5.length = 5 := rfl
theorem conway_guy_5_pos : allPositive ConwayGuy5 = true := rfl
theorem conway_guy_5_nodup : isNodup ConwayGuy5 = true := rfl


/-- Exact verification that all 32 subset sums of {6, 9, 11, 12, 13} are pairwise distinct. -/
theorem conway_guy_5_distinct_sums : hasDistinctSubsetSums ConwayGuy5 = true := rfl


theorem conway_guy_5_max_mem : 13 ∈ ConwayGuy5 := by decide
theorem conway_guy_5_max_bound : ∀ x ∈ ConwayGuy5, x ≤ 13 := by decide
theorem conway_guy_5_beats_power_of_two : (13 : Nat) < 2 ^ (ConwayGuy5.length - 1) := by decide


/-! ### 4. Refutation of the Naive 2^(n-1) Lower Bound -/


/-- Formal statement of the naive 2^(n-1) lower bound hypothesis:
    "For every non-empty finite set S of positive integers with distinct subset sums,
     any upper bound m on the elements of S must satisfy 2^(|S|-1) ≤ m." -/
def NaivePowerOfTwoBoundHypothesis : Prop :=
  ∀ S : List Nat,
    S.length > 0 →
    allPositive S = true →
    isNodup S = true →
    hasDistinctSubsetSums S = true →
    ∀ m : Nat, (∀ x ∈ S, x ≤ m) → 2 ^ (S.length - 1) ≤ m


/-- Main Theorem: The naive bound max(S) ≥ 2^(|S|-1) is false. -/
theorem naive_power_of_two_bound_disproved :
    ¬ NaivePowerOfTwoBoundHypothesis := by
  intro h
  have h_bound := h ConwayGuy4
    (by decide)
    conway_guy_4_pos
    conway_guy_4_nodup
    conway_guy_4_distinct_sums
    7
    conway_guy_4_max_bound
  have h_gap : ¬ (2 ^ (ConwayGuy4.length - 1) ≤ 7) := by decide
  exact h_gap h_bound


/-! ### Axiomatic Kernel Audits -/
#print axioms conway_guy_4_distinct_sums
#print axioms conway_guy_5_distinct_sums
#print axioms naive_power_of_two_bound_disproved


end LowerBoundMaxElement